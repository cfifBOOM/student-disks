"""Файловый монитор студенческого диска.

Обычный запуск открывает нумерованное меню. Пункт 6 открывает веб-интерфейс
с тем же каталогом. Подробная инструкция — в README.md внутри resources.zip.

Примеры запуска из распакованной папки:
    python app.py
    python app.py --open
    python app.py --root "C:/Практика"
    python app.py --config config.json --serve
"""
import argparse
import base64
from contextlib import contextmanager, ExitStack
from dataclasses import dataclass, replace
from decimal import Decimal, InvalidOperation
from fnmatch import fnmatchcase
from getpass import getpass
from hashlib import blake2b, sha256
import hmac
import json
import logging
from math import ceil
import os
from pathlib import Path
import re
import secrets
import stat
import sys
from tempfile import NamedTemporaryFile
from threading import Event, Lock, Thread
import time
from urllib.parse import urlencode, urlsplit
import webbrowser
from zipfile import ZipFile

HERE = Path(os.path.abspath(__file__)).parent
RESOURCES = HERE / "resources.zip"


# Типы файлов и правила хранения

MB = 1_000_000
LARGE = 100 * MB
CATEGORIES = {
    "photo": "Фотография", "exec": "Запускаемый файл", "archive": "Архив",
    "video": "Видео", "audio": "Аудио", "document": "Документ", "other": "Другое",
}
EXTENSIONS = {
    "photo": "jpg jpeg jfif png heic heif webp gif bmp tif tiff avif dng raw cr2 cr3 nef arw",
    "exec": "exe com msi msp msix appx bat cmd ps1 psm1 vbs vbe js jse wsf wsh scr jar sh run appimage",
    "archive": "zip rar 7z tar gz bz2 xz zst tgz tbz tbz2 txz cab tar.gz tar.bz2 tar.xz tar.zst",
    "video": "mp4 mov mkv avi webm m4v mpg mpeg",
    "audio": "mp3 wav flac ogg m4a aac",
    "document": "txt md doc docx pdf odt rtf xls xlsx ods csv ppt pptx odp",
}
EXT_TYPE = {ext: kind for kind, words in EXTENSIONS.items() for ext in words.split()}
COMPOUND = tuple("." + ext for ext in EXT_TYPE if "." in ext)


def extension(name):
    lower = name.casefold()
    return next((ext for ext in COMPOUND if lower.endswith(ext)), Path(lower).suffix)


def string_list(raw, key):
    value = raw.get(key, [])
    if not isinstance(value, list) or any(not isinstance(x, str) or not x.strip() for x in value):
        raise ValueError(f"{key} должен содержать список непустых строк")
    return list(dict.fromkeys(x.strip().casefold() for x in value))


class Policy:
    def __init__(self, raw):
        self.limit = raw.get("size_from_mb", 100)
        if self.limit is not None and (type(self.limit) is not int or self.limit < 1):
            raise ValueError("Порог размера должен быть целым числом больше нуля. Пустое значение отключает правило.")
        self.types = string_list(raw, "forbidden_types")
        if set(self.types) - CATEGORIES.keys():
            raise ValueError("Неизвестная категория в forbidden_types")
        self.extensions = []
        for ext in string_list(raw, "forbidden_extensions"):
            value = ext.lstrip(".")
            if not value or any(char in value for char in "/\\*?;,: "):
                raise ValueError("Укажи расширения через запятую, например .exe, .tmp.")
            self.extensions.append("." + value)
        self.masks = string_list(raw, "name_masks")

    def examine(self, name, size, mode=0):
        ext = extension(name)
        kind = EXT_TYPE.get(ext.lstrip("."), "other")
        if not ext and mode & 0o111:
            kind = "exec"
        return kind, ext, self.issues_for(name, size, kind)

    def issues_for(self, name, size, kind):
        issues = []
        normalized_name = name.casefold()
        if self.limit is not None and size >= self.limit * MB:
            issues.append(f"Размер от {self.limit} МБ")
        if kind in self.types:
            issues.append(f"Запрещённый тип «{CATEGORIES[kind]}»")
        denied_extensions = [ext for ext in self.extensions if normalized_name.endswith(ext)]
        if denied_extensions:
            issues.append("Запрещённое расширение " + ", ".join(denied_extensions))
        matched_masks = [mask for mask in self.masks if fnmatchcase(normalized_name, mask)]
        if matched_masks:
            issues.append("Имя совпало с маской " + ", ".join(matched_masks))
        return issues

    def as_config(self):
        return {"size_from_mb": self.limit, "forbidden_types": list(self.types),
                "forbidden_extensions": list(self.extensions), "name_masks": list(self.masks)}


# Поиск и сортировка

FILTERS = {
    "all": "Все файлы", "photo": "Фотографии",
    "exec": "Запускаемые файлы", "archive": "Файлы-архивы", "issues": "Подозрительные файлы",
}
SORTS = {
    "size_desc": "Сначала крупные", "size_asc": "Сначала маленькие",
    "name_asc": "Имя от А до Я", "name_desc": "Имя от Я до А",
    "type": "По типу файла", "ext": "По расширению", "none": "Без сортировки",
}


def number_of_bytes(value, label):
    text = "" if value is None else str(value).strip()
    if not text:
        return None
    try:
        size = Decimal(text.replace(",", "."))
        if not size.is_finite() or not 0 <= size <= 10**12:
            raise ValueError
        return size * MB
    except (ValueError, InvalidOperation):
        raise ValueError(f"{label}: укажи неотрицательное число МБ до 10¹².") from None


def extensions(text):
    result = []
    for part in str(text).replace(";", ",").split(","):
        value = part.strip().casefold().lstrip(".")
        if not value:
            continue
        if any(symbol in value for symbol in "/\\*? :"):
            raise ValueError("Расширения вводятся через запятую, например .zip, .7z.")
        result.append("." + value)
    return tuple(dict.fromkeys(result))


@dataclass(frozen=True)
class Search:
    kind: str
    sort: str
    drive: str
    query: str
    mask: str
    exts: tuple[str, ...]
    minimum: Decimal | None
    maximum: Decimal | None

    @classmethod
    def parse(cls, values, drive_count):
        kind, sort = values.get("filter", "all"), values.get("sort", "size_desc")
        if (kind not in FILTERS and kind not in {"large", "min_mb", "max_mb"}) or sort not in SORTS:
            raise ValueError("Неизвестный фильтр или сортировка.")
        drive = values.get("drive", "all")
        if drive != "all" and drive not in {str(i) for i in range(drive_count)}:
            raise ValueError("Неизвестный диск.")
        low = number_of_bytes(values.get("min_mb"), "Минимальный размер")
        high = number_of_bytes(values.get("max_mb"), "Максимальный размер")
        if low is not None and high is not None and low > high:
            raise ValueError("Минимальный размер превышает максимальный.")
        return cls(kind, sort, drive, values.get("q", "").strip().casefold(),
                   values.get("mask", "").strip().casefold(), extensions(values.get("ext", "")), low, high)

    def matches(self, file):
        if self.drive != "all" and str(file.drive) != self.drive:
            return False
        if self.kind == "large" and file.size < LARGE:
            return False
        if self.kind == "issues" and not file.issues:
            return False
        if self.kind in CATEGORIES and self.kind != file.kind:
            return False
        if self.minimum is not None and file.size < self.minimum:
            return False
        if self.maximum is not None and file.size > self.maximum:
            return False
        name = file.path.name.casefold()
        return ((not self.query or self.query in str(file.path).casefold())
                and (not self.mask or fnmatchcase(name, self.mask))
                and (not self.exts or name.endswith(self.exts)))

    def apply(self, records):
        chosen = [file for file in records if self.matches(file)]
        # Индекс уже упорядочен по убыванию размера, затем по полному пути.
        if self.sort != "size_desc":
            keys = {
                "size_asc": lambda f: (f.size, str(f.path).casefold()),
                "name_asc": lambda f: (f.path.name.casefold(), str(f.path).casefold()),
                "type": lambda f: (CATEGORIES[f.kind].casefold(), f.path.name.casefold(), str(f.path).casefold()),
                "ext": lambda f: (f.ext, f.path.name.casefold(), str(f.path).casefold()),
                "none": lambda f: f.scan_order,
            }
            key = keys["name_asc"] if self.sort == "name_desc" else keys[self.sort]
            chosen.sort(key=key, reverse=self.sort == "name_desc")
        return chosen


# Проверка пути и удаление одного файла

class Changed(Exception):
    """Запись больше не совпадает с результатом проверки."""


def linked(info):
    return (stat.S_ISLNK(info.st_mode)
            or bool(getattr(info, "st_file_attributes", 0) & stat.FILE_ATTRIBUTE_REPARSE_POINT))


def identity(info):
    return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns


def check_file(info, expected):
    if linked(info) or not stat.S_ISREG(info.st_mode) or identity(info) != expected:
        raise Changed("Файл изменился. Обнови список и выбери его заново.")


def remove_indexed(root, parts, expected):
    if not parts or any(part in ("", ".", "..") or Path(part).name != part for part in parts):
        raise Changed("Некорректная запись в каталоге.")
    if os.name == "nt":
        _windows_remove(root, parts, expected)
    else:
        _posix_remove(root, parts, expected)


def _posix_remove(root, parts, expected):
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    with ExitStack() as stack:
        parent = os.open(root, flags)
        stack.callback(os.close, parent)
        for part in parts[:-1]:
            parent = os.open(part, flags, dir_fd=parent)
            stack.callback(os.close, parent)
        name = parts[-1]
        check_file(os.stat(name, dir_fd=parent, follow_symlinks=False), expected)
        # Переименование внутри той же папки атомарно захватывает выбранную запись.
        # После этого конкурентная замена исходного имени не попадёт под unlink.
        staging = ".diskmonitor-" + secrets.token_hex(16)
        os.mkdir(staging, 0o700, dir_fd=parent)
        try:
            temp = os.open(staging, flags, dir_fd=parent)
            try:
                os.rename(name, "selected", src_dir_fd=parent, dst_dir_fd=temp)
                try:
                    check_file(os.stat("selected", dir_fd=temp, follow_symlinks=False), expected)
                    os.unlink("selected", dir_fd=temp)
                except Exception:
                    # Восстановление без перезаписи другого файла с тем же именем.
                    try:
                        os.link("selected", name, src_dir_fd=temp, dst_dir_fd=parent, follow_symlinks=False)
                        os.unlink("selected", dir_fd=temp)
                    except OSError:
                        raise Changed(f"Запись сохранена для восстановления в {staging}/selected.")
                    raise
            finally:
                os.close(temp)
        finally:
            try:
                os.rmdir(staging, dir_fd=parent)
            except OSError:
                pass  # Внутри может оставаться запись, требующая ручного восстановления.


def _windows_remove(root, parts, expected):
    # Один HANDLE используется и для проверки объекта, и для запроса удаления.
    from ctypes import WinDLL, WinError, byref, c_ubyte, create_unicode_buffer, get_last_error, sizeof
    from ctypes import wintypes as w

    api = WinDLL("kernel32", use_last_error=True)
    create = api.CreateFileW
    create.argtypes = [w.LPCWSTR, w.DWORD, w.DWORD, w.LPVOID, w.DWORD, w.DWORD, w.HANDLE]
    create.restype = w.HANDLE
    final = api.GetFinalPathNameByHandleW
    final.argtypes = [w.HANDLE, w.LPWSTR, w.DWORD, w.DWORD]
    final.restype = w.DWORD
    dispose = api.SetFileInformationByHandle
    dispose.argtypes = [w.HANDLE, w.INT, w.LPVOID, w.DWORD]
    dispose.restype = w.BOOL
    close = api.CloseHandle
    close.argtypes = [w.HANDLE]
    close.restype = w.BOOL

    @contextmanager
    def opened(path, *, directory):
        access = 0x80 if directory else 0x10080  # FILE_READ_ATTRIBUTES + DELETE у файла.
        flags = 0x00200000 | (0x02000000 if directory else 0)  # OPEN_REPARSE_POINT, BACKUP_SEMANTICS
        share = 3 if directory else 1  # Для выбранного файла разрешаем только параллельное чтение.
        handle = create(str(path), access, share, None, 3, flags, None)  # OPEN_EXISTING
        if handle == w.HANDLE(-1).value:
            raise WinError(get_last_error())
        try:
            yield handle
        finally:
            close(handle)

    def final_path(handle):
        buffer = create_unicode_buffer(32768)
        count = final(handle, buffer, len(buffer), 0)
        if not count or count >= len(buffer):
            raise WinError(get_last_error())
        return os.path.normcase(os.path.normpath(buffer.value))

    with ExitStack() as stack:
        current = root
        root_handle = stack.enter_context(opened(root, directory=True))
        root_info = root.lstat()
        if linked(root_info) or not stat.S_ISDIR(root_info.st_mode):
            raise Changed("Корневая папка изменилась.")
        base = final_path(root_handle)
        for part in parts[:-1]:
            current /= part
            stack.enter_context(opened(current, directory=True))
            info = current.lstat()
            if linked(info) or not stat.S_ISDIR(info.st_mode):
                raise Changed("Расположение папки изменилось.")
        path = current / parts[-1]
        handle = stack.enter_context(opened(path, directory=False))
        # Открытые каталоги и файл удерживаются без SHARE_DELETE до конца операции.
        check_file(path.lstat(), expected)
        if final_path(handle) != os.path.normcase(os.path.normpath(os.path.join(base, *parts))):
            raise Changed("Расположение файла изменилось.")
        value = c_ubyte(1)  # FILE_DISPOSITION_INFO.DeleteFile = TRUE
        if not dispose(handle, 4, byref(value), sizeof(value)):
            raise WinError(get_last_error())


# Чтение и сохранение настроек

def load_config(path):
    with Path(path).open(encoding="utf-8-sig") as handle:
        return json.load(handle)


def rules_version(policy):
    data = json.dumps(policy.as_config(), ensure_ascii=False, sort_keys=True)
    return sha256(data.encode("utf-8")).hexdigest()


@contextmanager
def config_lock(path):
    """Короткая блокировка между экземплярами, в том числе на общей папке."""
    lockpath = path.with_name("." + path.name + ".lock")
    if os.name == "nt":
        import msvcrt
        try:
            with lockpath.open("a+b") as handle:
                if os.fstat(handle.fileno()).st_size == 0:
                    handle.write(b"0")
                    handle.flush()
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_LOCK, 1)
                try:
                    yield
                finally:
                    handle.seek(0)
                    msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        finally:
            try:
                lockpath.unlink(missing_ok=True)
            except PermissionError:
                pass  # Другой экземпляр держит файл. Он уберёт его после записи.
        return
    import fcntl
    while True:
        with lockpath.open("a+b") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            # Предыдущий владелец мог убрать файл, пока мы ждали его дескриптор.
            try:
                if not os.path.samestat(os.fstat(handle.fileno()), lockpath.stat()):
                    continue
            except FileNotFoundError:
                continue
            try:
                yield
            finally:
                lockpath.unlink(missing_ok=True)
            return


def write_rules(path, policy, expected):
    with config_lock(path):
        data = load_config(path)
        previous = Policy(data.get("rules", {}))
        if rules_version(previous) != expected:
            raise Changed("Другой экземпляр уже изменил правила. Перезапусти программу, чтобы загрузить их.")
        data["rules"] = policy.as_config()
        mode = stat.S_IMODE(path.stat().st_mode)
        temp_path = None
        try:
            with NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, delete=False) as handle:
                temp_path = Path(handle.name)
                json.dump(data, handle, ensure_ascii=False, indent=2)
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.chmod(temp_path, mode)
            os.replace(temp_path, path)
        finally:
            if temp_path:
                temp_path.unlink(missing_ok=True)


# Сканирование дисков и общий каталог

PAGE_SIZE = 20


@dataclass(frozen=True)
class Drive:
    name: str
    path: Path


@dataclass(frozen=True)
class Record:
    id: str
    drive: int
    path: Path
    stamp: tuple
    kind: str
    ext: str
    issues: list
    scan_order: int

    @property
    def size(self):
        return self.stamp[2]

    def public(self):
        return {"id": self.id, "name": self.path.name, "path": str(self.path),
                "size": self.size, "kind": self.kind, "type": CATEGORIES[self.kind],
                "ext": self.ext, "issues": self.issues}


def settings(raw):
    if not isinstance(raw, dict) or not isinstance(raw.get("drives"), list) or not raw["drives"]:
        raise ValueError("В конфигурации нужен непустой список drives.")
    drives = []
    for item in raw["drives"]:
        if not isinstance(item, dict) or not isinstance(item.get("path"), str):
            raise ValueError("Для диска укажи name и path.")
        name, path = item.get("name"), Path(item["path"]).expanduser()
        use_parent = path == Path("..")
        if use_parent:
            path = HERE.parent
        if not isinstance(name, str) or not name.strip() or not path.is_absolute() or ".." in path.parts:
            raise ValueError("Укажи имя и абсолютный путь диска или «..» для папки над программой.")
        if any(d.path == path or d.path in path.parents or path in d.path.parents for d in drives):
            raise ValueError("Корневые папки дисков пересекаются.")
        label = f"{name.strip()} ({path})" if use_parent else name.strip()
        drives.append(Drive(label, path))
    seconds = raw.get("rescan_seconds", 120)
    if type(seconds) is not int or seconds < 0:
        raise ValueError("rescan_seconds должен быть целым неотрицательным числом.")
    rules = raw.get("rules", {})
    if not isinstance(rules, dict):
        raise ValueError("rules должен быть объектом.")
    return drives, Policy(rules), seconds


def application_folder_in(root):
    if root in HERE.parents:
        return HERE
    if root != HERE:
        # Один сетевой ресурс может быть указан как буква диска или как UNC-путь.
        resolved_root = root.resolve()
        resolved_app = HERE.resolve()
        if resolved_root in resolved_app.parents:
            return root / resolved_app.relative_to(resolved_root)
    return None


def walk_files(root, on_error):
    root_info = root.lstat()
    if linked(root_info) or not stat.S_ISDIR(root_info.st_mode):
        raise OSError("Указанный путь не является обычной папкой")
    excluded = application_folder_in(root)
    if os.name == "posix":
        for folder, dirs, names, descriptor in os.fwalk(root, onerror=on_error, follow_symlinks=False):
            if excluded is not None and Path(folder) == excluded.parent and excluded.name in dirs:
                dirs.remove(excluded.name)
            for name in names:
                try:
                    info = os.stat(name, dir_fd=descriptor, follow_symlinks=False)
                    if stat.S_ISREG(info.st_mode):
                        yield Path(folder, name), info
                except FileNotFoundError:
                    continue
                except OSError as error:
                    on_error(error)
        return
    # На Windows DirEntry.stat может не вернуть идентификатор файла на томе.
    pending = [root]
    while pending:
        folder = pending.pop()
        try:
            if linked(folder.lstat()):
                continue
            with os.scandir(folder) as entries:
                for entry in entries:
                    try:
                        path = Path(entry.path)
                        if path == excluded:
                            continue
                        info = path.lstat()
                        if linked(info):
                            continue
                        if stat.S_ISDIR(info.st_mode):
                            pending.append(path)
                        elif stat.S_ISREG(info.st_mode):
                            yield path, info
                    except FileNotFoundError:
                        continue
                    except OSError as error:
                        on_error(error)
        except OSError as error:
            on_error(error)


class Monitor:
    def __init__(self, raw, config_path=None):
        self.drives, self.policy, self.seconds = settings(raw)
        self.config_path = Path(config_path).resolve() if config_path is not None else None
        self.records = {}
        self.generation = 0
        self.warnings = []
        self.scanned = None
        self.busy = False
        self.secret = secrets.token_bytes(32)
        self.state_lock, self.operation = Lock(), Lock()
        self.stop = Event()
        self.scan_thread = None

    def _scan(self):
        warnings, records = [], {}
        for number, drive in enumerate(self.drives):
            errors = 0

            def failed(_):
                nonlocal errors
                errors += 1

            try:
                for path, info in walk_files(drive.path, failed):
                    if self.stop.is_set():
                        return
                    stamp = identity(info)
                    # Стабилен для неизменённого файла между проверками.
                    digest = blake2b(key=self.secret, digest_size=16)
                    digest.update(os.fsencode(path) + b"\x00" + repr(stamp).encode("ascii"))
                    key = digest.hexdigest()
                    permissions = info.st_mode if os.name == "posix" else 0
                    kind, ext, issues = self.policy.examine(path.name, info.st_size, permissions)
                    records[key] = Record(key, number, path, stamp, kind, ext, issues, len(records))
            except OSError:
                warnings.append(f"{drive.name} ({drive.path}) недоступен. Проверь подключение и права учётной записи.")
                continue
            if errors:
                warnings.append(f"{drive.name}: часть записей пропущена. Ошибок доступа или чтения: {errors}.")
        ordered = sorted(records.values(), key=lambda r: (-r.size, str(r.path).casefold()))
        with self.state_lock:
            self.records = {item.id: item for item in ordered}
            self.warnings, self.scanned = warnings, int(time.time() * 1000)
            self.generation += 1

    def _scan_guarded(self):
        try:
            with self.operation:
                self._scan()
        except Exception:
            logging.exception("Ошибка при сканировании")
            with self.state_lock:
                self.warnings = ["Проверка прервана. Показан последний доступный список."]
                self.generation += 1
        finally:
            with self.state_lock:
                self.busy = False

    def request_scan(self):
        with self.state_lock:
            if self.busy or self.stop.is_set():
                return
            self.busy = True
            self.scan_thread = Thread(target=self._scan_guarded, daemon=True)
            self.scan_thread.start()

    def start(self):
        self.request_scan()
        if self.seconds:
            def schedule():
                while not self.stop.wait(self.seconds):
                    self.request_scan()
            Thread(target=schedule, daemon=True).start()

    def wait_for_scan(self, timeout=None):
        with self.state_lock:
            worker = self.scan_thread
        if worker:
            worker.join(timeout)

    def close(self):
        self.stop.set()
        self.wait_for_scan(timeout=1)

    def delete(self, key):
        with self.operation:
            with self.state_lock:
                item = self.records.get(key)
            if item is None:
                raise Changed("Файл уже удалён или изменился. Обнови каталог.")
            root = self.drives[item.drive].path
            remove_indexed(root, item.path.relative_to(root).parts, item.stamp)
            with self.state_lock:
                del self.records[key]
                self.generation += 1

    def update_rules(self, raw, expected):
        if not isinstance(raw, dict) or set(raw) != {"size_from_mb", "forbidden_types", "forbidden_extensions", "name_masks"}:
            raise ValueError("Нужны размер, типы, расширения и маски имён.")
        policy = Policy(raw)
        if self.config_path is None:
            raise ValueError("Не указан файл настроек.")
        with self.operation:
            if rules_version(self.policy) != expected:
                raise Changed("Правила были изменены. Открой их ещё раз.")
            # Подстановка правил использует готовый индекс, без сетевого обхода.
            records = {
                key: replace(f, issues=policy.issues_for(f.path.name, f.size, f.kind))
                for key, f in self.records.items()
            }
            write_rules(self.config_path, policy, expected)
            with self.state_lock:
                self.records, self.policy = records, policy
                self.generation += 1

    def status(self):
        with self.state_lock:
            return {"generation": self.generation, "busy": self.busy, "scanned": self.scanned}

    def view(self, filters):
        search = Search.parse(filters, len(self.drives))
        requested = max(1, int(filters.get("page", "1")))
        with self.state_lock:
            items = tuple(self.records.values())
            busy, scanned, warnings, policy = self.busy, self.scanned, self.warnings, self.policy
            generation = self.generation
        selected = search.apply(items)
        pages = max(1, ceil(len(selected) / PAGE_SIZE))
        page = min(requested, pages)
        start = (page - 1) * PAGE_SIZE
        return {
            "files": [r.public() for r in selected[start:start + PAGE_SIZE]],
            "total": len(selected), "page": page, "pages": pages,
            "drives": [d.name for d in self.drives], "rules": policy.as_config(),
            "version": rules_version(policy), "filters": FILTERS, "sorts": SORTS,
            "types": CATEGORIES, "generation": generation, "busy": busy, "scanned": scanned, "warnings": warnings,
        }


# Консольное меню

def plain(value):
    # Управляющие символы из реальных имён не должны управлять терминалом.
    return "".join(char if char.isprintable() else ascii(char)[1:-1] for char in str(value))


def choose(title, options, current=None):
    entries = list(options.items())
    print("\n" + title)
    for index, (key, label) in enumerate(entries, 1):
        marker = " *" if key == current else ""
        print(f"  {index}. {plain(label)}{marker}")
    print("  0. Назад")
    while True:
        value = input("> ").strip()
        if value in ("0", ""):
            return None
        index = int(value) if value.isdecimal() else 0
        if 1 <= index <= len(entries):
            return entries[index - 1][0]
        print(f"Введи число от 0 до {len(entries)}.")


def text_value(label, current=""):
    value = input(f"{label} [{plain(current) or '—'}] (Enter оставить, - очистить): ").strip()
    return "" if value == "-" else value or current


def size_text(size):
    if size < 1000:
        return f"{size} Б"
    if size < MB:
        return f"{size / 1000:.2f} КБ"
    if size < 1000 * MB:
        return f"{size / MB:.2f} МБ"
    return f"{size / (1000 * MB):.2f} ГБ"


def parameters(monitor, values):
    options = {"filter": "Категория", "q": "Поиск по имени или пути", "mask": "Маска имени",
               "ext": "Расширения через запятую", "range": "Размер от и до, МБ"}
    if len(monitor.drives) > 1:
        options["drive"] = "Диск"
    options["reset"] = "Сбросить параметры поиска"
    while True:
        active = [FILTERS[values["filter"]]]
        active += [v for k, v in values.items() if k in ("q", "mask", "ext") and v]
        if values.get("min_mb"): active.append("от " + values["min_mb"] + " МБ")
        if values.get("max_mb"): active.append("до " + values["max_mb"] + " МБ")
        key = choose("Параметры поиска · " + plain(" / ".join(active)), options)
        if key is None:
            return
        next_values = dict(values)
        if key == "filter":
            selected = choose("Выбор фильтра", FILTERS, values[key])
            if selected: next_values[key] = selected
        elif key == "drive":
            drives = {"all": "Все диски", **{str(i): d.name for i, d in enumerate(monitor.drives)}}
            selected = choose("Диск", drives, values.get(key, "all"))
            if selected: next_values[key] = selected
        elif key == "range":
            next_values["min_mb"] = text_value("От, МБ", values.get("min_mb", ""))
            next_values["max_mb"] = text_value("До, МБ", values.get("max_mb", ""))
        elif key == "reset":
            next_values = {"filter": "all", "sort": values["sort"]}
        else:
            next_values[key] = text_value(options[key], values.get(key, ""))
        try:
            Search.parse(next_values, len(monitor.drives))
        except ValueError as error:
            print("Параметры не приняты.", error)
            continue
        values.clear()
        values.update(next_values)


def edit_rules(monitor):
    with monitor.state_lock:
        policy = monitor.policy
    original = rules_version(policy)
    raw = policy.as_config()
    keys = list(CATEGORIES)
    print("\nПравила хранения · применяются в консоли и браузере.")
    print("Enter оставляет значение, один минус отключает порог или очищает список.")
    limit = raw["size_from_mb"]
    size = input(f"Помечать файлы от скольких МБ [{limit if limit is not None else 'отключено'}]: ").strip()
    if size:
        raw["size_from_mb"] = None if size == "-" else int(size)
    labels = ", ".join(f"{i}. {CATEGORIES[k]}" for i, k in enumerate(keys, 1))
    print(labels)
    current = ", ".join(str(keys.index(k) + 1) for k in raw["forbidden_types"])
    chosen = text_value("Номера запрещённых типов через запятую", current)
    items = [item.strip() for item in chosen.split(",") if item.strip()]
    if any(not item.isdecimal() or not 1 <= int(item) <= len(keys) for item in items):
        raise ValueError("Некорректный номер типа.")
    raw["forbidden_types"] = [keys[int(item) - 1] for item in items]
    for field, label in [("forbidden_extensions", "Запрещённые расширения"), ("name_masks", "Маски имён")]:
        answer = text_value(label + " через запятую", ", ".join(raw[field]))
        raw[field] = [part.strip() for part in answer.split(",") if part.strip()]
    if input("Сохранить эти правила для следующих запусков? [д/Н] ").strip().casefold() in ("д", "да"):
        monitor.update_rules(raw, original)
        print("Правила сохранены.")


def results(monitor, values):
    if monitor.scanned is None and monitor.busy:
        print("Идёт первая проверка…")
        monitor.wait_for_scan()
    page = 1
    while True:
        view = monitor.view(dict(values, page=str(page)))
        page = view["page"]
        for warning in view["warnings"]:
            print(plain(warning))
        print(f"\nНайдено: {view['total']} · страница {page}/{view['pages']}")
        for i, item in enumerate(view["files"], 1):
            status = "Подозрительный — " + " · ".join(item["issues"]) if item["issues"] else "Без нарушений"
            print(f"  {i}. {plain(item['name'])} | {size_text(item['size'])} | {item['type']} | {plain(status)}")
            print("     " + plain(item["path"]))
        if not view["files"]:
            return
        command = input("Номер файла — действия, + / - страницы, 0 назад: ").strip()
        if command in ("", "0"):
            return
        if command in ("+", "-"):
            page = max(1, min(view["pages"], page + (1 if command == "+" else -1)))
            continue
        if not command.isdecimal() or not 1 <= int(command) <= len(view["files"]):
            print("Выбери номер из текущего списка.")
            continue
        file = view["files"][int(command) - 1]
        print(f"\n{plain(file['path'])}\n{file['size']} байт · {file['type']}")
        command = input("1. Удалить файл   0. Назад\n> ").strip()
        if command == "1":
            yes = input("Удалить этот файл без корзины? Введи ДА для подтверждения: ").strip().casefold()
            if yes == "да":
                try:
                    monitor.delete(file["id"])
                    print("Файл удалён.")
                except (Changed, OSError) as err:
                    print("Удаление не выполнено.", plain(err))
            else:
                print("Удаление отменено.")


def run(monitor, open_web):
    values = {"filter": "all", "sort": "size_desc"}
    print("Студенческие диски · " + ", ".join(plain(d.path) for d in monitor.drives))
    while True:
        print(f"\n1. Выбрать сортировку ({SORTS[values['sort']]})"
              f"\n2. Внести параметры поиска ({FILTERS[values['filter']]})"
              "\n3. Показать файлы\n4. Проверить диск заново\n5. Правила хранения"
              "\n6. Открыть веб-интерфейс\n0. Выход")
        command = input("> ").strip()
        try:
            if command == "0":
                return
            if command == "1":
                selected = choose("Сортировка", SORTS, values["sort"])
                if selected: values["sort"] = selected
            elif command == "2":
                parameters(monitor, values)
            elif command == "3":
                results(monitor, values)
            elif command == "4":
                print("Идёт проверка диска…")
                monitor.request_scan()
                monitor.wait_for_scan()
                summary = monitor.view({})
                for warning in summary["warnings"]: print(plain(warning))
                print(f"Проверка завершена. Файлов: {summary['total']}.")
            elif command == "5":
                edit_rules(monitor)
            elif command == "6":
                open_web(values)
            else:
                print("Введи число от 0 до 6.")
        except (Changed, ValueError, OSError) as error:
            print("Действие не выполнено.", plain(error))


# Обработчики веб-интерфейса

def page_policy(html):
    # CSP разрешает ровно те встроенные блоки, которые пришли с приложением.
    directives = ["default-src 'self'", "object-src 'none'", "frame-ancestors 'none'", "base-uri 'none'"]
    for tag in ("script", "style"):
        contents = re.findall(r"<" + tag + r"\b[^>]*>(.*?)</" + tag + ">", html, re.DOTALL)
        hashes = [base64.b64encode(sha256(part.encode("utf-8")).digest()).decode("ascii") for part in contents]
        directives.append(tag + "-src " + " ".join("'sha256-" + h + "'" for h in hashes))
    return "; ".join(directives)


def create_app(monitor, password=None):
    if str(RESOURCES) not in sys.path:
        sys.path.insert(0, str(RESOURCES))
    from flask import Flask, abort, request
    from werkzeug.exceptions import BadRequest, HTTPException

    app = Flask(__name__, static_folder=None, root_path=str(HERE))
    app.config.update(MAX_CONTENT_LENGTH=8192, PROVIDE_AUTOMATIC_OPTIONS=False)
    token = secrets.token_urlsafe(32)
    credentials = ("admin:" + password).encode("utf-8") if password else None
    with ZipFile(RESOURCES) as bundle:
        html = bundle.read("web.html").decode("utf-8")
    csp = page_policy(html)

    @app.before_request
    def authorize():
        if credentials is None:
            host = urlsplit("//" + request.host).hostname
            if host not in {"127.0.0.1", "localhost", "::1"}:
                abort(403, "Локальный режим доступен на этом компьютере.")
            return
        method, _, value = request.headers.get("Authorization", "").partition(" ")
        try:
            given = base64.b64decode(value, validate=True) if method.lower() == "basic" else b""
        except ValueError:
            given = b""
        if not hmac.compare_digest(given, credentials):
            abort(401, "Введи логин и пароль администратора.")

    @app.after_request
    def response_headers(response):
        response.headers.update({
            "Cache-Control": "no-store",
            "X-Content-Type-Options": "nosniff",
            "Referrer-Policy": "no-referrer",
            "X-Frame-Options": "DENY",
            "Content-Security-Policy": csp,
        })
        if response.status_code == 401:
            response.headers["WWW-Authenticate"] = 'Basic realm="Disk Monitor", charset="UTF-8"'
        return response

    def read_action():
        given = request.headers.get("X-Disk-Token", "").encode("utf-8")
        if not hmac.compare_digest(given, token.encode("ascii")):
            abort(403, "Обнови страницу перед этим действием.")
        if request.mimetype != "application/json":
            abort(415, "Ожидается application/json.")
        if not 0 < (request.content_length or 0) <= app.config["MAX_CONTENT_LENGTH"]:
            abort(400, "Некорректное тело запроса.")
        try:
            data = request.get_json()
        except BadRequest:
            abort(400, "Некорректный JSON.")
        if not isinstance(data, dict):
            abort(400, "Ожидается объект JSON.")
        return data

    @app.get("/")
    def index():
        return html

    app.get("/api/status")(monitor.status)

    @app.get("/api/files")
    def files():
        if request.query_string.count(b"&") >= 16:
            abort(400, "Слишком много параметров запроса.")
        return dict(monitor.view(dict(request.args.items(multi=True))), token=token)

    @app.post("/api/<any(scan,rules,remove):action>")
    def file_action(action):
        data = read_action()
        if action == "scan":
            monitor.request_scan()
        elif action == "rules":
            monitor.update_rules(data.get("rules"), data.get("version"))
        else:
            key = data.get("id")
            if not isinstance(key, str) or len(key) != 32:
                abort(400, "Нужен идентификатор выбранного файла.")
            monitor.delete(key)
        return {"ok": True}

    @app.errorhandler(HTTPException)
    def http_error(error):
        messages = {404: "Страница не найдена.", 405: "Метод запроса не поддерживается.",
                    500: "Серверу не удалось выполнить запрос."}
        response = error.get_response()
        response.set_data(app.json.dumps({"error": messages.get(error.code, error.description)}))
        response.mimetype = "application/json"
        return response

    @app.errorhandler(ValueError)
    def invalid_value(error):
        return {"error": str(error) or "Некорректные параметры запроса."}, 400

    @app.errorhandler(Changed)
    def changed(error):
        return {"error": str(error)}, 409

    @app.errorhandler(OSError)
    def disk_error(error):
        if isinstance(error, PermissionError):
            message = ("Нет прав на сохранение конфигурации." if request.path == "/api/rules" else
                       "Недостаточно прав или файл занят другой программой.")
            return {"error": message}, 403
        if isinstance(error, (FileNotFoundError, NotADirectoryError)):
            return {"error": "Файл или папка изменились. Запусти проверку снова."}, 409
        logging.exception("Операция с диском прервана")
        return {"error": "Диск или файл недоступен. Обнови каталог и проверь подключение."}, 409

    return app


def local_server(monitor, port):
    app = create_app(monitor)
    from werkzeug.serving import make_server, WSGIRequestHandler

    class QuietHandler(WSGIRequestHandler):
        def log_request(self, code="-", size="-"):
            pass

    return make_server("127.0.0.1", port, app, threaded=True, request_handler=QuietHandler)


# Запуск программы

def open_browser(url):
    print("Веб-интерфейс: " + url, flush=True)
    try:
        if webbrowser.open(url):
            return
    except webbrowser.Error:
        pass
    print("Скопируй адрес в браузер.")


def serve_network(monitor, port):
    password = os.environ.get("DISKMON_PASSWORD") or getpass("Задай пароль веб-пользователя admin: ")
    if not password.strip():
        raise ValueError("Для серверного запуска нужен непустой пароль.")
    print(f"Сервер для HTTPS-прокси: http://127.0.0.1:{port} · вход admin.", flush=True)
    app = create_app(monitor, password)
    from waitress import serve
    serve(app, host="127.0.0.1", port=port, max_request_body_size=8192)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--console", action="store_true", help="консольное меню (по умолчанию)")
    mode.add_argument("--web", action="store_true", help="только локальный веб-сервер")
    mode.add_argument("--serve", action="store_true", help="серверный запуск за HTTPS-прокси с паролем")
    parser.add_argument("--open", action="store_true", help="сразу открыть локальный веб-интерфейс")
    parser.add_argument("--config", type=Path, default=HERE / "config.json", help="файл настроек")
    parser.add_argument("--root", type=Path, help="реальная папка вместо настроенных дисков на этот запуск")
    parser.add_argument("--port", type=int, default=8765)
    args = parser.parse_args()
    if not 1 <= args.port <= 65535:
        parser.error("Порт должен быть от 1 до 65535.")
    if args.open and (args.console or args.serve):
        parser.error("--open подходит для локального веб-режима.")
    config = load_config(args.config)
    if args.root is not None:
        folder = args.root.expanduser().absolute()
        config["drives"] = [{"name": str(folder), "path": str(folder)}]
    monitor = Monitor(config, args.config)
    addr = f"http://127.0.0.1:{args.port}/"
    with ExitStack() as cleanup:
        monitor.start()
        cleanup.callback(monitor.close)
        if args.serve:
            serve_network(monitor, args.port)
            return
        if args.web or args.open:
            with local_server(monitor, args.port) as server:
                if args.open:
                    open_browser(addr)
                else:
                    print(addr + " · для остановки нажми Ctrl+C.", flush=True)
                server.serve_forever()
            return
        server = None

        def open_from_menu(filters):
            nonlocal server
            if server is None:
                server = cleanup.enter_context(local_server(monitor, args.port))
                Thread(target=server.serve_forever, daemon=True).start()
                cleanup.callback(server.shutdown)
            open_browser(addr + "?" + urlencode(filters))

        run(monitor, open_from_menu)


if __name__ == "__main__":
    try:
        main()
    except (KeyboardInterrupt, EOFError):
        print()
    except (OSError, ValueError) as error:
        sys.exit("Не удалось запустить программу. " + str(error))
