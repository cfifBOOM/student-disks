@echo off
setlocal
where py >nul 2>nul
if errorlevel 1 goto use_python
py -3 -B "%~dp0app.py" --console
goto finished
:use_python
python -B "%~dp0app.py" --console
:finished
if errorlevel 1 pause
endlocal
