@echo off
cd /d "%~dp0"
REM Builds MapCoords.exe with the Kuwait chart embedded inside it.
REM Needs 64-bit Python 3.9+ on PATH, and Kuwait_Chart_2884.png next to this file.
if not exist "Kuwait_Chart_2884.png" (
  echo ERROR: Kuwait_Chart_2884.png not found in this folder.
  pause
  exit /b 1
)
python -m pip install --upgrade pip pillow pypdfium2 pyinstaller certifi
python -m PyInstaller --noconfirm --clean --onefile --windowed --collect-all pypdfium2 --collect-all certifi --add-data "Kuwait_Chart_2884.png;." --name MapCoords mapcoords.py
echo.
echo Done. Your program is in: dist\MapCoords.exe
pause
