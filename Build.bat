@echo off
setlocal EnableExtensions EnableDelayedExpansion
title SzTextCompar - Clean Build

REM ============================================================
REM SzTextCompar - Clean Build
REM Copies the project's own license and documentation files
REM next to the executable. No new license is generated.
REM ============================================================

cd /d "%~dp0"

set "SCRIPT_NAME=SzTextCompar.py"
set "APP_NAME=SzTextCompar"
set "VENV_DIR=build_venv"
set "DIST_DIR=dist\%APP_NAME%"
set "BUILD_LOG=%CD%\%APP_NAME%_pyinstaller_debug.log"
set "AUDIT_REPORT=%CD%\%APP_NAME%_full_audit.txt"

echo.
echo ============================================================
echo 1. Checking required files
echo ============================================================
echo.

if not exist "%SCRIPT_NAME%" (
    echo ERROR: "%SCRIPT_NAME%" was not found.
    pause
    exit /b 1
)

for %%F in ("LICENSE" "THIRD_PARTY_LICENSES.txt" "README.txt" "NOTICE.txt") do (
    if not exist "%%~F" (
        echo ERROR: Required file not found: %%~F
        pause
        exit /b 1
    )
)

echo All required files were found.

echo.
echo ============================================================
echo 2. Cleaning previous build files
echo ============================================================
echo.

if exist "%VENV_DIR%" rmdir /s /q "%VENV_DIR%"
if exist "build" rmdir /s /q "build"
if exist "dist" rmdir /s /q "dist"
if exist "%APP_NAME%.spec" del /q "%APP_NAME%.spec"
if exist "%BUILD_LOG%" del /q "%BUILD_LOG%"
if exist "%AUDIT_REPORT%" del /q "%AUDIT_REPORT%"

echo.
echo ============================================================
echo 3. Creating a clean virtual environment
echo ============================================================
echo.

where python >nul 2>nul
if errorlevel 1 (
    echo ERROR: Python was not found on PATH.
    pause
    exit /b 1
)

python -m venv "%VENV_DIR%"
if errorlevel 1 (
    echo ERROR: Failed to create the virtual environment.
    pause
    exit /b 1
)

call "%VENV_DIR%\Scripts\activate.bat"

echo.
echo ============================================================
echo 4. Installing PyInstaller
echo ============================================================
echo.

python -m pip install --upgrade pip
if errorlevel 1 (
    echo ERROR: Failed to upgrade pip.
    call "%VENV_DIR%\Scripts\deactivate.bat"
    pause
    exit /b 1
)

python -m pip install pyinstaller
if errorlevel 1 (
    echo ERROR: Failed to install PyInstaller.
    call "%VENV_DIR%\Scripts\deactivate.bat"
    pause
    exit /b 1
)

echo.
echo ============================================================
echo 5. Building the executable
echo ============================================================
echo.

python -m PyInstaller ^
    --noconfirm ^
    --clean ^
    --onedir ^
    --windowed ^
    --name "%APP_NAME%" ^
    --log-level=DEBUG ^
    "%SCRIPT_NAME%" > "%BUILD_LOG%" 2>&1

if errorlevel 1 (
    echo ERROR: The build failed.
    echo Check the build log:
    echo %BUILD_LOG%
    call "%VENV_DIR%\Scripts\deactivate.bat"
    pause
    exit /b 1
)

if not exist "%DIST_DIR%\%APP_NAME%.exe" (
    echo ERROR: The executable was not created.
    echo Check the build log:
    echo %BUILD_LOG%
    call "%VENV_DIR%\Scripts\deactivate.bat"
    pause
    exit /b 1
)

echo.
echo ============================================================
echo 6. Copying license and documentation files
echo ============================================================
echo.

copy /Y "LICENSE" "%DIST_DIR%\LICENSE" >nul
copy /Y "THIRD_PARTY_LICENSES.txt" "%DIST_DIR%\THIRD_PARTY_LICENSES.txt" >nul
copy /Y "README.txt" "%DIST_DIR%\README.txt" >nul
copy /Y "NOTICE.txt" "%DIST_DIR%\NOTICE.txt" >nul

if errorlevel 1 (
    echo ERROR: Failed to copy one or more documentation files.
    call "%VENV_DIR%\Scripts\deactivate.bat"
    pause
    exit /b 1
)

echo.
echo ============================================================
echo 7. Verifying copied files
echo ============================================================
echo.

for %%F in (
    "%DIST_DIR%\LICENSE"
    "%DIST_DIR%\THIRD_PARTY_LICENSES.txt"
    "%DIST_DIR%\README.txt"
    "%DIST_DIR%\NOTICE.txt"
) do (
    if not exist "%%~F" (
        echo ERROR: Missing file in the package: %%~nxF
        call "%VENV_DIR%\Scripts\deactivate.bat"
        pause
        exit /b 1
    )
)

echo All license and documentation files are next to the executable.

echo.
echo ============================================================
echo 8. Creating SHA256 audit report
echo ============================================================
echo.

powershell -NoProfile -ExecutionPolicy Bypass -Command ^
"$ErrorActionPreference = 'Stop'; ^
$distPath = Resolve-Path '%DIST_DIR%'; ^
$reportPath = '%AUDIT_REPORT%'; ^
$files = Get-ChildItem -LiteralPath $distPath -Recurse -File; ^
$sb = [System.Text.StringBuilder]::new(); ^
[void]$sb.AppendLine('======================================================================'); ^
[void]$sb.AppendLine(' SzTextCompar - BUILD AUDIT REPORT'); ^
[void]$sb.AppendLine(' Date: ' + (Get-Date)); ^
[void]$sb.AppendLine(' Package: ' + $distPath.Path); ^
[void]$sb.AppendLine(' Total files: ' + $files.Count); ^
[void]$sb.AppendLine('======================================================================'); ^
[void]$sb.AppendLine(''); ^
foreach ($file in $files) { ^
    $hash = Get-FileHash -LiteralPath $file.FullName -Algorithm SHA256; ^
    $relative = $file.FullName.Substring($distPath.Path.Length); ^
    [void]$sb.AppendLine('File: ' + $relative); ^
    [void]$sb.AppendLine('SHA256: ' + $hash.Hash); ^
    [void]$sb.AppendLine(''); ^
}; ^
Set-Content -LiteralPath $reportPath -Value $sb.ToString() -Encoding UTF8"

call "%VENV_DIR%\Scripts\deactivate.bat"

echo.
echo ============================================================
echo BUILD COMPLETED SUCCESSFULLY
echo ============================================================
echo.
echo Executable:
echo %DIST_DIR%\%APP_NAME%.exe
echo.
echo Included files:
echo - LICENSE
echo - THIRD_PARTY_LICENSES.txt
echo - README.txt
echo - NOTICE.txt
echo.
echo Audit report:
echo %AUDIT_REPORT%
echo.

notepad "%AUDIT_REPORT%"
pause
