@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "RUN_EXIT=1"
set "RUN_PUSHED=0"
set "RUN_STEP=Opening the project directory"
pushd "%~dp0"
if errorlevel 1 goto :failed
set "RUN_PUSHED=1"
set "RUN_STEP=Creating log files"
> "run-build.log" echo PACKAGE=RH_MISTERPREMISE_LEAN_v0_1_0
if errorlevel 1 goto :failed
> "run-audit.log" echo Audit has not run yet.
if errorlevel 1 goto :failed

echo PACKAGE=RH_MISTERPREMISE_LEAN_v0_1_0
echo RUNNER_ENTERED=PASS
echo RUNNER=NATIVE_WINDOWS_LEAN_433_FASTCACHE
echo NETWORK=NOT_USED
echo LAKE=NOT_USED
echo PYTHON=NOT_USED
echo POWERSHELL=NOT_USED
echo WSL=NOT_USED

rem Use the established native executable overrides and elan installation.
if defined AWPIRH_LEAN_EXE set "LEAN_EXE=%AWPIRH_LEAN_EXE%"
if defined LEAN_EXE goto :compiler_selected
if defined ELAN_HOME goto :compiler_elan_home
set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
goto :compiler_selected
:compiler_elan_home
set "LEAN_EXE=%ELAN_HOME%\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
:compiler_selected
set "RUN_STEP=Checking native Lean 4.33.0"
if not exist "%LEAN_EXE%" goto :missing_lean
"%LEAN_EXE%" --version > "lean_version.log" 2>&1
set "RUN_EXIT=%errorlevel%"
if not "%RUN_EXIT%"=="0" goto :failed
type "lean_version.log"
type "lean_version.log" >> "run-build.log"
findstr /L /C:"version 4.33.0," "lean_version.log" >nul
set "RUN_EXIT=%errorlevel%"
if not "%RUN_EXIT%"=="0" goto :wrong_version
for %%F in ("%LEAN_EXE%") do set "LEAN_BIN=%%~dpF"
for %%F in ("%LEAN_BIN%..") do set "TOOLCHAIN=%%~fF"

rem Reuse the prior cached project; explicit overrides never silently fall back.
if defined MATHLIB_CACHE_ROOT goto :cache_override
set "CACHE_ROOT=%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
if exist "%CACHE_ROOT%\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean" goto :cache_selected
set "CACHE_ROOT=%USERPROFILE%\Downloads\awpi_phi_rh_lean_sieved_v0_1_1"
goto :cache_selected
:cache_override
set "CACHE_ROOT=%MATHLIB_CACHE_ROOT%"
:cache_selected
set "RUN_STEP=Checking the existing Mathlib cache"
if not exist "%CACHE_ROOT%\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean" goto :missing_cache
echo MATHLIB_CACHE=READY
echo CACHE_ROOT="%CACHE_ROOT%"
>> "run-build.log" echo CACHE_ROOT="%CACHE_ROOT%"

rem Local outputs take priority. Do not import stale outputs from other projects.
set "BUILD_DIR=%CD%\.native-build"
set "RUN_STEP=Removing previous local build outputs"
set "RUN_EXIT=1"
if exist "%BUILD_DIR%" rmdir /s /q "%BUILD_DIR%"
if exist "%BUILD_DIR%" goto :failed
set "RUN_STEP=Preparing the fresh local build directory"
mkdir "%BUILD_DIR%"
if not exist "%BUILD_DIR%\" goto :failed
rem Reset, rather than extend, any inherited LEAN_PATH. Never add CACHE_ROOT's
rem own build directory or the current source directory to the import path.
set "LEAN_PATH=%BUILD_DIR%"
for /d %%D in ("%CACHE_ROOT%\.lake\packages\*") do (
  set "CACHE_PACKAGE=%%~fD"
  call :append_cache
)
set "LEAN_PATH=%LEAN_PATH%;%TOOLCHAIN%\lib\lean"
set "LEAN_SYSROOT=%TOOLCHAIN%"
set "PATH=%TOOLCHAIN%\bin;%PATH%"
if not defined LEAN_JOBS set "LEAN_JOBS=16"
set "LEAN_NUM_THREADS=%LEAN_JOBS%"
echo LEAN_JOBS=%LEAN_JOBS%
echo CACHE_PATH_SETUP=PASS

rem The generated list is the sole order of project source modules.
set "RUN_STEP=Reading the source dependency order"
set "RUN_EXIT=1"
if not exist "compile-order.txt" goto :failed
set "SOURCE_COUNT=0"
> "source_scan.log" echo MISTERPREMISE_SOURCE_SCAN
if errorlevel 1 goto :failed

rem Lexical checks supplement the transitive kernel audit. Scan exactly the
rem compiled source list and Audit.lean; do not recurse into retained archives.
set "RUN_STEP=Scanning local Lean sources"
for /f "usebackq delims=" %%M in ("compile-order.txt") do (
  call :scan_source "%%M"
  if errorlevel 1 goto :failed
)
if "%SOURCE_COUNT%"=="0" goto :empty_source_list
call :scan_source "Audit.lean"
if errorlevel 1 goto :failed
echo PROJECT_SOURCE_SCAN=PASS

rem Build directories are created from each listed module's relative path.
rem Every module is compiled again into a completely fresh .native-build.
for /f "usebackq delims=" %%M in ("compile-order.txt") do (
  call :compile "%%M"
  if errorlevel 1 goto :failed
)

set "RUN_STEP=Auditing theorem types and transitive axiom dependencies"
> "run-audit.log" echo MISTERPREMISE_PACKAGE_AXIOM_AUDIT
call :audit "Audit.lean"
if errorlevel 1 goto :failed

set "RUN_EXIT=0"
echo AUDIT_PASS=ALL_LOADED_PROJECT_DECLARATIONS
echo AXIOM_AUDIT=STANDARD_LOGICAL_AXIOMS_ONLY
echo SORRYAX=NONE
echo MISTERPREMISE_EQUIVALENCE=PROVED
echo MISTERPREMISE=EXPLICIT_UNPROVED_INPUT
echo RH_ENDPOINT=ACTUAL_MATHLIB_RIEMANN_HYPOTHESIS
echo RH_PROOF=NOT_CLAIMED
echo MISTERPREMISE_MODULES=COMPILED
echo PROJECT_BUILD=PASS
echo RUN=PASS
>> "run-build.log" echo AXIOM_AUDIT=STANDARD_LOGICAL_AXIOMS_ONLY
>> "run-build.log" echo SORRYAX=NONE
>> "run-build.log" echo RH_PROOF=NOT_CLAIMED
>> "run-build.log" echo MISTERPREMISE_MODULES=COMPILED
>> "run-build.log" echo MISTERPREMISE_EQUIVALENCE=PROVED
>> "run-build.log" echo MISTERPREMISE=EXPLICIT_UNPROVED_INPUT
>> "run-build.log" echo PROJECT_BUILD=PASS
echo.
echo Build details: run-build.log
echo Theorem types and axiom dependencies: run-audit.log
goto :finish

:append_cache
if exist "%CACHE_PACKAGE%\.lake\build\lib\lean" set "LEAN_PATH=%LEAN_PATH%;%CACHE_PACKAGE%\.lake\build\lib\lean"
exit /b 0

rem FINDSTR uses a literal tab inside the following whitespace character sets.
rem Same-line attributes/modifiers are covered in addition to bare axioms.
:scan_source
set "RUN_SRC=%~1"
set "RUN_SRC=%RUN_SRC:/=\%"
set "RUN_STEP=Scanning %RUN_SRC%"
set "RUN_EXIT=1"
if not exist "%RUN_SRC%" (
  echo SOURCE_FILE=MISSING "%RUN_SRC%"
  exit /b 1
)
findstr /N /I /R /C:"\<sorry\>" /C:"\<admit\>" /C:"^[ 	]*axiom\>" /C:"^[ 	]*@.*\<axiom\>" /C:"^[ 	]*private[ 	].*\<axiom\>" /C:"^[ 	]*protected[ 	].*\<axiom\>" /C:"^[ 	]*noncomputable[ 	].*\<axiom\>" /C:"^[ 	]*unsafe[ 	].*\<axiom\>" "%RUN_SRC%" >> "source_scan.log" 2>&1
set "RUN_EXIT=%errorlevel%"
if "%RUN_EXIT%"=="0" (
  type "source_scan.log"
  echo PROJECT_SOURCE_SCAN=FAIL
  echo FAILED_SOURCE="%RUN_SRC%"
  set "RUN_EXIT=5"
  exit /b 1
)
if not "%RUN_EXIT%"=="1" exit /b 1
set /a SOURCE_COUNT+=1 >nul
set "RUN_EXIT=0"
exit /b 0

:compile
set "RUN_SRC=%~1"
set "RUN_SRC=%RUN_SRC:/=\%"
set "RUN_STEP=Compiling %~1"
set "RUN_OUT=%BUILD_DIR%\%RUN_SRC:.lean=.olean%"
set "RUN_EXIT=1"
if not exist "%RUN_SRC%" exit /b 1
for %%D in ("%RUN_OUT%") do if not exist "%%~dpD" mkdir "%%~dpD"
for %%D in ("%RUN_OUT%") do if not exist "%%~dpD" exit /b 1
if exist "%RUN_OUT%" del /q "%RUN_OUT%"
if exist "%RUN_OUT%" exit /b 1
echo COMPILE_START=%RUN_SRC%
>> "run-build.log" echo COMPILE_START=%RUN_SRC%
"%LEAN_EXE%" -j%LEAN_JOBS% -o "%RUN_OUT%" "%RUN_SRC%" > "last_compile.log" 2>&1
set "RUN_EXIT=%errorlevel%"
type "last_compile.log"
type "last_compile.log" >> "run-build.log"
if not "%RUN_EXIT%"=="0" exit /b 1
if not exist "%RUN_OUT%" (
  set "RUN_EXIT=1"
  exit /b 1
)
echo COMPILE_PASS=%RUN_SRC%
>> "run-build.log" echo COMPILE_PASS=%RUN_SRC%
exit /b 0

:audit
set "RUN_STEP=Auditing %~1"
echo AUDIT_START=%~1
"%LEAN_EXE%" -j%LEAN_JOBS% "%~1" > "last_audit.log" 2>&1
set "RUN_EXIT=%errorlevel%"
type "last_audit.log" >> "run-audit.log"
if not "%RUN_EXIT%"=="0" (
  type "last_audit.log"
  exit /b 1
)
findstr /L /C:"MISTERPREMISE_AXIOM_AUDIT=PASS" "last_audit.log" >nul
if errorlevel 1 (
  set "RUN_EXIT=7"
  echo AUDIT_RECEIPT=MISSING
  exit /b 1
)
findstr /L /C:"sorryAx" "last_audit.log" >nul
set "RUN_EXIT=%errorlevel%"
if "%RUN_EXIT%"=="0" (
  set "RUN_EXIT=6"
  echo SORRYAX=FOUND
  exit /b 1
)
if not "%RUN_EXIT%"=="1" exit /b 1
set "RUN_EXIT=0"
echo AUDIT_PASS=%~1
exit /b 0


:empty_source_list
echo COMPILE_ORDER=EMPTY
set "RUN_EXIT=8"
goto :failed
:missing_lean
echo LEAN_EXE_FOUND=FAIL
echo EXPECTED="%LEAN_EXE%"
echo Set AWPIRH_LEAN_EXE or LEAN_EXE to your native Lean 4.33.0 executable.
set "RUN_EXIT=2"
goto :failed
:wrong_version
echo LEAN_VERSION_CHECK=FAIL_EXPECTED_4.33.0
set "RUN_EXIT=3"
goto :failed
:missing_cache
echo MATHLIB_CACHE=NOT_FOUND
echo CACHE_ROOT="%CACHE_ROOT%"
echo Set MATHLIB_CACHE_ROOT to your existing cached project root.
set "RUN_EXIT=4"
goto :failed
:failed
if "%RUN_EXIT%"=="0" set "RUN_EXIT=1"
echo.
echo PROJECT_BUILD=FAIL
echo FAILED_STAGE=%RUN_STEP%
echo EXIT_CODE=%RUN_EXIT%
if "%RUN_PUSHED%"=="0" goto :finish
if exist "run-build.log" echo Build details: "%CD%\run-build.log"
if exist "run-audit.log" echo Audit details: "%CD%\run-audit.log"
:finish
echo.
if /I not "%~1"=="--no-pause" pause
if "%RUN_PUSHED%"=="1" popd
endlocal & exit /b %RUN_EXIT%
