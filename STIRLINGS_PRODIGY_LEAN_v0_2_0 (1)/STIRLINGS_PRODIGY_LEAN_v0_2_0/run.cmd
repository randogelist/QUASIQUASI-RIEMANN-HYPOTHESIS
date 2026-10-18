@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "RUN_EXIT=1"
set "RUN_PUSHED=0"
set "RUN_STEP=Opening the project directory"
pushd "%~dp0"
if errorlevel 1 goto :failed
set "RUN_PUSHED=1"
set "RUN_STEP=Creating log files"
> "run-build.log" echo PACKAGE=STIRLINGS_PRODIGY_LEAN_v0_2_0
if errorlevel 1 goto :failed
> "run-audit.log" echo Audit has not run yet.
if errorlevel 1 goto :failed

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
set "RUN_STEP=Preparing local build directories"
if not exist "%BUILD_DIR%\AWPIRH" mkdir "%BUILD_DIR%\AWPIRH"
if not exist "%BUILD_DIR%\AWPIRH" goto :failed
if not exist "%BUILD_DIR%\AngularMaster" mkdir "%BUILD_DIR%\AngularMaster"
if not exist "%BUILD_DIR%\AngularMaster" goto :failed
if not exist "%BUILD_DIR%\StirlingsProdigy" mkdir "%BUILD_DIR%\StirlingsProdigy"
if not exist "%BUILD_DIR%\StirlingsProdigy" goto :failed
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

rem Lexical checks supplement the transitive kernel audit.
set "RUN_STEP=Scanning local Lean sources"
findstr /S /N /I /R /C:"\<sorry\>" /C:"\<admit\>" /C:"^[ ]*axiom " AWPIRH\*.lean AngularMaster\*.lean RiemannHypothesis\*.lean StirlingsProdigy\*.lean StirlingsProdigy.lean Audit.lean > "source_scan.log" 2>&1
set "RUN_EXIT=%errorlevel%"
if "%RUN_EXIT%"=="0" goto :source_fail
if not "%RUN_EXIT%"=="1" goto :failed
echo PROJECT_SOURCE_SCAN=PASS

rem Recompile every included source, including actual theta and the native RH bridge.
set "RUN_STEP=Reading the source dependency order"
if not exist "compile-order.txt" goto :failed
for /f "usebackq delims=" %%M in ("compile-order.txt") do (
  call :compile "%%M"
  if errorlevel 1 goto :failed
)

set "RUN_STEP=Auditing theorem types and axioms"
> "run-audit.log" echo FULL_PACKAGE_AXIOM_AUDIT
for %%A in (Audit.lean) do (
  call :audit "%%A"
  if errorlevel 1 goto :failed
)

set "RUN_EXIT=0"
echo AUDIT_PASS=SELECTED_CLOSURE_DECLARATIONS
echo AXIOM_AUDIT=STANDARD_LOGICAL_AXIOMS_ONLY
echo SORRYAX=NONE
echo SOLE_INPUT=STIRLINGS_PRODIGY
echo CONDITIONAL_NATIVE_RH_CLOSURE=PROVED
echo LOCAL_FIRST_ORDER_NATIVE_RH_EQUIVALENCE=PROVED
echo STIRLINGS_PRODIGY_ESTABLISHED=NO
echo STIRLINGS_PRODIGY_LOCAL_ESTABLISHED=NO
echo UNCONDITIONAL_RH_PROOF=NO
echo PROJECT_BUILD=PASS
echo RUN=PASS
>> "run-build.log" echo PROJECT_BUILD=PASS
>> "run-build.log" echo CONDITIONAL_NATIVE_RH_CLOSURE=PROVED
echo.
echo Build details: run-build.log
echo Theorem types and axiom dependencies: run-audit.log
goto :finish

:append_cache
if exist "%CACHE_PACKAGE%\.lake\build\lib\lean" set "LEAN_PATH=%LEAN_PATH%;%CACHE_PACKAGE%\.lake\build\lib\lean"
exit /b 0

:compile
set "RUN_SRC=%~1"
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
findstr /L /C:"STIRLINGS_PRODIGY_AXIOM_AUDIT=PASS COUNT=32" "last_audit.log" >nul
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
:source_fail
type "source_scan.log"
echo PROJECT_SOURCE_SCAN=FAIL
set "RUN_EXIT=5"
goto :failed
:audit_fail
type "run-audit.log"
goto :failed
:sorry_found
echo SORRYAX=FOUND
set "RUN_EXIT=6"
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
