#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

compiler=${AWPIRH_LEAN_EXE:-${LEAN_EXE:-lean}}
if ! command -v "$compiler" >/dev/null 2>&1; then
  echo 'LEAN_EXE_FOUND=FAIL'
  exit 2
fi
compiler=$(command -v "$compiler")
"$compiler" --version > lean_version.log 2>&1
cat lean_version.log
if ! grep -Fq 'version 4.33.0,' lean_version.log; then
  echo 'LEAN_VERSION_CHECK=FAIL_EXPECTED_4.33.0'
  exit 3
fi
cache_root=${MATHLIB_CACHE_ROOT:?Set MATHLIB_CACHE_ROOT to your existing cached project or Mathlib checkout}
if [[ -f "$cache_root/.lake/build/lib/lean/Mathlib.olean" ]] ||
   [[ -f "$cache_root/.lake/build/lib/lean/Mathlib/NumberTheory/LSeries/Nonvanishing.olean" ]]; then
  mathlib_root=$cache_root
elif [[ -f "$cache_root/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]]; then
  mathlib_root=$cache_root/.lake/packages/mathlib
else
  echo 'MATHLIB_CACHE=NOT_FOUND'
  exit 4
fi
build_dir=$PWD/.native-build
mkdir -p "$build_dir"
search_path=$build_dir:$mathlib_root/.lake/build/lib/lean
for dependency in "$cache_root"/.lake/packages/* "$mathlib_root"/.lake/packages/*; do
  if [[ -d "$dependency/.lake/build/lib/lean" ]]; then
    search_path=$search_path:$dependency/.lake/build/lib/lean
  fi
done
export LEAN_PATH=$search_path
jobs=${LEAN_JOBS:-4}
printf 'PACKAGE=STIRLINGS_PRODIGY_LEAN_v0_2_0\n' > run-build.log
if grep -Enr '\b(sorry|admit)\b|^[[:space:]]*axiom[[:space:]]' \
    --include='*.lean' AWPIRH AngularMaster RiemannHypothesis StirlingsProdigy StirlingsProdigy.lean Audit.lean \
    > source_scan.log; then
  echo 'PROJECT_SOURCE_SCAN=FAIL'
  cat source_scan.log
  exit 5
else
  scan_status=$?
  if [[ "$scan_status" -ne 1 ]]; then
    echo 'PROJECT_SOURCE_SCAN=ERROR'
    exit 5
  fi
fi
while IFS= read -r source || [[ -n "$source" ]]; do
  source=${source%$'\r'}
  [[ -z "$source" ]] && continue
  output=$build_dir/${source%.lean}.olean
  mkdir -p -- "$(dirname -- "$output")"
  rm -f -- "$output"
  printf 'COMPILE_START=%s\n' "$source" | tee -a run-build.log
  "$compiler" -j"$jobs" -o "$output" "$source" 2>&1 | tee -a run-build.log
  [[ -f "$output" ]]
  printf 'COMPILE_PASS=%s\n' "$source" | tee -a run-build.log
done < compile-order.txt
"$compiler" -j"$jobs" Audit.lean > run-audit.log 2>&1
grep -Fq 'STIRLINGS_PRODIGY_AXIOM_AUDIT=PASS COUNT=32' run-audit.log
if grep -Fq 'sorryAx' run-audit.log; then
  echo 'SORRYAX=FOUND'
  exit 6
fi
printf '%s\n' \
  'AXIOM_AUDIT=STANDARD_LOGICAL_AXIOMS_ONLY' \
  'SOLE_INPUT=STIRLINGS_PRODIGY' \
  'CONDITIONAL_NATIVE_RH_CLOSURE=PROVED' \
  'LOCAL_FIRST_ORDER_NATIVE_RH_EQUIVALENCE=PROVED' \
  'STIRLINGS_PRODIGY_ESTABLISHED=NO' \
  'STIRLINGS_PRODIGY_LOCAL_ESTABLISHED=NO' \
  'UNCONDITIONAL_RH_PROOF=NO' \
  'PROJECT_BUILD=PASS' \
  'RUN=PASS' | tee -a run-build.log
