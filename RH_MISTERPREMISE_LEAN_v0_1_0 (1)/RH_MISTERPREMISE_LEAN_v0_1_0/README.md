# RH and MISTERPREMISE — v0.1.0

The package formalizes the exact equivalence

\[
\boxed{\mathrm{MISTERPREMISE}\iff\mathrm{RH}}.
\]

The endpoint is Mathlib's native `RiemannHypothesis`. **MISTERPREMISE remains
unproved: this is an equivalence theorem, not an unconditional proof of RH.**

## The frozen premise

\[
\Theta(z)=\xi(\tfrac12+\sqrt z),\qquad
P(r,x)=\left|\Theta\!\left(r(x+i\sqrt{1-x^2})\right)\right|^2,
\qquad A(r,x)=\partial_xP(r,x),
\]

\[
\kappa(r)=\inf_{R\ge85/2}
\frac{(R-\tfrac12)(R^2+r^2)}{2rR^2}.
\]

`MISTERPREMISE` means

\[
\forall r>255/7\;\exists M_r>0\;\forall -1<x\le-\kappa(r):
\quad A(r,x)>0\Longrightarrow
(1+x)\,\partial_xA(r,x)\le M_r A(r,x).
\]

The constant is finite and uniform in `x` for each radius. It may depend
arbitrarily on `r`. There is no additional positivity assumption on
`P_xx`, no simple-zero assumption, and no bound uniform over all radii.
The critical line corresponds to `x = -1`.

```lean
MisterPremise.MISTERPREMISE_iff_RiemannHypothesis :
  MisterPremise.MISTERPREMISE ↔ RiemannHypothesis

MisterPremise.RiemannHypothesis_iff_MISTERPREMISE :
  RiemannHypothesis ↔ MisterPremise.MISTERPREMISE
```

The forward proof combines the retained zero-height and strip geometry with
weighted differential continuation: a positive angular slope to the right of
a hypothetical off-line zero propagates back to that zero, contradicting
stationarity. The reverse proof uses the RH canonical product and analyticity
to bound the weighted logarithmic derivative, including at multiple zeros.

## Run on native Windows

Place the ZIP in Downloads and run:

```cmd
cd /d "%USERPROFILE%\Downloads" && tar -xf "RH_MISTERPREMISE_LEAN_v0_1_0.zip" && call "RH_MISTERPREMISE_LEAN_v0_1_0\run.cmd"
```

The runner requires native Lean **4.33.0** and the existing compatible Mathlib
cache. It uses no network, Lake, Python, PowerShell, or WSL. Compiler and cache
binaries are not included. The supported overrides are `AWPIRH_LEAN_EXE`,
`LEAN_EXE`, `MATHLIB_CACHE_ROOT`, and `LEAN_JOBS` (default 16).

The default cache root is
`%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1`, with the corresponding
Downloads directory as fallback. `MATHLIB_CACHE_ROOT` names a cached project
root containing `.lake\packages\mathlib` and the other cached dependencies.

The delivered dependency closure uses `MisterPremise/MathlibImports.lean`,
an explicit bundle of genuine Mathlib modules. Bare `import Mathlib` commands
were replaced with that bundle where needed; it adds no mathematical
definitions or assumptions. The exact import changes and original source
hashes are recorded in `SOURCE_PROVENANCE.json` and
`local-validation/import-normalization.json`.

`SOURCE_COUNTS.json` separates explicit `theorem`/`lemma` counts for the new
MISTERPREMISE modules and retained sources. `DECLARATIONS.tsv` lists the counted
source declarations. `SHA256SUMS.json` identifies the delivered files.

Every listed source is recompiled into a fresh local `.native-build`. The
runner then checks the exact theorem endpoints and audits every loaded
project declaration, including private helpers and generated declarations.
Transitive dependencies are restricted to `propext`, `Classical.choice`, and
`Quot.sound`. Source scanning also rejects unfinished proof tokens and custom
axiom declarations.

Success requires both `PROJECT_BUILD=PASS` and
`MISTERPREMISE_AXIOM_AUDIT=PASS`. The complete build log is `run-build.log`; the
endpoint and transitive dependency audit is `run-audit.log`. The audit reports
its project declaration and theorem-constant counts. Those kernel environment
counts include generated declarations and differ from source-level
`theorem`/`lemma` counts. Validation performed for the release is recorded
separately in `VERIFICATION_STATUS.json`.
