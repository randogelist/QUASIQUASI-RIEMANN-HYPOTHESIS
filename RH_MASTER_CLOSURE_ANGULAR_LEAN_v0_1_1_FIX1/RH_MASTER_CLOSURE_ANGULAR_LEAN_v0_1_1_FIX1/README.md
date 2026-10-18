# RH master closure and angular development — v0.1.1 FIX1

One source package, one native Windows Lean 4.33.0 runner, one literal Mathlib
`RiemannHypothesis` endpoint. The package combines the strongest compatible
actual-RH routes found in the supplied Lean archives with FIX9 regularity.

FIX1 explicitly rewrites the real-to-complex multiplication cast before using
`Complex.mul_cpow_ofReal_nonneg` in `AWPIRH/NativeCompletionReduction.lean`.
This corrects the mismatch reported by the Windows build at line 52. All
theorem statements, audit entries, and other mathematical sources are unchanged.

**This merged release has not been compiled.** Its source checks pass. The
earlier FIX9 Windows run passed, and the angular source archives contain prior
build reports; neither constitutes a build of this new merged release.

## Run

Place the ZIP in Downloads and run:

```cmd
cd /d "%USERPROFILE%\Downloads" && tar -xf "RH_MASTER_CLOSURE_ANGULAR_LEAN_v0_1_1_FIX1.zip" && call "RH_MASTER_CLOSURE_ANGULAR_LEAN_v0_1_1_FIX1\run.cmd"
```

The runner uses the existing native Lean 4.33.0 executable and Mathlib cache.
It uses no network, Lake, Python, PowerShell, or WSL. Default threads: 16.
The established overrides `AWPIRH_LEAN_EXE`, `LEAN_EXE`, `MATHLIB_CACHE_ROOT`,
and `LEAN_JOBS` remain supported. The default cache is the existing
`%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1` project, with its
Downloads location as fallback. No compiler or Mathlib binaries are bundled.

Every source is rebuilt in dependency order into a fresh local `.native-build`.
The full compile log is `run-build.log`; theorem types and transitive axiom
dependencies appear in `run-audit.log`. On failure, paste the first Lean error
and `FAILED_STAGE`, or attach the two logs.

## Main result and remaining premise

Write

\[
\Theta(z)=\xi(1/2+\sqrt z),\qquad
z(r,x)=r\bigl(x+i\sqrt{1-x^2}\bigr),\qquad
P(r,x)=|\Theta(z(r,x))|^2.
\]

Here `r` is the radius in the theta plane. On `-1 < x < 1`, the FIX9 ordinary
derivative and the angular Master's within derivative agree. No equality of
those two conventions is asserted at the endpoints.

The new master source states

\[
\mathrm{RH}\iff
\forall r>255/7\;\forall -1<x\le-84/85:\quad P_x(r,x)\ge0.
\]

Lean endpoint:

```lean
RHMaster.RH_MASTER_EQUIVALENCE :
  RiemannHypothesis ↔ RHMaster.AngularResidualNonnegative
```

The residual sign condition is **open**. The equivalence and conditional
closure do not prove it. Its smaller domain follows by combining the supplied
full-angle radius slab `r ≤ 255/7` with the supplied height gap `13/2`, which
the new source transports to QQRH(13) and the cutoff `-84/85`.

## Stronger merged routes

| Route | Explicit remaining input | Main declaration |
| --- | --- | --- |
| Residual angular sign | `AngularResidualNonnegative` | `RHMaster.RH_MASTER_CLOSURE` |
| Angular stationary points | `ActualNoRegularAngularStationary` | `RHMaster.native_RH_of_noRegularAngularStationary` |
| Arbitrary-slope QQRH | `AllSlopeQQRH`, or the cofinal version | `RHMaster.rh_iff_allSlopeQQRH` |
| Arbitrary-slope positivity | `AllSlopePositivity` | `RHMaster.rh_iff_allSlopePositivity` |
| Actual Cayley loss | Zero spectral loss at every nontrivial zero | `RHMaster.rh_iff_cayley_zero_loss` |
| Local pole + trace | Local direct-coefficient negativity and cofinal actual-xi Cayley-trace convergence for the supplied finite system | `RHMaster.NativeRoutes.rh_of_local_pole_and_cayley_trace` |
| Native row/product | Native subexponential energy and product coefficient identification | `RHMaster.NativeRoutes.rh_of_native_energy_and_coefficient_identity` |
| AWPI scalar/tail | Canonical plus passivity or the canonical exact-tail upper bound | `RHMaster.awpi_exact_tail_upper_iff_rh` |

The stationary-point route uses radius isolation, persistence of a negative
slope, and the intermediate value theorem. It needs no simple-zero premise.
The local-pole/trace route replaces the original global channel-analysis input
with the local pole coefficient-negativity input. Neither input is discharged.

Cayley loss nonnegativity alone is already available and is insufficient for
the zero-loss criterion. The AWPI transverse jet is the source package's
explicitly chosen product model; this merge does not identify it with an
independently defined historical Phi derivative.

`RHMaster.RH_MASTER_EQUIVALENCE_ATLAS` connects the residual condition, global
interior positivity, all/cofinal QQRH slopes, all-slope positivity, Cayley zero
loss, canonical AWPI tail upper bounds, and the frozen logarithmic Master.

## Source inventory and audit

- 240 compiled source modules, plus the separate `Audit.lean`.
- 1,835 theorem/lemma declarations in the source inventory, including private
  helpers: 1,762 `theorem` and 73 `lemma` declarations.
- 77 new bridge/coverage/closure theorem declarations in `RHMaster/`.
- 2,533 named source declarations in total.
- The audit checks all 2,460 explicit public named declarations and rejects
  transitive axioms other than `propext`, `Classical.choice`, and `Quot.sound`.
- 73 private source declarations are included in the source count. Private
  helpers used by audited public declarations are checked transitively.
  Generated constructors/projections are not separate source-count entries.
- Static checks found no duplicate public names, unresolved local imports,
  dependency cycles, or `sorry`/`admit`/custom-`axiom`/`native_decide` tokens.

These are **source counts**, not a claim that 1,835 theorems have passed this
merged build. The runner reports success only after compilation and audit.

`DECLARATIONS.tsv` gives every counted name and source location.
`VERIFICATION_STATUS.json` separates static checks from compilation status.
`SOURCE_MANIFEST.json` records hashes and matches to the attached archives;
the `provenance/` directory records the branch selections. The full source
selection and its exclusions are in `SOURCE_SELECTION.md`.

No unconditional RH theorem is claimed by this release.
