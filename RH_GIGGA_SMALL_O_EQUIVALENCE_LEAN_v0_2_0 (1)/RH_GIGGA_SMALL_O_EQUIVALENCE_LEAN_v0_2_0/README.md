# Native RH equivalence with the angular little-o premise

Lean 4.33.0, Mathlib v4.33.0. The main theorem is

```lean
theorem RHSmallO.rh_iff_small_o :
    RiemannHypothesis ↔ RHSmallO.SmallOPremise
```

Its literal mathematical statement is

\[
\mathrm{RH}\iff
I(r)-\pi rS_{\mathrm{line}}(r)=o(r),\qquad r\downarrow0.
\]

The objects are unchanged from the checked closure package:

\[
\Theta(z)=\xi(1/2+\sqrt z),\qquad
P(r,x)=|\Theta(r(x+i\sqrt{1-x^2}))|^2,
\]
\[
I(r)=\int_{-1}^{1}\frac{P_x(r,x)}{P(r,x)}\sqrt{1-x^2}\,dx,
\qquad
S_{\mathrm{line}}(r)=
\sum_{\substack{0<\gamma\le1/r\\\mathrm{critical\ line}}}
\frac{m_\gamma}{\gamma^2}.
\]

`I` is the literal interval integral. The cutoff uses the actual opposite-paired
zero occurrence divisor, so analytic multiplicities are retained. Its support
is proved finite. No simplicity or zero-enumeration hypothesis is used.

`SmallOPremise` is Mathlib's actual `Asymptotics.IsLittleO` at
`nhdsWithin 0 (Set.Ioi 0)`.

## Proved directions

* `RHSmallO.rh_of_small_o`: the little-o premise implies native Mathlib RH.
* `RHSmallO.small_o_of_rh`: native Mathlib RH implies the same little-o premise.
* `RHSmallO.small_o_iff_RH` and `RHSmallO.rh_iff_small_o`: both orientations.
* `RHSmallO.rh_iff_angular_integral_isLittleO`: the expanded equivalence.

The forward direction uses the proved limits `I(r)/r -> pi*q1`, `I(r) -> 0`,
the unconditional reciprocal-zero trace, and positivity of every omitted
spectral contribution.

For the reverse direction, RH places all actual zero representatives on the
real pullback axis. Each fixed contribution eventually enters the cutoff.
A finite-sum argument using summability gives `S_line(r) -> q1`. Hence
`(I(r)-pi*r*S_line(r))/r -> 0`, which is exactly the little-o premise.

The exact finite-radius GIGGA identity is not required by this proof. The
normalized integral limit is proved directly. The equivalence theorem adds
neither RH nor the little-o premise as an axiom.

## Run on native Windows

Extract the ZIP and run `run.cmd`. The runner reuses the existing native
Lean 4.33.0 and Mathlib cache, recompiles all 87 included project modules,
and executes `Audit.lean`. It does not fetch dependencies or invoke Lake,
Python, PowerShell, or WSL.

If needed, set `LEAN_EXE` (or `AWPIRH_LEAN_EXE`) and `MATHLIB_CACHE_ROOT` to
the existing compiler and cached project. Use `run.cmd --no-pause` to omit
the final pause.

Expected final markers include:

```text
REVERSE_RH_TO_SMALL_O=PROVED
SMALL_O_RH_EQUIVALENCE=PROVED
PROJECT_BUILD=PASS
RUN=PASS
```

See `BUILD_REPORT.txt`, `BUILD_AUDIT.txt`, `BUILD_MANIFEST.json`, and
`validation/` for the actual validation performed. Linux compilation and
static Windows-runner review are distinguished in the report.

## Source provenance

The existing analytic dependency closure is preserved from the verified
`RH_GIGGA_SMALL_O_CLOSURE_LEAN_v0_1_0` package. That package retained the
supplied `QQRH_FULL_X_ANCHOR_2_LEAN_v0_1_0` and angular regularity sources,
including their existing copyright and Apache-2.0 license notices.

The three added modules are `ReverseCutoff.lean`, `ScalarConverse.lean`,
and `RHSmallOEquivalence.lean`.
