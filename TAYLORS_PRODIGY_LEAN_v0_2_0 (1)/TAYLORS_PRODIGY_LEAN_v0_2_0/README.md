# TAYLORS-PRODIGY-PREMISE

Version: `TAYLORS_PRODIGY_LEAN_v0_2_0`

The package proves the equivalence

```lean
TaylorsProdigy.TAYLORS_PRODIGY_PREMISE_iff_RH :
  TaylorsProdigy.TAYLORS_PRODIGY_PREMISE ↔ RiemannHypothesis
```

`RiemannHypothesis` is Mathlib's native statement about `riemannZeta`.
The named premise is a definition and an explicit theorem argument. It is
not declared as an axiom, and no proof of the premise is supplied.

## The sole research input

The actual objects are

\[
\Theta(z)=\xi(1/2+\sqrt z),\quad
P(r,x)=|\Theta(r(x+i\sqrt{1-x^2}))|^2,
\quad H(r,x)=\partial_xP(r,x),
\quad F_r(\theta)=H(r,\cos\theta).
\]

`TAYLORS_PRODIGY_PREMISE` says: for every `r > 0`, there is a real
function `rate` such that

- `rate` is interval-integrable on `[0,b]` for every `0 < b < pi`;
- `rate(theta) >= 0` for `0 < theta < pi`;
- wherever `F r theta > 0` in this open interval,
  `-rate theta * F r theta <= deriv (F r) theta`.

The coefficient is only assumed integrable, not continuous. By the proved
chain rule, the last inequality is exactly

\[
\sin\theta\,P_{xx}(r,\cos\theta)
\le\operatorname{rate}(\theta)P_x(r,\cos\theta).
\]

No rate bound at `pi` and no bound uniform in `r` are required. Integrability
through every prospective *interior* zero is essential. Taylor expansion
alone does not establish this premise.

## Forward implication

1. For a continuous, interior-differentiable real signal, an integrable
   nonnegative rate and `f' >= -rate*f` only while `f > 0` prevent a first
   zero. The quantitative result is
   `f(a) * exp(-integral rate) <= f(b)`.
2. The actual theta function is entire. Its angular slope and angle pullback
   are smooth on the open angular interval.
3. The premise propagates a positive slope from any interior `y` to every
   interior `x <= y` on the same circle.
4. A hypothetical interior theta zero has squared-modulus profile zero and
   therefore slope zero. Analytic uniqueness and the mean-value theorem
   supply a positive slope to its right. Propagation gives a contradiction.
5. Conjugation excludes the lower half-plane. A retained, unconditional
   low-height estimate excludes positive-real theta zeros. The proved actual
   theta/xi/zeta geometry then yields native `RiemannHypothesis`.

## Reverse implication

Assuming native RH, the actual Hadamard product supplies positive affine
angular factors and summable reciprocal zero scales. Their locally uniform
complex product defines a smooth real angular extension beyond `x = 1`.
On `-1 < x < 1` it agrees with the literal actual profile.

Removing any one factor leaves a monotone quotient. Its derivative gives
an explicit positive lower bound for the extended angular slope wherever
the profile is positive. Under RH the profile is positive for
`-1 < x <= 1`; this includes the starting endpoint.

The resulting smooth positive angle extension `g` agrees with `F` on
`0 < theta < pi`. Define

\[
\lambda_r(\theta)=\max\{0,-g'(\theta)/g(\theta)\}.
\]

This rate is continuous on `[0,pi)` and therefore integrable on each
`[0,b]` with `b < pi`. It satisfies the exact original differential
inequality. The case of an empty zero index is handled separately by the
constant angular product and the zero rate.

The original `TAYLORS_PRODIGY_PREMISE` definition is byte-for-byte unchanged
from v0.1.0. No additional research condition is inserted.
Neither side of the equivalence is established unconditionally.

The forward proof does not assume a positive derivative at `x = 1`. The ordinary
derivative of the total square-root profile at that endpoint need not equal
its angular boundary extension. Every derivative of the literal square-root
profile used in the forward argument is at an interior point; the hypothetical
zero supplies its own seed. The reverse argument justifies its endpoint
derivatives using the smooth product extension.

## Run on Windows, offline

Extract the archive, enter its directory, and run:

```bat
run.cmd
```

Requirements: native **Lean 4.33.0** and your existing Mathlib cache for that
compiler. The runner uses no network, Lake, Python, PowerShell, or WSL.
It recompiles every included source, then audits every new Taylor declaration and the transitive dependencies of both directions and the equivalence.

The default cache locations are
`%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1` and
`%USERPROFILE%\Downloads\awpi_phi_rh_lean_sieved_v0_1_1`.
Optional overrides:

```bat
set "AWPIRH_LEAN_EXE=C:\path\to\lean.exe"
set "MATHLIB_CACHE_ROOT=C:\path\to\cached-project"
run.cmd --no-pause
```

`MATHLIB_CACHE_ROOT` is the project containing `.lake\packages\mathlib`.
The runner requires the cached modules used by this package. `LEAN_JOBS`
is optional; its default is 16.

Success requires both a zero compiler exit code and the audit receipt
`TAYLORS_PRODIGY_AXIOM_AUDIT=PASS`.
The runner prints `PREMISE_PROVED=NO` and `UNCONDITIONAL_RH=NO` explicitly.

## Verification and files

The included build report distinguishes the Linux Lean 4.33 verification
from the Windows runner, which has been statically reviewed.
The only permitted transitive axioms are Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

| File | Role |
| --- | --- |
| `TaylorProdigy/Comparison.lean` | Genuine real-analysis proof of finite-rate comparison and its quantitative lower bound |
| `TaylorProdigy/Objects.lean` | Actual functions, proved interior regularity, chain rule, and named premise |
| `TaylorProdigy/ZeroExclusion.lean` | Positive slope from an alleged zero; contradiction by transport |
| `TaylorProdigy/Closure.lean` | Discharges all actual-function interfaces and proves conditional native RH |
| `TaylorProdigy/PositiveExtension.lean` | Constructs an integrable rate from a positive smooth endpoint extension |
| `TaylorProdigy/AngularExtension.lean` | Builds the entire angular product and matches it to the actual profile |
| `TaylorProdigy/StrictProductSlope.lean` | A selected factor gives strict positivity of the derivative |
| `TaylorProdigy/ActualPositivity.lean` | RH gives positive actual profile, including `x = 1` |
| `TaylorProdigy/Reverse.lean` | Proves RH implies the unchanged premise |
| `TaylorProdigy/Equivalence.lean` | Combines the two proved implications |
| `Audit.lean` | Displays definitions and theorem types; checks all new declarations and transitive endpoint dependencies |
| `SOURCE_PROVENANCE.txt` | Retained sources from the supplied angular package |
| `BUILD_REPORT.txt` | Checks actually executed |

No unconditional proof of RH is claimed.
