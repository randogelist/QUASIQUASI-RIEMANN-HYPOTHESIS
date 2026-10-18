# Second full-x-range anchor — Lean 4.33.0

Public entry point: `import QQRH`. This package preserves the prior QQRH(2)
and QQRH(11) results and adds the bounded-radius full-angular anchor

\[
\forall\,0<r\le\frac{255}{7},\quad\forall\,-1<x<1:
\quad \partial_x P(r,x)\ge0.
\]

Here the functions are the actual Mathlib-backed analytic objects,

\[
\xi(s)=\frac{1+s(s-1)\operatorname{completedRiemannZeta}_0(s)}2,
\quad \Theta(z)=\xi\left(\tfrac12+\sqrt z\right),
\quad P(r,x)=\left|\Theta\left(r(x+i\sqrt{1-x^2})\right)\right|^2.
\]

The theorem has no zero-height, RH, or angular-positivity hypothesis.
Monotonicity holds on the **closed** angular interval `[-1,1]`. The derivative
statement uses its interior. Strict profile positivity is also proved for
`0 <= r <= 255/7` and `-1 <= x <= 1`, including the origin and both endpoints.
This is a finite-radius anchor; an unbounded sequence of radii is not proved.

## Public statements

```lean
import QQRH

#check QQRH.second_full_x_radius
-- secondFullXRadius = 255/7

#check QQRH.second_full_x_monotone
-- (r : ℝ) → 0 < r → r ≤ 255/7 →
-- MonotoneOn (QQRH.profile r) (Set.Icc (-1) 1)

#check QQRH.second_full_x_range_anchor
-- (r : ℝ) → 0 < r → r ≤ 255/7 →
-- (x : ℝ) → -1 < x → x < 1 →
-- 0 ≤ deriv (QQRH.profile r) x

#check QQRH.second_full_x_positive
-- (r : ℝ) → 0 ≤ r → r ≤ 255/7 →
-- (x : ℝ) → -1 ≤ x → x ≤ 1 → 0 < QQRH.profile r x

#check QQRH.two
#check QQRH.eleven
#check QQRH.of_positivity
```

## Analytic and algebraic proof

1. Set `p = 6283/2000`, `q = 100/2313`, and `A = 2/(1-q^3)`.
   A rational lower bound for pi, a finite Taylor bound for the exponential,
   and `(n+1)^2 >= 1+3n` give the actual theta-kernel estimate
   `norm(K(u)) <= A exp(-p*u)` for `u >= 1`.
   The Mellin inversion and paired strip exponents retain the two weights
   `u^(-1)` and `u^(-1/2)`. For `a >= 0`, the proved integral estimate is
   \[
   \int_1^\infty u^{-a}e^{-pu}\,du
   \le\frac{e^{-p}}p\left(1-\frac{a}{p+a+1}\right).
   \]
   Therefore, throughout `0 <= Re(s) <= 1`,
   \[
   |\operatorname{completedRiemannZeta}_0(s)|
   \le\frac{q}{p(1-q^3)}
      \left(2-\frac1{p+2}-\frac1{2p+3}\right)
   \le\frac9{385}.
   \]
2. On the critical strip, `norm(s*(s-1)) <= (Im s)^2 + 1/2`.
   If `|Im(s)| <= 13/2`, their product is at most
   \[
   \frac{171}{4}\frac9{385}=\frac{1539}{1540}<1.
   \]
   The defining equation for xi then excludes zeros. Thus every actual xi
   zero satisfies `13/2 < |Im(s)|`. No numerical zero table is used.
3. For a theta zero `alpha = (delta+i*gamma)^2`, put
   `g = |gamma|`, `h = |delta|`, and `D = g^2+h^2`.
   The strip and height bound give `h <= 1/2`, `g >= 13/2`.
   The inner radial threshold for a conjugate factor is
   \[
   D\frac{g-h}{g+h}\ge
   \left(\frac{169}{4}+\frac14\right)\frac67
   =\frac{255}{7}.
   \]
   Lean proves this inequality by explicit nonnegative polynomial
   factorizations. Consequently, with `q = r/|alpha|` and
   `c = Re(alpha)/|alpha|`, the quadratic vertex condition
   `2*q + c*(1+q^2) <= 0` holds. It makes the conjugate-factor squared
   modulus nondecreasing over all `-1 <= x <= 1`.
4. The unconditional canonical product retains complex zero locations.
   The symmetric finite products converge to **P(r,x)^2**. Their
   nonnegativity and monotonicity pass to the limit, then to `P` since
   `P >= 0`. Interior derivative nonnegativity follows. The analytic
   zero-arc argument supplies interior nonvanishing; the height bound
   also includes the negative-axis endpoint and radius zero.

New modules, all under `AngularMaster`:
`ThetaKernelAnchorBound`, `MellinAnchorBound`, `MellinPairedBound`,
`AnchorHeight`, `FullXGeometry`, `FullXProduct`, `SecondFullXAnchor`.

## Build and audit

Extract the ZIP and run `run.cmd` using the established native Windows
Lean 4.33.0 and Mathlib cache. For a noninteractive run:

```bat
run.cmd --no-pause
```

The runner accepts `AWPIRH_LEAN_EXE` or `LEAN_EXE`, `MATHLIB_CACHE_ROOT`,
and `LEAN_JOBS`. The cache root is an existing Lean project containing
`.lake/packages/mathlib`. It recompiles the included sources into this
package's own output directory and runs `Audit.lean`.

With a Lake-managed installation:

```sh
lake update
lake exe cache get
lake build QQRH
lake env lean Audit.lean
```

`BUILD_REPORT.txt`, `AUDIT.txt`, and `VERIFICATION_STATUS.json` record the
actual local verification. `Audit.lean` checks exact public theorem types,
instantiates the boundary radius, and prints transitive axiom dependencies
for the height gap and unconditional anchor endpoints. Standard logical
axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The Windows runner is statically reviewed; native Windows execution and
the Lake-managed workflow have not been tested in this Linux environment.

## Provenance

This is a dependency-closed extension of the earlier focused QQRH package.
The previous public theorems and their analytic proofs remain present.
The upstream classical factorization sources are from
[alejandrozu/RiemannHypothesis-Formalization](https://github.com/alejandrozu/RiemannHypothesis-Formalization),
commit `753938937e624d1c8bbe4c208517660a672d1b8e`, derived from
[TristenHarr/RiemannHypothesis](https://github.com/TristenHarr/RiemannHypothesis).
Their notices and Apache-2.0 license are retained. Exact attribution and
inherited Lean 4.33 compatibility changes are in `THIRD_PARTY_SOURCES.json`
and `LEAN_433_COMPATIBILITY.patch`.
