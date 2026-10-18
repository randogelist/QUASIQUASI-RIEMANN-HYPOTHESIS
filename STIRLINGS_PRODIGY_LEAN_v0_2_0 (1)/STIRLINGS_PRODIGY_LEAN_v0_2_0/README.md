# STIRLINGS_PRODIGY — local first-order RH equivalence, v0.2.0

This update retains the original `STIRLINGS_PRODIGY` unchanged and adds a
**separately named** local premise. Its proved chain is:

```text
STIRLINGS_PRODIGY => STIRLINGS_PRODIGY_LOCAL <=> native RiemannHypothesis.
```

The new equivalence is:

```lean
theorem StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL_IFF_RH :
    StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL ↔ RiemannHypothesis
```

The original theorem remains:

```lean
theorem StirlingsProdigy.RH_of_STIRLINGS_PRODIGY
    (h : StirlingsProdigy.STIRLINGS_PRODIGY) : RiemannHypothesis
```

## Exact new local premise

`P = AngularMaster.actualProfile` is the squared modulus of the actual
Mathlib-backed theta on the upper semicircle. For every radius `r > 0`, every
interior angle `-1 < x < 1`, and every `epsilon > 0`, the local premise requires
some `eta > 0` such that

```text
P(r,x+h) - P(r,x) >= -epsilon*h
```

whenever `0 < h < eta` and `x+h <= 1`. The neighborhood may depend on the
radius, angle, and epsilon. No uniformity over all radii or finite angular
intervals is assumed. This is a local first-order lower increment criterion
for P, rather than the earlier global affine approximation for U = P_x.

## Proof of the equivalence

For the forward direction, actual differentiability makes the forward
difference quotients converge to `P_x(r,x)`. The local premise forces their
limit to be nonnegative. The mean value theorem gives angular monotonicity,
and the retained actual-theta zero-exclusion bridge gives native RH.

For the reverse direction, the retained proved actual-theta Hadamard
factorization gives angular monotonicity under RH. Its forward increments
are nonnegative, so they satisfy every local `-epsilon*h` bound. The
factorization and reverse sign bridge are included proved dependencies,
not axioms or extra theorem parameters.

The equivalence has no additional hypotheses. It does not prove either RH
or the local premise itself, and does not assert a new sign theorem for
`P_xx` or a complete classification of flows between equipotentials.

## Why the original premise has no new converse

The original premise is retained byte for byte in `StirlingsProdigy/Closure.lean`.
It defines one-sided within-interval endpoint jets

```text
U(r,x) = derivWithin (P r) [-1,1] x
A(r)   = U(r,1)
B(r)   = derivWithin (U r) [-1,1] 1
E(r,x) = U(r,x) - [A(r) - B(r)(1-x)]
```

and assumes, for every `r > 0`, all three clauses:

1. `E(r,x) >= 0` at every interior angle;
2. `2 B(r) <= A(r)`;
3. `B(r) > 0`.

It implies `U(r,x) >= B(r)(1+x) > 0`, hence RH. However, the actual
positive-axis asymptotics give `B(r)/A(r) ~ sqrt(r)*log(r)/8`, so its global
slope clause fails at large radii. This analytic obstruction is documented,
not formalized in Lean here. The new local criterion is not a renamed or
silently weakened definition of that original premise.

The classical asymptotic inputs are https://dlmf.nist.gov/25.4 and
https://dlmf.nist.gov/5.11.

## Run on native Windows

Use native Lean 4.33.0 and the existing compatible Mathlib cache:

```bat
run.cmd
```

The runner does not invoke network access, Lake, Python, PowerShell, or WSL.
It checks the compiler version, recompiles the included modules, prints the
definitions and endpoint theorems, and audits their transitive axioms.

Default cached projects:

```text
%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1
%USERPROFILE%\Downloads\awpi_phi_rh_lean_sieved_v0_1_1
```

Optional overrides:

```bat
set "AWPIRH_LEAN_EXE=C:\path\to\lean.exe"
set "MATHLIB_CACHE_ROOT=C:\path\to\cached-project"
run.cmd --no-pause
```

The cached project must contain
`.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean`.
Local rebuilt outputs take priority over caches from other projects.

The optional Linux runner supports an existing Mathlib checkout directly.
Use an explicit installed compiler executable for strictly offline execution:

```sh
AWPIRH_LEAN_EXE=/path/to/lean \
MATHLIB_CACHE_ROOT=/path/to/mathlib \
bash run.sh
```

## Audit and validation

`Audit.lean` checks the original closure and the new local equivalence.
Only `propext`, `Classical.choice`, and `Quot.sound` may appear in transitive
axiom dependencies. It rejects any additional dependency. The runners also
reject placeholder-proof tokens and local axiom declarations.

Successful execution reports `STIRLINGS_PRODIGY_AXIOM_AUDIT=PASS COUNT=32`,
`LOCAL_FIRST_ORDER_NATIVE_RH_EQUIVALENCE=PROVED`, and `RUN=PASS`.
The properties themselves remain unestablished: `UNCONDITIONAL_RH_PROOF=NO`.

`VALIDATION.txt` records the checks actually performed. The build and audit
logs contain actual compiler output. `SOURCE_PROVENANCE.txt` identifies the
72 retained modules, and `BUILD_INPUTS.sha256` binds the reviewed source bytes.
