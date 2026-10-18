/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import RiemannHypothesis.ComplexAnalysis.RealSymmetry

/-!
# The real-zeros engine

The core theorem of the overflow-residue argument:

  anti-Herglotz logarithmic derivative
  + a pole-witness at every upper-half-plane zero
  + conjugation (Schwarz) symmetry
  ⇒ every zero is real.

## Main definitions

* `LogDerivPoleWitnessLaw f R` — every upper-half-plane zero of `f` produces
  positive upper-imaginary escape for the response `R`.

## Main results

* `antiHerglotz_forbids_upper_zeros` — pole witness + anti-Herglotz ⇒ no upper
  zeros.
* `realZeros_of_antiHerglotz_logDerivative` — the engine theorem.
-/

namespace OverflowResidueRH

open Complex

/-- **Log-derivative pole-witness law.** Every upper-half-plane zero of
`f` produces positive upper-imaginary escape for the response `R`. In
applications `R = logDerivativeResponse f`; the parameterization keeps
the abstraction sharp.

Discharged in concrete cases by local factorization `f(z) = (z − ρ)^m · g(z)`
with `g(ρ) ≠ 0`, applied to `Λ[f](z) = m / (z − ρ) + g'(z)/g(z)`. The
constructive discharge for any such decomposition is
`positiveEscape_of_localLogDerivPole` in `ComplexAnalysis.PoleProbe`. -/
structure LogDerivPoleWitnessLaw (f R : ℂ → ℂ) : Prop where
  upper_zero_forces_escape :
    ∀ ρ : ℂ, f ρ = 0 → 0 < ρ.im → PositiveUpperImaginaryEscape R

/-- **Anti-Herglotz forbids upper zeros.** Pole witness + anti-Herglotz
response ⇒ `f` has no upper-half-plane zeros. One line via the iff. -/
theorem antiHerglotz_forbids_upper_zeros
    {f R : ℂ → ℂ}
    (hpole : LogDerivPoleWitnessLaw f R)
    (hanti : AntiHerglotzUHP R) :
    ∀ ρ : ℂ, 0 < ρ.im → f ρ ≠ 0 := by
  intro ρ hupper hzero
  have hesc := hpole.upper_zero_forces_escape ρ hzero hupper
  exact (antiHerglotz_iff_no_positiveUpperEscape R).mp hanti hesc

/-- **Anti-Herglotz + Schwarz symmetry forces real zeros.** Trichotomy on
`ρ.im`:

* Upper zero: killed directly by `antiHerglotz_forbids_upper_zeros`.
* Lower zero: killed via conjugate reflection — `f (star ρ) = star (f ρ) = 0`
  with `(star ρ).im = −ρ.im > 0`, again contradicting
  `antiHerglotz_forbids_upper_zeros`. -/
theorem realZeros_of_antiHerglotz_logDerivative
    {f R : ℂ → ℂ}
    (hpole : LogDerivPoleWitnessLaw f R)
    (hanti : AntiHerglotzUHP R)
    (hsym : ∀ z : ℂ, f (star z) = star (f z)) :
    ∀ ρ : ℂ, f ρ = 0 → ρ.im = 0 := by
  intro ρ hρzero
  rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
  · -- lower zero ⇒ conjugate is upper zero ⇒ contradiction
    have hconj_zero : f (star ρ) = 0 := by
      rw [hsym ρ, hρzero]
      simp
    have hupper_conj : 0 < (star ρ).im := by
      rw [complex_star_im]
      linarith
    exact absurd hconj_zero
      (antiHerglotz_forbids_upper_zeros hpole hanti (star ρ) hupper_conj)
  · exact hzero
  · -- upper zero directly contradicts the engine
    exact absurd hρzero
      (antiHerglotz_forbids_upper_zeros hpole hanti ρ hpos)

/-- **Bundled hypotheses of the real-zeros engine.** A function `F` with
response `R` (in practice `R = Λ[F]`) together with the three facts that
force every zero of `F` onto the real axis:

* `poleWitness` — every upper-half-plane zero of `F` makes `R` escape upward
  (local-factorization content, discharged constructively in concrete cases);
* `antiHerglotz` — `R` satisfies the anti-Herglotz sign law on the upper
  half-plane;
* `conjugationSymmetry` — `F(z̄) = conj F(z)` (Schwarz reflection).

Wholly generic: no commitment to a specific `F`. -/
structure AntiHerglotzReflectionData where
  F : ℂ → ℂ
  R : ℂ → ℂ
  poleWitness : LogDerivPoleWitnessLaw F R
  antiHerglotz : AntiHerglotzUHP R
  conjugationSymmetry : ∀ z : ℂ, F (star z) = star (F z)

/-- **PROVED — every zero of `P.F` is real.** Immediate from the engine
theorem applied to the three bundled hypotheses. -/
theorem AntiHerglotzReflectionData.zeros_real (P : AntiHerglotzReflectionData) :
    ∀ ρ : ℂ, P.F ρ = 0 → ρ.im = 0 :=
  realZeros_of_antiHerglotz_logDerivative
    P.poleWitness P.antiHerglotz P.conjugationSymmetry

end OverflowResidueRH
