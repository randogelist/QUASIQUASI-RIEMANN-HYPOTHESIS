import Merger02.FiniteFilter

namespace Merger02
open scoped BigOperators Polynomial

/-- Normalized finite polynomial used to cancel a chosen finite set of poles. -/
noncomputable def poleFilterPolynomial (E : Finset ℂ) : ℂ[X] :=
  ∏ w ∈ E, (1 - Polynomial.C w⁻¹ * Polynomial.X)

@[simp] theorem poleFilterPolynomial_eval (E : Finset ℂ) (v : ℂ) :
    (poleFilterPolynomial E).eval v = ∏ w ∈ E, (1 - w⁻¹ * v) := by
  simp only [poleFilterPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

@[simp] theorem poleFilterPolynomial_eval_zero (E : Finset ℂ) :
    (poleFilterPolynomial E).eval 0 = 1 := by simp

@[simp] theorem poleFilterPolynomial_coeff_zero (E : Finset ℂ) :
    (poleFilterPolynomial E).coeff 0 = 1 := by
  exact (Polynomial.coeff_zero_eq_eval_zero (poleFilterPolynomial E)).trans
    (poleFilterPolynomial_eval_zero E)

theorem poleFilterPolynomial_vanishes {E : Finset ℂ} {v : ℂ}
    (hv : v ∈ E) (hv0 : v ≠ 0) : (poleFilterPolynomial E).eval v = 0 := by
  rw [poleFilterPolynomial_eval]
  apply Finset.prod_eq_zero hv
  simp [hv0]

theorem poleFilterPolynomial_preserves_target {E : Finset ℂ} {v : ℂ}
    (hv : v ∉ E) (hE : ∀ w ∈ E, w ≠ 0) :
    (poleFilterPolynomial E).eval v ≠ 0 := by
  rw [poleFilterPolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro w hw
  have hw0 := hE w hw
  intro h
  have he : w⁻¹ * v = 1 := (sub_eq_zero.mp h).symm
  have hev : v = w := by
    calc
      v = w * (w⁻¹ * v) := by simp [hw0]
      _ = w := by rw [he]; ring
  exact hv (hev.symm ▸ hw)

theorem poleFilterPolynomial_nonzero (E : Finset ℂ) : poleFilterPolynomial E ≠ 0 := by
  intro h
  have hc := poleFilterPolynomial_coeff_zero E
  rw [h] at hc
  norm_num at hc

/-- The normalization automatically supplies the filter-mass lower bound. -/
theorem poleFilterPolynomial_mass_one_le (E : Finset ℂ) :
    1 ≤ filterMass (poleFilterPolynomial E).natDegree (poleFilterPolynomial E).coeff :=
  filterMass_one_le (poleFilterPolynomial_coeff_zero E)

end Merger02
