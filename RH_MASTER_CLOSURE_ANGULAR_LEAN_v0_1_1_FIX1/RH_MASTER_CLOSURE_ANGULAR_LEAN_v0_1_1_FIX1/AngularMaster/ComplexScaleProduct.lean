import AngularMaster.ActualHadamard

/-!
# The unconditional actual-theta product with complex zero scales

The opposite-zero pairing is valid without RH. Its squared scales must remain
complex unless a separate theorem locates the zeros. This module retains those
literal complex scales and proves their product convergence and Schwarz symmetry.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ComplexConjugate

namespace AngularMaster
open OverflowResidueRH

/-- The literal squared zero location in the opposite-pair divisor. -/
def actualComplexScale (i : ActualPairIndex) : ℂ := (actualPairZero i) ^ 2

theorem actualComplexScale_ne_zero (i : ActualPairIndex) :
    actualComplexScale i ≠ 0 :=
  pow_ne_zero 2 (actualPairZero_ne_zero i)

theorem norm_actualComplexScale (i : ActualPairIndex) :
    ‖actualComplexScale i‖ = actualZeroScale i := by
  simp only [actualComplexScale, actualZeroScale, norm_pow]

theorem actualComplexScale_inv_norm_summable :
    Summable (fun i : ActualPairIndex => ‖actualComplexScale i‖⁻¹) := by
  simpa only [norm_actualComplexScale] using actualZeroScale_inv_summable

theorem actualComplexScale_norm_inv_summable :
    Summable (fun i : ActualPairIndex => ‖(actualComplexScale i)⁻¹‖) := by
  simpa only [norm_inv] using actualComplexScale_inv_norm_summable

theorem actual_complexScaleProduct_multipliable (z : ℂ) :
    Multipliable (fun i : ActualPairIndex => 1 + z / actualComplexScale i) := by
  apply multipliable_one_add_of_summable
  have h := actualComplexScale_inv_norm_summable.mul_left ‖z‖
  exact h.congr (fun i => by rw [norm_div, div_eq_mul_inv])

/-- The actual entire theta factors with complex scales, with no RH input. -/
theorem actual_theta_complex_factorization :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      AWPIRH.theta z = C * (-Complex.I * Complex.sqrt z) ^
        entireXiPullbackOriginMultiplicity *
        ∏' i : ActualPairIndex, (1 + z / actualComplexScale i) := by
  obtain ⟨C, hC, hfactor⟩ := entireXiPullback_exists_constant_factorization_unconditional
  refine ⟨C, hC, ?_⟩
  intro z
  rw [actual_theta_eq_external_pullback, hfactor,
    entireXiPullbackCanonicalProduct, Pi.mul_apply,
    entireXiPullbackInfiniteHadamardProduct_eq_pairedQuadraticProduct, ← mul_assoc]
  congr 1
  unfold pairedQuadraticProduct
  apply tprod_congr
  intro i
  change 1 - ((-Complex.I * Complex.sqrt z) / actualPairZero i) ^ 2 =
    1 + z / actualComplexScale i
  exact transformed_quadratic_factor z (actualPairZero i)

/-- Every complex scale is an actual theta zero after negation. -/
theorem actual_theta_neg_complexScale_zero (i : ActualPairIndex) :
    AWPIRH.theta (-actualComplexScale i) = 0 := by
  unfold actualComplexScale
  rw [← external_pullback_eq_actual_theta]
  exact entireXiPullbackZeroOccurrenceLoc_is_zero _

/-- Actual xi Schwarz reflection, transported from the unconditional source. -/
theorem actual_xi_conj (s : ℂ) :
    AWPIRH.xi (conj s) = conj (AWPIRH.xi s) := by
  have h := EntireXi.schwarzReflection_holds s
  simpa only [Complex.star_def, external_entireRiemannXi_eq_actual_xi] using h

/-- Entire theta inherits Schwarz reflection through its even square descent. -/
theorem actual_theta_conj (z : ℂ) :
    AWPIRH.theta (conj z) = conj (AWPIRH.theta z) := by
  have hsq : (conj (Complex.sqrt z)) ^ 2 = conj z := by
    rw [← map_pow, AWPIRH.complex_sqrt_sq]
  rw [← hsq, AWPIRH.theta_square]
  change AWPIRH.xi ((1 / 2 : ℂ) + conj (Complex.sqrt z)) =
    conj (AWPIRH.xi ((1 / 2 : ℂ) + Complex.sqrt z))
  have h := actual_xi_conj ((1 / 2 : ℂ) + Complex.sqrt z)
  have htwo : conj (2 : ℂ) = 2 := Complex.conj_ofNat 2
  simpa [htwo] using h

theorem actual_theta_norm_conj (z : ℂ) :
    ‖AWPIRH.theta (conj z)‖ = ‖AWPIRH.theta z‖ := by
  rw [actual_theta_conj, Complex.norm_conj]

theorem actual_theta_normSq_conj (z : ℂ) :
    Complex.normSq (AWPIRH.theta (conj z)) = Complex.normSq (AWPIRH.theta z) := by
  rw [actual_theta_conj, Complex.normSq_conj]

end AngularMaster
