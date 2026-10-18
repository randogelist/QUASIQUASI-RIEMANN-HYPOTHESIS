import AWPIRH.ThetaEntire
import RiemannHypothesis.Xi.CanonicalProductPairedGrowth
import AngularMaster.CanonicalProduct
import AngularMaster.IndexedProduct
import AngularMaster.ProductSummability
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
The actual xi factorization supplies the forward implication RH -> Master.

The imported theorem factors the literal Mathlib-backed xi pullback as a
nonzero constant times its multiplicity-bearing canonical product. Exact
negation pairing gives quadratic factors. Under RH their locations are real,
so rotating and descending through the square map gives positive scales.

Taking squared moduli along a circle absorbs the possible origin monomial
into the nonnegative radial coefficient. No assertion of RH, no asserted
factorization input, and no hypothesis on angular derivatives is introduced.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AngularMaster
open OverflowResidueRH

theorem external_entireRiemannXi_eq_actual_xi (s : ℂ) :
    OverflowResidueRH.entireRiemannXi s = AWPIRH.xi s := by
  unfold OverflowResidueRH.entireRiemannXi AWPIRH.xi
  ring

theorem actual_theta_eq_external_pullback (z : ℂ) :
    AWPIRH.theta z =
      OverflowResidueRH.EntireXiPullback (-Complex.I * Complex.sqrt z) := by
  rw [OverflowResidueRH.EntireXiPullback, external_entireRiemannXi_eq_actual_xi]
  unfold AWPIRH.theta AWPIRH.centeredXi
  congr 1
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc
    (1 / 2 : ℂ) + Complex.sqrt z = (1 / 2 : ℂ) + (-1) * (-Complex.sqrt z) := by ring
    _ = (1 / 2 : ℂ) + Complex.I * (-Complex.I * Complex.sqrt z) := by
      rw [← hI]
      ring

theorem external_pullback_eq_actual_theta (w : ℂ) :
    OverflowResidueRH.EntireXiPullback w = AWPIRH.theta (-(w ^ 2)) := by
  have hsq : (Complex.I * w) ^ 2 = -(w ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [← hsq, AWPIRH.theta_square]
  exact external_entireRiemannXi_eq_actual_xi _

theorem transformed_quadratic_factor (z rho : ℂ) :
    1 - ((-Complex.I * Complex.sqrt z) / rho) ^ 2 = 1 + z / rho ^ 2 := by
  rw [div_pow, mul_pow, neg_sq, Complex.I_sq, AWPIRH.complex_sqrt_sq]
  ring

theorem transformed_root_norm_sq (z : ℂ) :
    ‖-Complex.I * Complex.sqrt z‖ ^ 2 = ‖z‖ := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, ← norm_pow,
    AWPIRH.complex_sqrt_sq]


abbrev ActualPairIndex := entireXiPullbackZeroOccurrenceNegationPairingData.half

def actualPairZero (i : ActualPairIndex) : ℂ :=
  entireXiPullbackZeroOccurrenceNegationPairingData.repLoc i

def actualZeroScale (i : ActualPairIndex) : ℝ := ‖actualPairZero i‖ ^ 2

theorem actualPairZero_ne_zero (i : ActualPairIndex) : actualPairZero i ≠ 0 :=
  entireXiPullbackZeroOccurrenceLoc_ne_zero _

theorem actualZeroScale_positive (i : ActualPairIndex) : 0 < actualZeroScale i :=
  sq_pos_of_pos (norm_pos_iff.mpr (actualPairZero_ne_zero i))

theorem actualZeroScale_inv_summable :
    Summable (fun i : ActualPairIndex => (actualZeroScale i)⁻¹) := by
  let P := entireXiPullbackZeroOccurrenceNegationPairingData
  let e : ActualPairIndex → EntireXiPullbackZeroOccurrence :=
    fun i => P.pairEquiv (i, false)
  have he : Function.Injective e := by
    intro i j hij
    exact congrArg Prod.fst (P.pairEquiv.injective hij)
  exact entireXiPullbackCanonicalZeroDistributionFromTheta.inv_sq_summable.comp_injective he

theorem actualPairZero_sq_of_RH (hRH : RiemannHypothesis) (i : ActualPairIndex) :
    (actualPairZero i) ^ 2 = (actualZeroScale i : ℂ) := by
  have him : (actualPairZero i).im = 0 :=
    riemannHypothesis_iff_entireXiPullback_zeros_real.mp hRH _
      (entireXiPullbackZeroOccurrenceLoc_is_zero _)
  have hre : actualPairZero i = ((actualPairZero i).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  unfold actualZeroScale
  rw [hre, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_cast

theorem actual_theta_paired_factorization (hRH : RiemannHypothesis) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      AWPIRH.theta z = C * (-Complex.I * Complex.sqrt z) ^
        entireXiPullbackOriginMultiplicity *
        ∏' i : ActualPairIndex, (1 + z / (actualZeroScale i : ℂ)) := by
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
  change 1 - ((-Complex.I * Complex.sqrt z) / actualPairZero i)^2 = _
  rw [transformed_quadratic_factor, actualPairZero_sq_of_RH hRH]

theorem actual_canonicalProduct_multipliable (z : ℂ) :
    Multipliable (fun i : ActualPairIndex => 1 + z / (actualZeroScale i : ℂ)) := by
  apply multipliable_one_add_of_summable
  have h := actualZeroScale_inv_summable.mul_left ‖z‖
  exact h.congr (fun i => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (actualZeroScale_positive i), div_eq_mul_inv])

theorem circlePoint_norm (r x : ℝ) (hr : 0 ≤ r) (hx : x ∈ angularInterval) :
    ‖circlePoint r x‖ = r := by
  apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, circlePoint_re, circlePoint_im]
  have hs : (Real.sqrt (1-x^2))^2 = 1-x^2 := by
    apply Real.sq_sqrt
    rcases hx with ⟨hlo,hhi⟩
    nlinarith
  nlinarith

theorem actual_origin_factor_normSq (C : ℂ) (r x : ℝ)
    (hr : 0 ≤ r) (hx : x ∈ angularInterval) :
    Complex.normSq (C * (-Complex.I * Complex.sqrt (circlePoint r x)) ^
      entireXiPullbackOriginMultiplicity) =
      Complex.normSq C * r ^ entireXiPullbackOriginMultiplicity := by
  rw [map_mul, map_pow]
  congr 1
  rw [Complex.normSq_eq_norm_sq, transformed_root_norm_sq, circlePoint_norm r x hr hx]

theorem actualProfile_indexed_product_values (hRH : RiemannHypothesis) :
    ∃ c : ℝ → ℝ, (∀ r, 0 < r → 0 ≤ c r) ∧
      ∀ r, 0 < r → ∀ x ∈ angularInterval,
        Tendsto (fun s : Finset ActualPairIndex =>
          c r * indexedFiniteProductProfile actualZeroScale r s x)
          atTop (𝓝 (actualProfile r x)) := by
  obtain ⟨C, hC, hfactor⟩ := actual_theta_paired_factorization hRH
  let c : ℝ → ℝ := fun r => Complex.normSq C * r ^ entireXiPullbackOriginMultiplicity
  refine ⟨c, ?_, ?_⟩
  · intro r hr
    exact mul_nonneg (Complex.normSq_nonneg C) (pow_nonneg hr.le _)
  · intro r hr x hx
    let z := circlePoint r x
    let k := C * (-Complex.I * Complex.sqrt z)^entireXiPullbackOriginMultiplicity
    have hprod : Tendsto (fun s : Finset ActualPairIndex =>
        ∏ i ∈ s, (1 + z / (actualZeroScale i : ℂ))) atTop
        (𝓝 (∏' i : ActualPairIndex, (1 + z / (actualZeroScale i : ℂ)))) :=
      (actual_canonicalProduct_multipliable z).hasProd
    have ht := Complex.continuous_normSq.continuousAt.tendsto.comp
      (hprod.const_mul k)
    have heq : k * (∏' i : ActualPairIndex, (1 + z / (actualZeroScale i : ℂ))) =
        AWPIRH.theta z := (hfactor z).symm
    rw [heq] at ht
    convert ht using 1
    · ext s
      simp only [Function.comp_apply]
      rw [map_mul, map_prod]
      rw [show Complex.normSq k = c r from actual_origin_factor_normSq C r x hr.le hx]
      congr 1
      exact Finset.prod_congr rfl (fun i _ =>
        (normSq_canonicalFactor_circlePoint (actualZeroScale i) r x hx).symm)
    · rfl

theorem actual_profileMaster_of_native_RH (hRH : RiemannHypothesis) :
    ProfileMaster actualProfile := by
  obtain ⟨c, hc, hp⟩ := actualProfile_indexed_product_values hRH
  exact profileMaster_of_summable_indexedProductValues actualZeroScale_positive
    (by simpa only [one_div] using actualZeroScale_inv_summable) hc hp

end AngularMaster
