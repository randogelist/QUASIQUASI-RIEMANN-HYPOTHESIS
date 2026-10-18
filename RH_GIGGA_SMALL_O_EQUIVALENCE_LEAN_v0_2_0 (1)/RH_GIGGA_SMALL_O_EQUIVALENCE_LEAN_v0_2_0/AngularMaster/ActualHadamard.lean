import AWPIRH.ThetaEntire
import AngularMaster.ZeroExclusion
import RiemannHypothesis.Xi.CanonicalProductPairedGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Minimal unconditional actual-theta product foundations

This module binds the unconditional classical xi product to the actual entire
`AWPIRH.theta`, retaining complex zero locations. It contains no RH-to-Master
argument, positive-real-scale substitution, or angular derivative-limit layer.
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

theorem actualZeroScale_inv_summable :
    Summable (fun i : ActualPairIndex => (actualZeroScale i)⁻¹) := by
  let P := entireXiPullbackZeroOccurrenceNegationPairingData
  let e : ActualPairIndex → EntireXiPullbackZeroOccurrence :=
    fun i => P.pairEquiv (i, false)
  have he : Function.Injective e := by
    intro i j hij
    exact congrArg Prod.fst (P.pairEquiv.injective hij)
  exact entireXiPullbackCanonicalZeroDistributionFromTheta.inv_sq_summable.comp_injective he

theorem circlePoint_norm (r x : ℝ) (hr : 0 ≤ r) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖circlePoint r x‖ = r := by
  apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, circlePoint_re, circlePoint_im]
  have hs : (Real.sqrt (1-x^2))^2 = 1-x^2 := by
    apply Real.sq_sqrt
    rcases hx with ⟨hlo,hhi⟩
    nlinarith
  nlinarith

end AngularMaster
