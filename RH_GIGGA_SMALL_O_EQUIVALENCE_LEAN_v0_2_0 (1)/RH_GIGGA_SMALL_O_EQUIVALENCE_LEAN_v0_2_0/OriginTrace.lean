import AngularMaster.ComplexScaleProduct
import AngularMaster.ZeroFreeSeed
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# The first scalar trace of actual theta

The origin logarithmic derivative is the absolutely convergent sum of the
reciprocals of the literal squared zero scales.  All analytic inputs are
the unconditional actual-xi product and the existing low-height zero-free
theorem.  In particular no zero-location assertion is assumed here.
-/

noncomputable section
open Filter Metric Set
open scoped Topology BigOperators

namespace AngularMaster
open OverflowResidueRH

/-- A reciprocal-summable affine product converges locally uniformly near
the origin. -/
theorem affineProduct_hasProdLocallyUniformlyOn_origin
    {ι : Type*} {b : ι → ℂ} (hb : Summable (fun i => ‖b i‖)) :
    HasProdLocallyUniformlyOn (fun i (z : ℂ) => 1 + z * b i)
      (fun z => ∏' i, (1 + z * b i)) (ball 0 1) := by
  apply hb.hasProdLocallyUniformlyOn_one_add isOpen_ball
  · exact Eventually.of_forall (fun i z hz => by
      rw [norm_mul]
      have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hz' (norm_nonneg (b i)))
  · intro i
    fun_prop

/-- The logarithmic derivative of an affine infinite product at its center
is the sum of its coefficients. -/
theorem logDeriv_affineProduct_zero
    {ι : Type*} {b : ι → ℂ} (hb : Summable (fun i => ‖b i‖)) :
    logDeriv (fun z : ℂ => ∏' i, (1 + z * b i)) 0 = ∑' i, b i := by
  have hfactor (i : ι) :
      logDeriv (fun z : ℂ => 1 + z * b i) 0 = b i := by
    have hd : HasDerivAt (fun z : ℂ => 1 + z * b i) (b i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (b i)).const_add 1
    rw [logDeriv_apply, hd.deriv]
    simp
  have hprod := affineProduct_hasProdLocallyUniformlyOn_origin hb
  have hsum : Summable (fun i => logDeriv (fun z : ℂ => 1 + z * b i) 0) := by
    simpa only [hfactor] using hb.of_norm
  have h := logDeriv_tprod_eq_tsum
    (f := fun i (z : ℂ) => 1 + z * b i) isOpen_ball
    (by simp : (0 : ℂ) ∈ ball 0 1)
    (fun i => by simp)
    (fun i => by fun_prop) hsum hprod.multipliableLocallyUniformlyOn
    (by simp : (∏' i : ι, (1 + (0 : ℂ) * b i)) ≠ 0)
  simpa only [hfactor] using h

/-- The actual theta does not vanish at its center, by the established
low-height zero-free estimate. -/
theorem actual_theta_zero_ne_zero : AWPIRH.theta 0 ≠ 0 := by
  change AWPIRH.xi ((1 / 2 : ℂ) + Complex.sqrt 0) ≠ 0
  simp only [Complex.sqrt_zero, add_zero]
  apply actual_xi_ne_zero_of_low_height <;> norm_num

/-- Consequently the origin monomial in the unconditional xi product is
absent. -/
theorem actual_originMultiplicity_eq_zero :
    entireXiPullbackOriginMultiplicity = 0 := by
  by_contra hm
  have hz := entireXiPullbackOriginMultiplicity_ne_zero_iff.mp hm
  have htheta : AWPIRH.theta 0 = 0 := by
    simpa using (external_pullback_eq_actual_theta (0 : ℂ)).symm.trans hz
  exact actual_theta_zero_ne_zero htheta

/-- Normalize the established unconditional product at zero. -/
theorem actual_theta_normalized_complex_factorization (z : ℂ) :
    AWPIRH.theta z = AWPIRH.theta 0 *
      ∏' i : ActualPairIndex, (1 + z / actualComplexScale i) := by
  obtain ⟨C, hC, hfactor⟩ := actual_theta_complex_factorization
  have hfactor' (w : ℂ) : AWPIRH.theta w = C *
      ∏' i : ActualPairIndex, (1 + w / actualComplexScale i) := by
    simpa only [actual_originMultiplicity_eq_zero, pow_zero, mul_one] using hfactor w
  have hzero : AWPIRH.theta 0 = C := by
    simpa using hfactor' 0
  rw [hzero]
  exact hfactor' z

/-- Exact complex scalar spectral trace at the origin. -/
theorem actual_theta_origin_logDeriv_eq_tsum :
    deriv AWPIRH.theta 0 / AWPIRH.theta 0 =
      ∑' i : ActualPairIndex, (actualComplexScale i)⁻¹ := by
  have hfun : AWPIRH.theta = fun z : ℂ => AWPIRH.theta 0 *
      ∏' i : ActualPairIndex, (1 + z * (actualComplexScale i)⁻¹) := by
    funext z
    simpa only [div_eq_mul_inv] using actual_theta_normalized_complex_factorization z
  change logDeriv AWPIRH.theta 0 = _
  rw [hfun, logDeriv_const_mul _ _ actual_theta_zero_ne_zero]
  exact logDeriv_affineProduct_zero actualComplexScale_norm_inv_summable

/-- Real reciprocal weights form an absolutely summable scalar trace. -/
theorem actualComplexScale_inv_re_summable :
    Summable (fun i : ActualPairIndex => ((actualComplexScale i)⁻¹).re) := by
  exact Complex.reCLM.summable actualComplexScale_norm_inv_summable.of_norm

/-- The real first Taylor quotient equals the scalar sum used by the
critical-line cutoff criterion. -/
theorem actual_theta_origin_real_trace :
    (deriv AWPIRH.theta 0 / AWPIRH.theta 0).re =
      ∑' i : ActualPairIndex, ((actualComplexScale i)⁻¹).re := by
  rw [actual_theta_origin_logDeriv_eq_tsum]
  exact Complex.re_tsum actualComplexScale_norm_inv_summable.of_norm

end AngularMaster
