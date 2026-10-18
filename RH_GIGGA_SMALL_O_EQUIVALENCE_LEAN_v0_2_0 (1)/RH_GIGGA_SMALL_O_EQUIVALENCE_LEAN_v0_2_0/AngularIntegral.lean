import AngularMaster.ZeroFreeSeed
import AngularMaster.ActualProfile
import AngularRegularity.Derivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The literal angular integral and its unconditional first-order limit at zero.
All divisions use Lean's total-field convention.  Endpoint values are irrelevant
to the interval integral, and differentiation is used only on the open interval.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace AngularMaster

private theorem angular_theta_zero_ne_zero : AWPIRH.theta 0 ≠ 0 := by
  change AWPIRH.xi ((1 / 2 : ℂ) + Complex.sqrt 0) ≠ 0
  simp only [Complex.sqrt_zero, add_zero]
  apply actual_xi_ne_zero_of_low_height <;> norm_num

def angularI (r : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    (deriv (actualProfile r) x / actualProfile r x) * Real.sqrt (1 - x ^ 2)

def actualLogDerivative (z : ℂ) : ℂ :=
  deriv AWPIRH.theta z / AWPIRH.theta z

/-- The square-root endpoint singularity has cancelled in this integrand. -/
def angularRegularIntegrand (r x : ℝ) : ℝ :=
  2 * (circlePoint 1 x * actualLogDerivative (circlePoint r x)).im

def angularJ (r : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, angularRegularIntegrand r x

theorem actualLogDerivative_continuousAt_zero :
    ContinuousAt actualLogDerivative (0 : ℂ) :=
  AWPIRH.theta_differentiable.deriv.continuous.continuousAt.div
    AWPIRH.theta_continuous.continuousAt angular_theta_zero_ne_zero

theorem norm_circlePoint_eq_abs {r x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖circlePoint r x‖ = |r| := by
  have h := AngularRegularity.normSq_circlePoint (r := r) hx
  change Complex.normSq (circlePoint r x) = r ^ 2 at h
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (circlePoint r x), abs_nonneg r, sq_abs r]

theorem actualProfile_deriv_eq_slope {r x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv (actualProfile r) x =
      AngularRegularity.slopeFormula AWPIRH.theta r x := by
  exact (AngularRegularity.hasDerivAt_profile
    (AWPIRH.theta_differentiable (circlePoint r x)) hx).deriv

theorem angular_weighted_integrand_eq {r x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (deriv (actualProfile r) x / actualProfile r x) * Real.sqrt (1 - x ^ 2) =
      r * angularRegularIntegrand r x := by
  rw [actualProfile_deriv_eq_slope hx]
  by_cases hz : AWPIRH.theta (circlePoint r x) = 0
  · simp [actualProfile, angularNormSq, AngularRegularity.slopeFormula,
      AngularRegularity.circlePoint, circlePoint, actualLogDerivative,
      angularRegularIntegrand] at hz ⊢
    simp [hz]
  · have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 :=
      ne_of_gt (AngularRegularity.sqrt_one_sub_sq_pos hx)
    have hpne : Complex.normSq (AWPIRH.theta (circlePoint r x)) ≠ 0 :=
      mt Complex.normSq_eq_zero.mp hz
    simp only [actualProfile, angularNormSq, AngularRegularity.slopeFormula,
      angularRegularIntegrand, actualLogDerivative, AngularRegularity.circlePoint,
      circlePoint, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.div_re, Complex.div_im]
    field_simp [hsne, hpne]
    <;> ring

/-- This identity is global in the radius and does not assert integrability
at a zero; it uses the literal total-valued interval integral. -/
theorem angularI_eq_mul_angularJ (r : ℝ) : angularI r = r * angularJ r := by
  unfold angularI angularJ
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    (fun x hx => angular_weighted_integrand_eq hx)

theorem angularRegularIntegrand_continuousOn {r : ℝ}
    (hr : ∀ x ∈ Icc (-1 : ℝ) 1, AWPIRH.theta (circlePoint r x) ≠ 0) :
    ContinuousOn (angularRegularIntegrand r) (Icc (-1 : ℝ) 1) := by
  have hq : ContinuousOn (fun x => actualLogDerivative (circlePoint r x))
      (Icc (-1 : ℝ) 1) := by
    apply ContinuousOn.div
      ((AWPIRH.theta_differentiable.deriv.continuous.comp
        (continuous_circlePoint r)).continuousOn)
      ((AWPIRH.theta_continuous.comp (continuous_circlePoint r)).continuousOn)
    exact hr
  exact (Complex.continuous_im.comp_continuousOn
    ((continuous_circlePoint 1).continuousOn.mul hq)).const_mul 2

theorem angularRegularIntegrand_bound {r x M : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1)
    (hM : ‖actualLogDerivative (circlePoint r x)‖ ≤ M) :
    ‖angularRegularIntegrand r x‖ ≤ 2 * M := by
  rw [angularRegularIntegrand, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |(circlePoint 1 x * actualLogDerivative (circlePoint r x)).im|
        ≤ 2 * ‖circlePoint 1 x * actualLogDerivative (circlePoint r x)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)
    _ = 2 * ‖actualLogDerivative (circlePoint r x)‖ := by
      rw [norm_mul, norm_circlePoint_eq_abs hx]
      norm_num
    _ ≤ 2 * M := mul_le_mul_of_nonneg_left hM (by norm_num)

theorem angularRegularIntegrand_eventually_regular :
    ∀ᶠ r : ℝ in 𝓝 0,
      (∀ x ∈ Icc (-1 : ℝ) 1, AWPIRH.theta (circlePoint r x) ≠ 0) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1,
        ‖angularRegularIntegrand r x‖ ≤ 2 * (‖actualLogDerivative 0‖ + 1)) := by
  have hn := AWPIRH.theta_continuous.continuousAt.eventually_ne angular_theta_zero_ne_zero
  have hb : ∀ᶠ z : ℂ in 𝓝 0,
      ‖actualLogDerivative z‖ ≤ ‖actualLogDerivative 0‖ + 1 :=
    actualLogDerivative_continuousAt_zero.norm.tendsto.eventually_le_const (by linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hn.and hb)
  have hrball : ∀ᶠ r : ℝ in 𝓝 0, |r| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with r hr
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hr
  filter_upwards [hrball] with r hr
  have hpoint (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      AWPIRH.theta (circlePoint r x) ≠ 0 ∧
        ‖actualLogDerivative (circlePoint r x)‖ ≤ ‖actualLogDerivative 0‖ + 1 := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_circlePoint_eq_abs hx]
    exact hr
  exact ⟨fun x hx => (hpoint x hx).1,
    fun x hx => angularRegularIntegrand_bound hx (hpoint x hx).2⟩

theorem angularRegularIntegrand_continuousAt_radius_zero (x : ℝ) :
    ContinuousAt (fun r => angularRegularIntegrand r x) 0 := by
  have hc : Continuous (fun r : ℝ => circlePoint r x) := by
    unfold circlePoint
    fun_prop
  have hq : ContinuousAt (fun r : ℝ => actualLogDerivative (circlePoint r x)) 0 := by
    have hq0 : ContinuousAt actualLogDerivative (circlePoint 0 x) := by
      simpa [circlePoint] using actualLogDerivative_continuousAt_zero
    exact ContinuousAt.comp' (f := fun r : ℝ => circlePoint r x) (x := 0)
      hq0 hc.continuousAt
  have hm : ContinuousAt
      (fun r : ℝ => circlePoint 1 x * actualLogDerivative (circlePoint r x)) 0 :=
    continuousAt_const.mul hq
  exact (Complex.continuous_im.continuousAt.comp hm).const_mul 2

theorem angularJ_continuousAt_zero : ContinuousAt angularJ 0 := by
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ : ℝ => 2 * (‖actualLogDerivative 0‖ + 1))
  · filter_upwards [angularRegularIntegrand_eventually_regular] with r hr
    have hc := angularRegularIntegrand_continuousOn hr.1
    apply (hc.mono ?_).aestronglyMeasurable measurableSet_uIoc
    rw [uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
    exact Ioc_subset_Icc_self
  · filter_upwards [angularRegularIntegrand_eventually_regular] with r hr
    exact ae_of_all _ (fun x hx => hr.2 x (by
      rw [uIoc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] at hx
      exact ⟨hx.1.le, hx.2⟩))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun x _ => angularRegularIntegrand_continuousAt_radius_zero x)

theorem angularJ_zero :
    angularJ 0 = Real.pi * (deriv AWPIRH.theta 0 / AWPIRH.theta 0).re := by
  have hf (x : ℝ) : angularRegularIntegrand 0 x =
      (2 * (actualLogDerivative 0).re) * Real.sqrt (1 - x ^ 2) +
        (2 * (actualLogDerivative 0).im) * x := by
    simp [angularRegularIntegrand, circlePoint, Complex.mul_im]
    ring
  unfold angularJ
  simp_rw [hf]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_sqrt_one_sub_sq, integral_id]
    norm_num
    simp only [actualLogDerivative]
    ring
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      (2 * (actualLogDerivative 0).re) * Real.sqrt (1 - x ^ 2))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun x : ℝ =>
      (2 * (actualLogDerivative 0).im) * x)).intervalIntegrable _ _

theorem angularI_div_radius_tendsto :
    Tendsto (fun r : ℝ => angularI r / r) (𝓝[>] 0)
      (𝓝 (Real.pi * (deriv AWPIRH.theta 0 / AWPIRH.theta 0).re)) := by
  have heq : (fun r : ℝ => angularI r / r) =ᶠ[𝓝[>] 0] angularJ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [angularI_eq_mul_angularJ, mul_div_cancel_left₀ _ (ne_of_gt hr)]
  apply Tendsto.congr' heq.symm
  rw [← angularJ_zero]
  exact angularJ_continuousAt_zero.tendsto.mono_left nhdsWithin_le_nhds

theorem angularI_tendsto_zero : Tendsto angularI (𝓝[>] 0) (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hJ : Tendsto angularJ (𝓝[>] 0) (𝓝 (angularJ 0)) :=
    angularJ_continuousAt_zero.tendsto.mono_left nhdsWithin_le_nhds
  have h := hr.mul hJ
  have heq : (fun r : ℝ => r * angularJ r) =ᶠ[𝓝[>] 0] angularI :=
    Eventually.of_forall (fun r => (angularI_eq_mul_angularJ r).symm)
  simpa only [zero_mul] using h.congr' heq

end AngularMaster
