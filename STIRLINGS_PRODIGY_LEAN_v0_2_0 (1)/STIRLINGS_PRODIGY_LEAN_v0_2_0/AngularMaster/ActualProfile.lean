import AngularMaster.ZeroGeometry
import AngularMaster.ZeroExclusion
import AngularMaster.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv

/-!
The angular profile is the actual squared modulus of Mathlib-backed theta.
Continuity and interior differentiability are proved here, so the implication
from the raw angular Master to native RH needs no endpoint regularity hypothesis.
-/

noncomputable section
namespace AngularMaster

def actualProfile : ℝ → ℝ → ℝ := angularNormSq AWPIRH.theta

theorem actualProfile_nonnegative_all (r x : ℝ) : 0 ≤ actualProfile r x :=
  Complex.normSq_nonneg _

theorem actualProfile_nonnegative : ProfileNonnegative actualProfile := by
  intro r hr x hx
  exact Complex.normSq_nonneg _

theorem actualProfile_continuous (r : ℝ) : Continuous (actualProfile r) :=
  Complex.continuous_normSq.comp
    (AWPIRH.theta_continuous.comp (continuous_circlePoint r))

theorem actualProfile_continuousOn :
    ∀ r : ℝ, 0 < r → ContinuousOn (actualProfile r) angularInterval := by
  intro r hr
  exact (actualProfile_continuous r).continuousOn

theorem actualProfile_interior_differentiable :
    ∀ r : ℝ, 0 < r → DifferentiableOn ℝ (actualProfile r) (Set.Ioo (-1) 1) := by
  intro r hr x hx
  rcases hx with ⟨hx0, hx1⟩
  have hinside : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - x) (by linarith : 0 < 1 + x)]
  have hsqrt : DifferentiableAt ℝ (fun y : ℝ => Real.sqrt (1 - y ^ 2)) x :=
    (differentiableAt_const (1 : ℝ) |>.sub (differentiableAt_id.pow 2)).sqrt
      (ne_of_gt hinside)
  have hcircle : DifferentiableAt ℝ (circlePoint r) x := by
    unfold circlePoint
    fun_prop
  have ht : DifferentiableAt ℝ (fun y => AWPIRH.theta (circlePoint r y)) x :=
    ((AWPIRH.theta_differentiable (circlePoint r x)).restrictScalars ℝ).comp x hcircle
  have hre : DifferentiableAt ℝ (fun y => (AWPIRH.theta (circlePoint r y)).re) x := by
    fun_prop
  have him : DifferentiableAt ℝ (fun y => (AWPIRH.theta (circlePoint r y)).im) x := by
    fun_prop
  change DifferentiableWithinAt ℝ
    (fun y => Complex.normSq (AWPIRH.theta (circlePoint r y))) (Set.Ioo (-1) 1) x
  have hd : DifferentiableAt ℝ
      (fun y => Complex.normSq (AWPIRH.theta (circlePoint r y))) x := by
    simp only [Complex.normSq_apply]
    fun_prop
  exact hd.differentiableWithinAt

/-- An unconditional analytic implication for the actual theta function. -/
theorem theta_zeros_nonpositive_of_actual_angular_monotone
    (hm : ∀ r : ℝ, 0 < r → MonotoneOn (actualProfile r) angularInterval) :
    ThetaZerosNonpositive := by
  exact zeros_nonpositive_of_angular_monotone AWPIRH.theta_entire
    ⟨1, AWPIRH.theta_one_ne_zero⟩ (fun z hz => theta_zero_conj hz) hm

theorem native_RH_of_actual_angular_monotone
    (hm : ∀ r : ℝ, 0 < r → MonotoneOn (actualProfile r) angularInterval) :
    _root_.RiemannHypothesis :=
  native_RH_iff_theta_zeros_nonpositive.mpr
    (theta_zeros_nonpositive_of_actual_angular_monotone hm)

/-- Actual derivative nonnegativity implies RH; no product-limit assumption. -/
theorem native_RH_of_actual_derivative_nonnegative
    (h : DerivativeNonnegative actualProfile) : _root_.RiemannHypothesis := by
  apply native_RH_of_actual_angular_monotone
  exact profile_monotone_of_derivativeNonnegative_interior
    actualProfile_continuousOn actualProfile_interior_differentiable h

/-- Both actual Master inequalities imply native RH without a new analytic hypothesis. -/
theorem actual_profileMaster_implies_native_RH
    (h : ProfileMaster actualProfile) : _root_.RiemannHypothesis :=
  native_RH_of_actual_derivative_nonnegative (derivativeNonnegative_of_profileMaster h)

/-- The normalized Master implies RH with only a positive normalizer.
No differentiability at angular endpoints is an input to this implication. -/
theorem actual_logMaster_implies_native_RH
    {ε : ℝ} {S : ℝ → ℝ} (hε : 0 < ε) (hS : NormalizerPositive S)
    (h : LogMaster ε S actualProfile) : _root_.RiemannHypothesis := by
  apply native_RH_of_actual_angular_monotone
  exact profile_monotone_of_logMaster_interior hε hS actualProfile_nonnegative
    actualProfile_continuousOn actualProfile_interior_differentiable h

end AngularMaster
