import AngularMaster.ZeroGeometry
import AngularMaster.ZeroExclusion
import AngularMaster.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv

/-!
The literal squared-modulus angular profile of the actual entire theta.
Only nonnegativity, continuity, and interior differentiability are retained.
-/

set_option autoImplicit false
noncomputable section
namespace AngularMaster

def actualProfile : ℝ → ℝ → ℝ := angularNormSq AWPIRH.theta

theorem actualProfile_nonnegative_all (r x : ℝ) : 0 ≤ actualProfile r x :=
  Complex.normSq_nonneg _

theorem actualProfile_continuous (r : ℝ) : Continuous (actualProfile r) :=
  Complex.continuous_normSq.comp
    (AWPIRH.theta_continuous.comp (continuous_circlePoint r))

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

end AngularMaster
