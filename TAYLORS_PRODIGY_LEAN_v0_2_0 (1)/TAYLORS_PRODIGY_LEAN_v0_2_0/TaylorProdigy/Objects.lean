import AngularMaster.ActualProfile
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Taylor's Prodigy: the actual objects and the single research premise

`H` is the ordinary real derivative of the actual squared-modulus theta
profile. All derivative regularity below is restricted to the open angular
interval. In particular, this file makes no claim about an ordinary derivative
at either endpoint of the literal square-root profile.

`F` pulls `H` back by `x = cos θ`. The sole research input is the explicitly
named proposition `TAYLORS_PRODIGY_PREMISE`; no instance or proof of it is
declared here. Its coefficient must be integrable across every finite angular
window, including a prospective first zero, and it is not assumed continuous.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace TaylorsProdigy

/-- Actual ordinary angular derivative, used only on the angular interior. -/
def H (r x : ℝ) : ℝ := deriv (AngularMaster.actualProfile r) x

/-- Actual angular derivative in the angle coordinate. -/
def F (r θ : ℝ) : ℝ := H r (Real.cos θ)

theorem sqrtArgument_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  rcases hx with ⟨hx0, hx1⟩
  nlinarith [mul_pos (by linarith : 0 < 1 - x) (by linarith : 0 < 1 + x)]

/-- Smoothness is derived from the actual entire theta function. -/
theorem actualProfile_contDiffAt {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (AngularMaster.actualProfile r) x := by
  have hsqrt : ContDiffAt ℝ ⊤ (fun t : ℝ => Real.sqrt (1 - t ^ 2)) x :=
    (Real.contDiffAt_sqrt (ne_of_gt (sqrtArgument_pos hx))).comp x
      (contDiffAt_const.sub (contDiffAt_id.pow 2))
  have hxC : ContDiffAt ℝ ⊤ (fun t : ℝ => (t : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hsC : ContDiffAt ℝ ⊤
      (fun t : ℝ => (Real.sqrt (1 - t ^ 2) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hsqrt
  have hcircle : ContDiffAt ℝ ⊤ (AngularMaster.circlePoint r) x := by
    unfold AngularMaster.circlePoint
    exact contDiffAt_const.mul (hxC.add (contDiffAt_const.mul hsC))
  have htheta : ContDiff ℝ ⊤ AWPIRH.theta :=
    ContDiff.restrict_scalars ℝ (AWPIRH.theta_differentiable.contDiff :
      ContDiff ℂ ⊤ AWPIRH.theta)
  have hcomp := htheta.contDiffAt.comp x hcircle
  change ContDiffAt ℝ ⊤
    (fun t => Complex.normSq (AWPIRH.theta (AngularMaster.circlePoint r t))) x
  simpa only [Function.comp_apply, Complex.normSq_eq_norm_sq] using
    (ContDiffAt.norm_sq ℂ hcomp)

theorem H_contDiffAt {r x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (H r) x := by
  exact (actualProfile_contDiffAt hx).derivWithin (by simp)

theorem H_continuousAt {r x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (H r) x := (H_contDiffAt hx).continuousAt

theorem H_differentiableAt {r x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (H r) x := (H_contDiffAt hx).differentiableAt (by simp)

theorem H_continuousOn (r : ℝ) : ContinuousOn (H r) (Ioo (-1 : ℝ) 1) := by
  intro x hx
  exact (H_continuousAt hx).continuousWithinAt

theorem H_differentiableOn (r : ℝ) : DifferentiableOn ℝ (H r) (Ioo (-1 : ℝ) 1) := by
  intro x hx
  exact (H_differentiableAt hx).differentiableWithinAt

theorem cos_mem_interior {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    Real.cos θ ∈ Ioo (-1 : ℝ) 1 := Real.mapsTo_cos_Ioo hθ

theorem F_contDiffAt {r θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    ContDiffAt ℝ ⊤ (F r) θ := by
  exact (H_contDiffAt (cos_mem_interior hθ)).comp θ Real.contDiff_cos.contDiffAt

theorem F_continuousAt {r θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    ContinuousAt (F r) θ := (F_contDiffAt hθ).continuousAt

theorem F_differentiableAt {r θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    DifferentiableAt ℝ (F r) θ := (F_contDiffAt hθ).differentiableAt (by simp)

theorem F_continuousOn (r : ℝ) : ContinuousOn (F r) (Ioo (0 : ℝ) Real.pi) := by
  intro θ hθ
  exact (F_continuousAt hθ).continuousWithinAt

theorem F_differentiableOn (r : ℝ) : DifferentiableOn ℝ (F r) (Ioo (0 : ℝ) Real.pi) := by
  intro θ hθ
  exact (F_differentiableAt hθ).differentiableWithinAt

/-- The pullback derivative is the actual angular second derivative times
`-sin θ`; no endpoint derivative is used. -/
theorem deriv_F {r θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    deriv (F r) θ = -Real.sin θ * deriv (H r) (Real.cos θ) := by
  have h := (H_differentiableAt (r := r) (cos_mem_interior hθ)).hasDerivAt.comp θ
    (Real.hasDerivAt_cos θ)
  change deriv (H r ∘ Real.cos) θ = _
  simpa only [mul_comm] using h.deriv

/-- Taylor's Prodigy premise: one-sided relative derivative control of the
actual angle pullback, with a locally interval-integrable nonnegative rate.
This is the sole unproved analytic research premise. -/
def TAYLORS_PRODIGY_PREMISE : Prop :=
  ∀ r : ℝ, 0 < r → ∃ rate : ℝ → ℝ,
    (∀ b : ℝ, 0 < b → b < Real.pi → IntervalIntegrable rate volume 0 b) ∧
    (∀ θ ∈ Ioo (0 : ℝ) Real.pi, 0 ≤ rate θ) ∧
    ∀ θ ∈ Ioo (0 : ℝ) Real.pi,
      0 < F r θ → -rate θ * F r θ ≤ deriv (F r) θ

end TaylorsProdigy
