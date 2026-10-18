import AWPIRH.ThetaEntire
import AWPIRH.ProductGeometry

/-!
Entire analyticity of the literal symmetricProduct from the passing baseline.

Outside r=0 and r=1 we use a normalized local square root of the discriminant.
The two possible signs merely exchange the factors. At the two coalescence
points continuity follows from continuity of sqrt at zero; the remaining
isolated singularities are removable. The product definition is not changed.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

def rootDiscriminant (r : ℂ) : ℂ := (1 - 2 * r) ^ 2 - 1

theorem rootDiscriminant_factor (r : ℂ) :
    rootDiscriminant r = 4 * r * (r - 1) := by
  unfold rootDiscriminant
  ring

theorem rootDiscriminant_ne_zero {r : ℂ} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    rootDiscriminant r ≠ 0 := by
  rw [rootDiscriminant_factor]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hr0) (sub_ne_zero.mpr hr1)

theorem rootDiscriminant_differentiable : Differentiable ℂ rootDiscriminant := by
  unfold rootDiscriminant
  fun_prop

/-- Any square root gives the same unordered product. No branch is fixed here. -/
theorem symmetricProduct_eq_of_root_square (r u : ℂ)
    (hu : u ^ 2 = rootDiscriminant r) :
    symmetricProduct r =
      theta (1 - 2 * r + u) * theta (1 - 2 * r - u) / (theta 1) ^ 2 := by
  have hsq : (Complex.sqrt (rootDiscriminant r)) ^ 2 = u ^ 2 := by
    rw [complex_sqrt_sq, hu]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · change theta (1 - 2 * r + Complex.sqrt (rootDiscriminant r)) *
      theta (1 - 2 * r - Complex.sqrt (rootDiscriminant r)) / (theta 1) ^ 2 = _
    rw [h]
  · change theta (1 - 2 * r + Complex.sqrt (rootDiscriminant r)) *
      theta (1 - 2 * r - Complex.sqrt (rootDiscriminant r)) / (theta 1) ^ 2 = _
    rw [h]
    simp only [sub_eq_add_neg, neg_neg]
    rw [mul_comm]

/-- Differentiability off the two coalescence points, including on a branch cut. -/
theorem symmetricProduct_differentiableAt_of_ne {r : ℂ}
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    DifferentiableAt ℂ symmetricProduct r := by
  have hdisc := rootDiscriminant_ne_zero hr0 hr1
  let u : ℂ → ℂ := fun w => normalizedSqrt (rootDiscriminant r) (rootDiscriminant w)
  have hu : DifferentiableAt ℂ u r :=
    (normalizedSqrt_differentiableAt hdisc).comp r
      (rootDiscriminant_differentiable r)
  have hb : DifferentiableAt ℂ (fun w : ℂ => 1 - 2 * w) r := by fun_prop
  have hplus : DifferentiableAt ℂ (fun w : ℂ => theta (1 - 2 * w + u w)) r := by
    exact DifferentiableAt.fun_comp'
      (f := fun w : ℂ => 1 - 2 * w + u w) (g := theta) r
      (theta_differentiable (1 - 2 * r + u r)) (hb.add hu)
  have hminus : DifferentiableAt ℂ (fun w : ℂ => theta (1 - 2 * w - u w)) r := by
    exact DifferentiableAt.fun_comp'
      (f := fun w : ℂ => 1 - 2 * w - u w) (g := theta) r
      (theta_differentiable (1 - 2 * r - u r)) (hb.sub hu)
  have heq : symmetricProduct = fun w : ℂ =>
      theta (1 - 2 * w + u w) * theta (1 - 2 * w - u w) / (theta 1) ^ 2 := by
    funext w
    apply symmetricProduct_eq_of_root_square
    exact normalizedSqrt_sq hdisc (rootDiscriminant w)
  rw [heq]
  exact (hplus.mul hminus).div_const ((theta 1) ^ 2)

/-- At coalescence, both literal roots are continuous. No derivative of sqrt at 0. -/
theorem symmetricProduct_continuousAt_of_discriminant_zero {r : ℂ}
    (hr : rootDiscriminant r = 0) : ContinuousAt symmetricProduct r := by
  have hd : ContinuousAt rootDiscriminant r :=
    (rootDiscriminant_differentiable r).continuousAt
  have hsqrt : ContinuousAt Complex.sqrt (rootDiscriminant r) := by
    rw [hr]
    exact sqrt_continuousAt_zero
  have hs : ContinuousAt (fun w : ℂ => Complex.sqrt (rootDiscriminant w)) r :=
    hsqrt.comp hd
  have hb : ContinuousAt (fun w : ℂ => 1 - 2 * w) r := by fun_prop
  have hp : ContinuousAt rootPlus r := hb.add hs
  have hm : ContinuousAt rootMinus r := hb.sub hs
  change ContinuousAt
    (fun w : ℂ => theta (rootPlus w) * theta (rootMinus w) / (theta 1) ^ 2) r
  exact ((theta_continuous.continuousAt.comp hp).mul
    (theta_continuous.continuousAt.comp hm)).div_const ((theta 1) ^ 2)

/-- A two-exception version of the local removable-singularity argument. -/
theorem analyticAt_of_two_exceptions {f : ℂ → ℂ} {a b : ℂ}
    (hab : a ≠ b)
    (hd : ∀ z : ℂ, z ≠ a → z ≠ b → DifferentiableAt ℂ f z)
    (hc : ContinuousAt f a) : AnalyticAt ℂ f a := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hb : ∀ᶠ z : ℂ in 𝓝 a, z ≠ b :=
      IsOpen.eventually_mem isOpen_ne hab
    have ha : ∀ᶠ z : ℂ in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
    filter_upwards [ha, hb.filter_mono nhdsWithin_le_nhds] with z hza hzb
    exact hd z hza hzb
  · exact hc

theorem symmetricProduct_analyticAt_zero :
    AnalyticAt ℂ symmetricProduct (0 : ℂ) := by
  apply analyticAt_of_two_exceptions (b := (1 : ℂ)) (by norm_num)
  · intro z hz0 hz1
    exact symmetricProduct_differentiableAt_of_ne hz0 hz1
  · apply symmetricProduct_continuousAt_of_discriminant_zero
    norm_num [rootDiscriminant]

theorem symmetricProduct_analyticAt_one :
    AnalyticAt ℂ symmetricProduct (1 : ℂ) := by
  apply analyticAt_of_two_exceptions (b := (0 : ℂ)) (by norm_num)
  · intro z hz1 hz0
    exact symmetricProduct_differentiableAt_of_ne hz0 hz1
  · apply symmetricProduct_continuousAt_of_discriminant_zero
    norm_num [rootDiscriminant]

theorem symmetricProduct_differentiable : Differentiable ℂ symmetricProduct := by
  intro r
  by_cases hr0 : r = 0
  · subst r
    exact symmetricProduct_analyticAt_zero.differentiableAt
  · by_cases hr1 : r = 1
    · subst r
      exact symmetricProduct_analyticAt_one.differentiableAt
    · exact symmetricProduct_differentiableAt_of_ne hr0 hr1

theorem symmetricProduct_analyticAt (r : ℂ) : AnalyticAt ℂ symmetricProduct r :=
  symmetricProduct_differentiable.analyticAt r

/-- Entire analyticity of the original product, with no extra theorem parameters. -/
theorem symmetricProduct_entire : AnalyticOnNhd ℂ symmetricProduct Set.univ := by
  intro r _
  exact symmetricProduct_analyticAt r

end AWPIRH
