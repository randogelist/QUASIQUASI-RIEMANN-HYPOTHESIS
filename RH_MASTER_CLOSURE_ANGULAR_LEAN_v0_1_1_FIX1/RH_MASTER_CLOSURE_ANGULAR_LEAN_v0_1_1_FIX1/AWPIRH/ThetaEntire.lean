import AWPIRH.XiCore

/-!
Entire descent of the ACTUAL centered xi through the square map.

The principal square root is only used where its behavior has been justified.
At a nonzero center z0, sqrt(z0)*sqrt(z/z0) is differentiable at z0, because
z/z0 = 1 there. Its square is z everywhere. The previously proved theta_square
then identifies the resulting local expression with the literal theta.
At zero, continuity and the removable-singularity theorem finish the descent.
No nonvanishing assertion about xi away from the existing positive anchor enters.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

/-- The square root is differentiable at 1, a point of its slit domain. -/
theorem sqrt_differentiableAt_one :
    DifferentiableAt ℂ Complex.sqrt (1 : ℂ) := by
  have hslit : (1 : ℂ) ∈ Complex.slitPlane := by
    exact Or.inl (by norm_num)
  have h : DifferentiableAt ℂ (fun z : ℂ => z ^ (2 : ℂ)⁻¹) (1 : ℂ) :=
    differentiableAt_id.cpow_const hslit
  have hsqrt : Complex.sqrt = (fun z : ℂ => z ^ (2 : ℂ)⁻¹) := by
    funext z
    simp only [Complex.sqrt]
  rw [hsqrt]
  exact h

/-- At the branch point zero, only continuity is needed or claimed. -/
theorem sqrt_continuousAt_zero : ContinuousAt Complex.sqrt (0 : ℂ) := by
  have h : ContinuousAt (fun z : ℂ => z ^ (2 : ℂ)⁻¹) (0 : ℂ) :=
    Complex.continuousAt_cpow_const_of_re_pos
      (Or.inl (by norm_num)) (by norm_num)
  have hsqrt : Complex.sqrt = (fun z : ℂ => z ^ (2 : ℂ)⁻¹) := by
    funext z
    simp only [Complex.sqrt]
  rw [hsqrt]
  exact h

/-- A root normalized around a nonzero center; not a global analytic branch. -/
def normalizedSqrt (z0 z : ℂ) : ℂ :=
  Complex.sqrt z0 * Complex.sqrt (z / z0)

theorem normalizedSqrt_sq {z0 : ℂ} (hz0 : z0 ≠ 0) (z : ℂ) :
    (normalizedSqrt z0 z) ^ 2 = z := by
  rw [normalizedSqrt, mul_pow, complex_sqrt_sq, complex_sqrt_sq]
  field_simp [hz0] <;> ring

theorem normalizedSqrt_differentiableAt {z0 : ℂ} (hz0 : z0 ≠ 0) :
    DifferentiableAt ℂ (normalizedSqrt z0) z0 := by
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / z0) z0 := by
    simpa only [div_eq_mul_inv] using
      (hasDerivAt_mul_const (𝕜 := ℂ) (x := z0) z0⁻¹).differentiableAt
  have hsqrt : DifferentiableAt ℂ Complex.sqrt (z0 / z0) := by
    rw [div_self hz0]
    exact sqrt_differentiableAt_one
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => Complex.sqrt (z / z0)) z0 := by
    exact DifferentiableAt.fun_comp'
      (f := fun z : ℂ => z / z0) (g := Complex.sqrt) z0 hsqrt hdiv
  have hmul : DifferentiableAt ℂ
      (fun w : ℂ => Complex.sqrt z0 * w) (Complex.sqrt (z0 / z0)) :=
    (hasDerivAt_const_mul (𝕜 := ℂ)
      (x := Complex.sqrt (z0 / z0)) (Complex.sqrt z0)).differentiableAt
  change DifferentiableAt ℂ
    (fun z : ℂ => Complex.sqrt z0 * Complex.sqrt (z / z0)) z0
  exact DifferentiableAt.fun_comp'
    (f := fun z : ℂ => Complex.sqrt (z / z0))
    (g := fun w : ℂ => Complex.sqrt z0 * w) z0 hmul hcomp

theorem theta_eq_normalizedSqrt {z0 : ℂ} (hz0 : z0 ≠ 0) (z : ℂ) :
    theta z = centeredXi (normalizedSqrt z0 z) := by
  have h := theta_square (normalizedSqrt z0 z)
  simpa only [normalizedSqrt_sq hz0 z] using h

theorem theta_differentiableAt_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ theta z := by
  have heq : theta = fun w : ℂ => centeredXi (normalizedSqrt z w) := by
    funext w
    exact theta_eq_normalizedSqrt hz w
  rw [heq]
  exact (centeredXi_differentiable (normalizedSqrt z z)).comp z
    (normalizedSqrt_differentiableAt hz)

theorem theta_continuousAt_zero : ContinuousAt theta (0 : ℂ) := by
  change ContinuousAt (fun z : ℂ => centeredXi (Complex.sqrt z)) (0 : ℂ)
  exact (centeredXi_differentiable (Complex.sqrt 0)).continuousAt.comp
    sqrt_continuousAt_zero

theorem theta_analyticAt_zero : AnalyticAt ℂ theta (0 : ℂ) := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hpunct : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
    exact hpunct.mono (fun z hz => theta_differentiableAt_of_ne_zero hz)
  · exact theta_continuousAt_zero

theorem theta_differentiable : Differentiable ℂ theta := by
  intro z
  by_cases hz : z = 0
  · subst z
    exact theta_analyticAt_zero.differentiableAt
  · exact theta_differentiableAt_of_ne_zero hz

theorem theta_analyticAt (z : ℂ) : AnalyticAt ℂ theta z :=
  theta_differentiable.analyticAt z

theorem theta_entire : AnalyticOnNhd ℂ theta Set.univ := by
  intro z _
  exact theta_analyticAt z

theorem theta_continuous : Continuous theta :=
  theta_differentiable.continuous

end AWPIRH
