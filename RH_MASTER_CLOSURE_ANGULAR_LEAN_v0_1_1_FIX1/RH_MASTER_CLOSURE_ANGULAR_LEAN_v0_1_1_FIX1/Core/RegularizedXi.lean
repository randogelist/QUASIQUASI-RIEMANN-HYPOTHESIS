import Mathlib

namespace Merger04.Regularization

/-- The literal product used by the earlier frozen Widder core. -/
noncomputable def rawXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta s

/-- Entire doubled-xi normalization, including its removable endpoint values. -/
noncomputable def entireXi (s : ℂ) : ℂ :=
  1 + s * (s - 1) * completedRiemannZeta₀ s

@[simp] theorem RAW_XI_ZERO : rawXi 0 = 0 := by
  simp [rawXi]

@[simp] theorem RAW_XI_ONE : rawXi 1 = 0 := by
  simp [rawXi]

@[simp] theorem ENTIRE_XI_ZERO : entireXi 0 = 1 := by
  simp [entireXi]

@[simp] theorem ENTIRE_XI_ONE : entireXi 1 = 1 := by
  simp [entireXi]

/-- Actual differentiability, not a field in an analytic interface. -/
theorem ENTIRE_XI_DIFFERENTIABLE : Differentiable ℂ entireXi := by
  intro s
  have hL : DifferentiableAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀ s
  unfold entireXi
  fun_prop

/-- The functional equation for the endpoint-safe normalization. -/
theorem ENTIRE_XI_ONE_SUB (s : ℂ) :
    entireXi (1 - s) = entireXi s := by
  unfold entireXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- The old and entire formulas agree precisely on the regular locus. -/
theorem RAW_EQ_ENTIRE_AWAY_FROM_ENDPOINTS
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rawXi s = entireXi s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  unfold rawXi entireXi
  rw [completedRiemannZeta_eq]
  field_simp [hs0, h1s] <;> ring

/-- This prevents a global function-equality migration from being asserted. -/
theorem RAW_XI_NE_ENTIRE_XI : rawXi ≠ entireXi := by
  intro h
  have h_at_one := congrFun h (1 : ℂ)
  have h01 : (0 : ℂ) = 1 := by simpa using h_at_one
  exact zero_ne_one h01

/-- Entire centered function; its square descent can be built by evenness. -/
noncomputable def centeredXi (w : ℂ) : ℂ :=
  entireXi ((1 / 2 : ℂ) + w)

theorem CENTERED_XI_DIFFERENTIABLE : Differentiable ℂ centeredXi := by
  intro w
  unfold centeredXi
  exact (ENTIRE_XI_DIFFERENTIABLE ((1 / 2 : ℂ) + w)).comp w (by fun_prop)

theorem CENTERED_XI_EVEN (w : ℂ) : centeredXi (-w) = centeredXi w := by
  unfold centeredXi
  have h := ENTIRE_XI_ONE_SUB ((1 / 2 : ℂ) + w)
  convert h using 1 <;> ring

end Merger04.Regularization
