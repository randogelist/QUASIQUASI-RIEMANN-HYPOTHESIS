/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannHypothesis.ComplexAnalysis.MellinGrowth

/-!
# Two-sided exponential decay of the modified theta kernel

This file connects Mathlib's concrete Hurwitz theta kernel to the explicit
Mellin-growth API in `ComplexAnalysis.MellinGrowth`.

For the self-dual parameter `a = 0`, the modified kernel

`(HurwitzZeta.hurwitzEvenFEPair 0).f_modif`

is `evenKernel 0 - 1` on `(1, ∞)`, is zero at `1`, and satisfies the
inversion law of weight `1 / 2`.  Mathlib proves exponential decay only as an
eventual big-O statement.  We extend it to all of `[1, ∞)` by taking the
maximum of the exponentially weighted kernel on the remaining compact
interval.  Inversion then supplies the matching lower-tail estimate.
-/

namespace OverflowResidueRH

open MeasureTheory Set Filter Topology Asymptotics
open Real Complex

/-- The modified, self-dual Hurwitz theta kernel used in the Mellin
representation.  It is deliberately zero at `x = 1`; this is the convention
used by `WeakFEPair.f_modif` to preserve exact inversion symmetry. -/
noncomputable def hurwitzThetaMellinKernel : ℝ → ℂ :=
  (HurwitzZeta.hurwitzEvenFEPair 0).f_modif

@[simp]
theorem hurwitzThetaMellinKernel_one :
    hurwitzThetaMellinKernel 1 = 0 := by
  simp [hurwitzThetaMellinKernel, WeakFEPair.f_modif]

/-- Above `1`, the modified kernel is exactly the constant-subtracted even
Hurwitz kernel. -/
theorem hurwitzThetaMellinKernel_eq_evenKernel_sub_one
    {x : ℝ} (hx : 1 < x) :
    hurwitzThetaMellinKernel x =
      ((HurwitzZeta.evenKernel 0 x - 1 : ℝ) : ℂ) := by
  simp [hurwitzThetaMellinKernel, WeakFEPair.f_modif,
    HurwitzZeta.hurwitzEvenFEPair, hx, hx.le]

private theorem hurwitzEvenFEPair_zero_g_modif_eq_f_modif (x : ℝ) :
    (HurwitzZeta.hurwitzEvenFEPair 0).g_modif x =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  change (HurwitzZeta.hurwitzEvenFEPair 0).symm.f_modif x = _
  rw [HurwitzZeta.hurwitzEvenFEPair_zero_symm]

/-- Exact self-dual inversion of the modified kernel, with weight `1 / 2`. -/
theorem hurwitzThetaMellinKernel_inversion (x : ℝ) (hx : 0 < x) :
    hurwitzThetaMellinKernel (1 / x) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) • hurwitzThetaMellinKernel x := by
  have h := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE x hx
  rw [hurwitzEvenFEPair_zero_g_modif_eq_f_modif] at h
  simpa [hurwitzThetaMellinKernel, HurwitzZeta.hurwitzEvenFEPair] using h

/-- There are positive exponential rate and nonnegative amplitude constants
which bound the concrete modified kernel on the entire upper half-line.

The compact maximum is taken for
`x ↦ ‖(evenKernel 0 x - 1 : ℂ)‖ * exp (p * x)`.  This avoids any
continuity claim about `f_modif` at `x = 1`, where that function is defined to
be zero. -/
theorem exists_hurwitzThetaMellinKernel_upper_bound :
    ∃ p A : ℝ, 0 < p ∧ 0 ≤ A ∧
      ∀ x : ℝ, 1 ≤ x →
        ‖hurwitzThetaMellinKernel x‖ ≤ A * Real.exp (-(p * x)) := by
  obtain ⟨p, hp, hO⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub 0
  obtain ⟨C, hC, hCbound⟩ := hO.exists_nonneg
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hCbound.bound
  let X : ℝ := max 1 X₀
  have hX : 1 ≤ X := le_max_left _ _
  have hlarge (x : ℝ) (hx : X ≤ x) :
      |HurwitzZeta.evenKernel 0 x - 1| ≤
        C * Real.exp (-(p * x)) := by
    have h := hX₀ x (le_trans (le_max_right _ _) hx)
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h
  let q : ℝ → ℝ := fun x ↦
    ‖((HurwitzZeta.evenKernel 0 x - 1 : ℝ) : ℂ)‖ *
      Real.exp (p * x)
  have hsubset : Set.Icc (1 : ℝ) X ⊆ Set.Ioi 0 := by
    intro x hx
    exact lt_of_lt_of_le zero_lt_one hx.1
  have heven :
      ContinuousOn (HurwitzZeta.evenKernel 0) (Set.Icc (1 : ℝ) X) :=
    (HurwitzZeta.continuousOn_evenKernel 0).mono hsubset
  have hsub : ContinuousOn
      (fun x : ℝ ↦ HurwitzZeta.evenKernel 0 x - 1)
      (Set.Icc (1 : ℝ) X) :=
    heven.sub continuousOn_const
  have hq : ContinuousOn q (Set.Icc (1 : ℝ) X) := by
    dsimp [q]
    exact (continuous_ofReal.comp_continuousOn hsub).norm.mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨x₀, hx₀, hx₀max⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) X)).exists_isMaxOn
      (Set.nonempty_Icc.mpr hX) hq
  let B : ℝ := q x₀
  have hB : 0 ≤ B := by
    dsimp [B, q]
    positivity
  let A : ℝ := max C B
  have hA : 0 ≤ A := le_trans hC (le_max_left C B)
  refine ⟨p, A, hp, hA, ?_⟩
  intro x hx
  by_cases hxone : x = 1
  · subst x
    rw [hurwitzThetaMellinKernel_one, norm_zero]
    positivity
  have hxlt : 1 < x := lt_of_le_of_ne hx (Ne.symm hxone)
  rw [hurwitzThetaMellinKernel_eq_evenKernel_sub_one hxlt]
  by_cases hcompact : x ≤ X
  · have hweighted :
        ‖((HurwitzZeta.evenKernel 0 x - 1 : ℝ) : ℂ)‖ *
            Real.exp (p * x) ≤ B := by
      exact hx₀max ⟨hx, hcompact⟩
    calc
      ‖((HurwitzZeta.evenKernel 0 x - 1 : ℝ) : ℂ)‖ =
          (‖((HurwitzZeta.evenKernel 0 x - 1 : ℝ) : ℂ)‖ *
              Real.exp (p * x)) * Real.exp (-(p * x)) := by
            rw [mul_assoc, ← Real.exp_add]
            simp
      _ ≤ B * Real.exp (-(p * x)) :=
        mul_le_mul_of_nonneg_right hweighted (Real.exp_nonneg _)
      _ ≤ A * Real.exp (-(p * x)) :=
        mul_le_mul_of_nonneg_right (le_max_right C B) (Real.exp_nonneg _)
  · have hlarge' := hlarge x (le_of_not_ge hcompact)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans hlarge'
      (mul_le_mul_of_nonneg_right (le_max_left C B) (Real.exp_nonneg _))

/-- Bundled upper-tail constants for the concrete Hurwitz theta kernel. -/
structure HurwitzThetaMellinUpperDecay where
  p : ℝ
  A : ℝ
  p_pos : 0 < p
  A_nonneg : 0 ≤ A
  upper : ∀ x : ℝ, 1 ≤ x →
    ‖hurwitzThetaMellinKernel x‖ ≤ A * Real.exp (-(p * x))

theorem hurwitzThetaMellinUpperDecay_nonempty :
    Nonempty HurwitzThetaMellinUpperDecay := by
  obtain ⟨p, A, hp, hA, hupper⟩ :=
    exists_hurwitzThetaMellinKernel_upper_bound
  exact ⟨⟨p, A, hp, hA, hupper⟩⟩

/-- A fixed choice of valid upper-tail constants. -/
noncomputable def hurwitzThetaMellinUpperDecay :
    HurwitzThetaMellinUpperDecay :=
  Classical.choice hurwitzThetaMellinUpperDecay_nonempty

/-- The actual modified Hurwitz theta kernel has two-sided exponential decay,
with the exact functional-equation weight `k = 1 / 2`. -/
noncomputable def hurwitzThetaMellinTwoSidedExponentialDecay :
    MellinTwoSidedExponentialDecay hurwitzThetaMellinKernel := by
  let U := hurwitzThetaMellinUpperDecay
  refine
    { k := 1 / 2
      p := U.p
      A := U.A
      p_pos := U.p_pos
      A_nonneg := U.A_nonneg
      upper := U.upper
      lower := ?_ }
  intro x hx hxone
  have hypos : 0 < 1 / x := one_div_pos.mpr hx
  have hyone : 1 ≤ 1 / x := one_le_one_div hx hxone
  have hinv : hurwitzThetaMellinKernel x =
      ((((1 / x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
        hurwitzThetaMellinKernel (1 / x)) := by
    simpa [hx.ne'] using
      hurwitzThetaMellinKernel_inversion (1 / x) hypos
  rw [hinv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hypos.le _)]
  calc
    (1 / x) ^ (1 / 2 : ℝ) * ‖hurwitzThetaMellinKernel (1 / x)‖ ≤
        (1 / x) ^ (1 / 2 : ℝ) *
          (U.A * Real.exp (-(U.p * (1 / x)))) :=
      mul_le_mul_of_nonneg_left (U.upper (1 / x) hyone)
        (Real.rpow_nonneg hypos.le _)
    _ = U.A * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(U.p / x)) := by
      rw [one_div, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
      ring_nf

/-- Direct factorial Mellin envelope for the concrete modified Hurwitz theta
kernel.  The only remaining analytic input at a point `s` is Mellin
convergence itself. -/
theorem norm_mellin_hurwitzThetaMellinKernel_le_factorial
    (s : ℂ) (n : ℕ)
    (hupper : s.re - 1 ≤ n)
    (hlower : -(n : ℝ) - 2 ≤ s.re - 1 - (1 / 2 : ℝ))
    (hconv : MellinConvergent hurwitzThetaMellinKernel s) :
    ‖mellin hurwitzThetaMellinKernel s‖ ≤
      2 * hurwitzThetaMellinTwoSidedExponentialDecay.A *
        ((1 / hurwitzThetaMellinTwoSidedExponentialDecay.p) ^
          (n + 1 : ℝ) * n.factorial) := by
  apply hurwitzThetaMellinTwoSidedExponentialDecay.norm_mellin_le_factorial
  · exact hupper
  · exact hlower
  · exact hconv

/-! ## The concrete completed zeta function -/

/-- Mathlib's pole-subtracted completed zeta function is exactly one half of
the Mellin transform of the concrete modified theta kernel at `s / 2`. -/
theorem completedRiemannZeta₀_eq_thetaMellin (s : ℂ) :
    completedRiemannZeta₀ s =
      mellin hurwitzThetaMellinKernel (s / 2) / 2 := by
  rfl

/-- The modified theta-kernel Mellin transform converges at every complex
parameter, as supplied by Mathlib's strong functional-equation pair. -/
theorem hurwitzThetaMellinKernel_convergent (s : ℂ) :
    MellinConvergent hurwitzThetaMellinKernel s := by
  exact (HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin s |>.1

/-- Direct factorial envelope for Mathlib's actual
`completedRiemannZeta₀`. -/
theorem norm_completedRiemannZeta₀_le_factorial
    (s : ℂ) (n : ℕ)
    (hupper : (s / 2).re - 1 ≤ n)
    (hlower : -(n : ℝ) - 2 ≤
      (s / 2).re - 1 - (1 / 2 : ℝ)) :
    ‖completedRiemannZeta₀ s‖ ≤
      hurwitzThetaMellinTwoSidedExponentialDecay.A *
        ((1 / hurwitzThetaMellinTwoSidedExponentialDecay.p) ^
          (n + 1 : ℝ) * n.factorial) := by
  rw [completedRiemannZeta₀_eq_thetaMellin, norm_div]
  rw [Complex.norm_two]
  have h := norm_mellin_hurwitzThetaMellinKernel_le_factorial
    (s / 2) n hupper hlower
      (hurwitzThetaMellinKernel_convergent (s / 2))
  nlinarith

end OverflowResidueRH
