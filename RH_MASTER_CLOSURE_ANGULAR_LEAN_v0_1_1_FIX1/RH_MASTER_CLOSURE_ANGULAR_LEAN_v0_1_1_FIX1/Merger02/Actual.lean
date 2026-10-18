import Mathlib

/-!
Merger_02: literal actual-xi data, without a freely supplied sequence.
The theta representative below is used only in a neighborhood of 1.
No global analyticity claim about the raw principal-square-root expression
is used in the theorems in this file.
-/
namespace Merger02

open Complex
open scoped BigOperators

noncomputable def actualXi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

theorem actualXi_entire : Differentiable ℂ actualXi := by
  intro s
  have hL : DifferentiableAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀ s
  unfold actualXi
  fun_prop

theorem actualXi_reflection (s : ℂ) : actualXi (1 - s) = actualXi s := by
  unfold actualXi
  rw [completedRiemannZeta₀_one_sub]
  ring

noncomputable def centeredXi (w : ℂ) : ℂ := actualXi ((1 / 2 : ℂ) + w)

theorem centeredXi_entire : Differentiable ℂ centeredXi := by
  intro w
  unfold centeredXi
  exact (actualXi_entire ((1 / 2 : ℂ) + w)).comp w (by fun_prop)

theorem centeredXi_even (w : ℂ) : centeredXi (-w) = centeredXi w := by
  unfold centeredXi
  have h := actualXi_reflection ((1 / 2 : ℂ) + w)
  convert h using 1 <;> ring

noncomputable def theta (z : ℂ) : ℂ := centeredXi (Complex.sqrt z)

theorem theta_analyticOnSlit : AnalyticOnNhd ℂ theta Complex.slitPlane := by
  have hd : DifferentiableOn ℂ theta Complex.slitPlane := by
    intro z hz
    unfold theta
    exact ((centeredXi_entire (Complex.sqrt z)).comp z
      (Complex.differentiableAt_sqrt hz)).differentiableWithinAt
  exact hd.analyticOnNhd Complex.isOpen_slitPlane

theorem theta_analyticAt_one : AnalyticAt ℂ theta 1 := by
  apply theta_analyticOnSlit
  simp [Complex.mem_slitPlane_iff]

theorem actualXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    actualXi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    norm_num [actualXi]
  · have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    intro hxi
    apply hzeta
    rw [riemannZeta_eq_mul_completedRiemannZeta₀]
    have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
      simpa [actualXi] using hxi
    have h1ms : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hnum : s * completedRiemannZeta₀ s - 1 - s / (1 - s) = 0 := by
      calc
        s * completedRiemannZeta₀ s - 1 - s / (1 - s)
            = -(1 + s * (s - 1) * completedRiemannZeta₀ s) / (1 - s) := by
                field_simp [h1ms]
                ring
        _ = 0 := by rw [hraw]; simp
    rw [hnum]
    simp

theorem theta_one_ne_zero : theta 1 ≠ 0 := by
  have hx : actualXi (3 / 2 : ℂ) ≠ 0 :=
    actualXi_ne_zero_of_one_le_re (by norm_num)
  have heq : theta 1 = actualXi (3 / 2 : ℂ) := by
    norm_num [theta, centeredXi]
  rw [heq]
  exact hx

noncomputable def g (z : ℂ) : ℂ := z * deriv theta z / theta z

theorem g_analyticAt_one : AnalyticAt ℂ g 1 := by
  have ht := theta_analyticAt_one
  unfold g
  exact (analyticAt_id.fun_mul ht.deriv).fun_div ht theta_one_ne_zero

/-- This is the derivative jet in the paper, represented in C without
throwing away its imaginary component or changing its normalization. -/
noncomputable def actualJet (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * iteratedDeriv (n + 1) g 1 / ((n + 1).factorial : ℂ)

noncomputable def gTaylor : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n : ℕ => iteratedDeriv n g 1 / (n.factorial : ℂ))

theorem g_has_actual_Taylor_series : HasFPowerSeriesAt g gTaylor 1 := by
  simpa [gTaylor] using g_analyticAt_one.hasFPowerSeriesAt

noncomputable def row (s : ℕ → ℂ) (N j : ℕ) : ℂ :=
  (N.choose j : ℂ) *
    ∑ r ∈ Finset.range (N - j + 1),
      (-1 : ℂ) ^ r * ((N - j).choose r : ℂ) * s (j + r)

noncomputable def rowPolynomial (s : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), row s N j * z ^ j

noncomputable def energy (s : ℕ → ℂ) (N : ℕ) : ℝ :=
  (N + 1 : ℝ) * ∑ j ∈ Finset.range (N + 1), ‖row s N j‖ ^ 2

noncomputable def actualEnergy : ℕ → ℝ := energy actualJet

theorem energy_nonneg (s : ℕ → ℂ) (N : ℕ) : 0 ≤ energy s N := by
  unfold energy
  positivity

theorem actualEnergy_nonneg (N : ℕ) : 0 ≤ actualEnergy N := energy_nonneg _ _

@[simp] theorem row_diagonal (s : ℕ → ℂ) (N : ℕ) : row s N N = s N := by
  simp [row]

@[simp] theorem row_zero (s : ℕ → ℂ) : row s 0 0 = s 0 := by
  simp [row]

@[simp] theorem energy_zero (s : ℕ → ℂ) : energy s 0 = ‖s 0‖ ^ 2 := by
  simp [energy]

/-- Literal Mathlib nontrivial-zero predicate; no alternative RH is defined. -/
def NontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) ∧ s ≠ 1

end Merger02
