import AngularMaster.ZeroGeometry

/-!
Exact slope/sector geometry for the actual Riemann zeta function.

The theorem `QQRH_of_theta_sector_nonvanishing` transfers a nonvanishing
certificate for the literal entire theta to a wedge in the critical strip.
It does not assert that a positivity or nonvanishing certificate exists.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

open AWPIRH

/-- The angular cutoff associated with the slope `m`. -/
def slopeCutoff (m : ℝ) : ℝ := (1 - m ^ 2) / (1 + m ^ 2)

theorem slopeCutoff_two : slopeCutoff 2 = -(3 / 5 : ℝ) := by
  norm_num [slopeCutoff]

theorem slopeCutoff_mem_Ioo {m : ℝ} (hm : 0 < m) :
    slopeCutoff m ∈ Set.Ioo (-1) 1 := by
  have hden : 0 < 1 + m ^ 2 := by positivity
  constructor
  · change -1 < (1 - m ^ 2) / (1 + m ^ 2)
    apply (lt_div_iff₀ hden).2
    nlinarith [sq_nonneg m]
  · change (1 - m ^ 2) / (1 + m ^ 2) < 1
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_pos_of_pos hm]

/-- The requested wedge statement uses the actual Mathlib Riemann zeta. -/
def QQRH (m : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 →
    |s.im| < m * |s.re - 1 / 2| → riemannZeta s ≠ 0

theorem norm_square_eq_re_sq_add_im_sq (w : ℂ) :
    ‖w ^ 2‖ = w.re ^ 2 + w.im ^ 2 := by
  rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem square_re_eq_re_sq_sub_im_sq (w : ℂ) :
    (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
  simp [pow_two, Complex.mul_re]

theorem square_ne_zero_of_wedge {m : ℝ} {w : ℂ}
    (hwedge : |w.im| < m * |w.re|) : w ^ 2 ≠ 0 := by
  have hw : w ≠ 0 := by
    intro hw
    subst w
    simpa using hwedge
  exact pow_ne_zero 2 hw

/-- Squaring a wedge gives the exact angular sector; no zero assumption enters. -/
theorem slopeCutoff_lt_square_angle {m : ℝ} (hm : 0 < m) {w : ℂ}
    (hwedge : |w.im| < m * |w.re|) :
    slopeCutoff m < (w ^ 2).re / ‖w ^ 2‖ := by
  have hsum : 0 < w.re ^ 2 + w.im ^ 2 := by
    rw [← norm_square_eq_re_sq_add_im_sq]
    exact norm_pos_iff.mpr (square_ne_zero_of_wedge hwedge)
  have hden : 0 < 1 + m ^ 2 := by positivity
  have hprod : 0 < (m * |w.re| - |w.im|) * (m * |w.re| + |w.im|) := by
    apply mul_pos (sub_pos.mpr hwedge)
    linarith [abs_nonneg w.im]
  have hidentity :
      (m * |w.re| - |w.im|) * (m * |w.re| + |w.im|) =
        m ^ 2 * w.re ^ 2 - w.im ^ 2 := by
    calc
      _ = m ^ 2 * |w.re| ^ 2 - |w.im| ^ 2 := by ring
      _ = _ := by rw [sq_abs, sq_abs]
  rw [hidentity] at hprod
  rw [slopeCutoff, square_re_eq_re_sq_sub_im_sq,
    norm_square_eq_re_sq_add_im_sq]
  apply (div_lt_div_iff₀ hden hsum).2
  nlinarith only [hprod]

theorem centeredSquare_ne_zero_of_wedge {m : ℝ} {s : ℂ}
    (hwedge : |s.im| < m * |s.re - 1 / 2|) :
    (s - (1 / 2 : ℂ)) ^ 2 ≠ 0 := by
  apply square_ne_zero_of_wedge (m := m)
  convert hwedge using 1 <;> norm_num [Complex.sub_re, Complex.sub_im]

theorem slopeCutoff_lt_centeredSquare_angle {m : ℝ} (hm : 0 < m) {s : ℂ}
    (hwedge : |s.im| < m * |s.re - 1 / 2|) :
    slopeCutoff m <
      ((s - (1 / 2 : ℂ)) ^ 2).re / ‖(s - (1 / 2 : ℂ)) ^ 2‖ := by
  apply slopeCutoff_lt_square_angle hm
  convert hwedge using 1 <;> norm_num [Complex.sub_re, Complex.sub_im]

/-- A theta sector certificate transfers to the actual zeta wedge. -/
theorem QQRH_of_theta_sector_nonvanishing {m : ℝ} (hm : 0 < m)
    (hsector : ∀ z : ℂ, z ≠ 0 → slopeCutoff m < z.re / ‖z‖ → theta z ≠ 0) :
    QQRH m := by
  intro s hs0 hs1 hwedge hzeta
  have hnontrivial : NontrivialZero s := by
    refine ⟨hzeta, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp [Complex.mul_re] at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
  exact hsector _ (centeredSquare_ne_zero_of_wedge hwedge)
    (slopeCutoff_lt_centeredSquare_angle hm hwedge)
    (theta_zero_of_nontrivialZero hnontrivial)

end AngularMaster
