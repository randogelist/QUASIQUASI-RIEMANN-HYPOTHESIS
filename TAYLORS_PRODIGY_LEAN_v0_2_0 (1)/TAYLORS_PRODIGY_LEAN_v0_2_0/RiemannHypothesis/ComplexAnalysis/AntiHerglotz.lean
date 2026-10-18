/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Anti-Herglotz functions on the upper half-plane

Abstract sign condition for residue clouds with real roots. Independent of
zeta, Xi, zero-counting, and all explicit-formula machinery.

## Main definitions

* `AntiHerglotzUHP R` — `Im R z ≤ 0` for all `z` with `Im z > 0`.
* `StrictAntiHerglotzUHP R` — the corresponding strict inequality.
* `PositiveUpperImaginaryEscape R` — some upper-half-plane `z` has `Im R z > 0`.

## Main results

* `antiHerglotz_iff_no_positiveUpperEscape` — the clean iff.
* `real_residue_cloud_antiHerglotz_list` — any finite real-root cloud is anti-Herglotz.
* `real_weighted_residue_cloud_antiHerglotz_list` — weighted generalisation (non-negative weights).
-/

namespace OverflowResidueRH

open Complex Filter Topology

-- =====================================================================
-- §1. Sign laws
-- =====================================================================

/-- **Anti-Herglotz upper-half-plane sign law.** `R : ℂ → ℂ` is
anti-Herglotz iff `Im R z ≤ 0` for every `z` with `Im z > 0`. The sign law
of any real-rooted residue cloud `Σ m_j / (z − r_j)` with real `r_j` and
positive `m_j`. -/
def AntiHerglotzUHP (R : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → (R z).im ≤ 0

/-- **Strict anti-Herglotz upper-half-plane sign law.** This is the
classical strict form needed for logarithmic derivatives of nonconstant
real-rooted products. -/
def StrictAntiHerglotzUHP (R : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → (R z).im < 0

/-- A strict anti-Herglotz function is anti-Herglotz. -/
theorem StrictAntiHerglotzUHP.antiHerglotz
    {R : ℂ → ℂ} (hR : StrictAntiHerglotzUHP R) :
    AntiHerglotzUHP R :=
  fun z hz => (hR z hz).le

/-- **Positive upper imaginary escape.** Some upper-half-plane point has
strictly positive imaginary response — the witness produced by a nonreal
upper-half-plane pole of the function whose log-derivative is `R`. -/
def PositiveUpperImaginaryEscape (R : ℂ → ℂ) : Prop :=
  ∃ z : ℂ, 0 < z.im ∧ 0 < (R z).im

/-- **The clean iff.** Anti-Herglotz on the upper half-plane is precisely
the absence of positive upper-imaginary escape. -/
theorem antiHerglotz_iff_no_positiveUpperEscape (R : ℂ → ℂ) :
    AntiHerglotzUHP R ↔ ¬ PositiveUpperImaginaryEscape R := by
  unfold AntiHerglotzUHP PositiveUpperImaginaryEscape
  constructor
  · intro hanti ⟨z, hzim, hRim⟩
    exact absurd (hanti z hzim) (not_le.mpr hRim)
  · intro hno z hzim
    by_contra hpos
    push Not at hpos
    exact hno ⟨z, hzim, hpos⟩

/-- The logical gate — restating the iff as the contradiction direction. -/
theorem positive_escape_kills_antiHerglotz
    {R : ℂ → ℂ} (h : PositiveUpperImaginaryEscape R) :
    ¬ AntiHerglotzUHP R :=
  fun hanti => (antiHerglotz_iff_no_positiveUpperEscape R).mp hanti h

-- =====================================================================
-- §2. Real residue clouds
-- =====================================================================

/-- **Atom.** For a real root `r` and any upper-half-plane `z`,
  Im(1 / (z − r)) = −(Im z) / |z − r|² ≤ 0.
The single nonpositivity fact from which the anti-Herglotz cloud law
follows by summation. -/
theorem complex_real_root_residue_imag_nonpos
    (z : ℂ) (r : ℝ) (hz : 0 < z.im) :
    ((1 : ℂ) / (z - (r : ℂ))).im ≤ 0 := by
  -- z ≠ r since z has positive imaginary part and r is real.
  have hne : z - (r : ℂ) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have him : z.im = ((r : ℂ)).im := congr_arg Complex.im h
    rw [Complex.ofReal_im] at him
    linarith
  rw [one_div, Complex.inv_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hns : 0 < Complex.normSq (z - (r : ℂ)) := Complex.normSq_pos.mpr hne
  exact le_of_lt (div_neg_of_neg_of_pos (by linarith) hns)

/-- **Strict real residue atom.** A real pole contributes strictly negative
imaginary part at every point of the open upper half-plane. -/
theorem complex_real_root_residue_imag_neg
    (z : ℂ) (r : ℝ) (hz : 0 < z.im) :
    ((1 : ℂ) / (z - (r : ℂ))).im < 0 := by
  have hne : z - (r : ℂ) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have him : z.im = ((r : ℂ)).im := congrArg Complex.im h
    rw [Complex.ofReal_im] at him
    linarith
  rw [one_div, Complex.inv_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hns : 0 < Complex.normSq (z - (r : ℂ)) := Complex.normSq_pos.mpr hne
  exact div_neg_of_neg_of_pos (by linarith) hns

/-- **Real residue cloud is anti-Herglotz.** For any finite list of real
roots, the cloud `z ↦ Σ_r 1 / (z − r)` satisfies the anti-Herglotz
upper-half-plane sign law. -/
theorem real_residue_cloud_antiHerglotz_list (rs : List ℝ) :
    AntiHerglotzUHP
      (fun z : ℂ => (rs.map (fun r : ℝ => (1 : ℂ) / (z - (r : ℂ)))).sum) := by
  intro z hz
  change ((rs.map (fun r : ℝ => (1 : ℂ) / (z - (r : ℂ)))).sum).im ≤ 0
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_im]
    have h1 : ((1 : ℂ) / (z - (r : ℂ))).im ≤ 0 :=
      complex_real_root_residue_imag_nonpos z r hz
    linarith

/-- ⭐ **PROVED — weighted real residue cloud is anti-Herglotz.**
Generalizes `real_residue_cloud_antiHerglotz_list` to `(root, weight)`
pairs with non-negative real weights. -/
theorem real_weighted_residue_cloud_antiHerglotz_list
    (atoms : List (ℝ × ℝ))
    (hweights : ∀ a ∈ atoms, 0 ≤ a.2) :
    AntiHerglotzUHP
      (fun z : ℂ =>
        (atoms.map fun a : ℝ × ℝ =>
          (a.2 : ℂ) * ((1 : ℂ) / (z - (a.1 : ℂ)))).sum) := by
  intro z hz
  change ((atoms.map fun a : ℝ × ℝ =>
          (a.2 : ℂ) * ((1 : ℂ) / (z - (a.1 : ℂ)))).sum).im ≤ 0
  induction atoms with
  | nil => simp
  | cons a atoms ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_im]
    have ha_weight : 0 ≤ a.2 := hweights a (List.mem_cons_self ..)
    have hrest : ∀ b ∈ atoms, 0 ≤ b.2 :=
      fun b hb => hweights b (List.mem_cons_of_mem _ hb)
    have h_residue : ((1 : ℂ) / (z - (a.1 : ℂ))).im ≤ 0 :=
      complex_real_root_residue_imag_nonpos z a.1 hz
    have h_atom :
        ((a.2 : ℂ) * ((1 : ℂ) / (z - (a.1 : ℂ)))).im ≤ 0 := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos ha_weight h_residue
    have h_tail := ih hrest
    linarith

-- =====================================================================
-- §3. Limit closure
-- =====================================================================

/-- **UHP-restricted closure for `AntiHerglotzUHP`.**
If `F X` is eventually anti-Herglotz and `F X z → f z` pointwise *only
on UHP*, then `f` is anti-Herglotz. -/
theorem AntiHerglotzUHP.of_eventual_pointwise_tendsto_UHP
    {F : ℝ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ᶠ X in Filter.atTop, AntiHerglotzUHP (F X))
    (hlim : ∀ z, 0 < z.im →
      Tendsto (fun X => F X z) Filter.atTop (𝓝 (f z))) :
    AntiHerglotzUHP f := by
  intro z hz
  have him_tendsto :
      Tendsto (fun X => (F X z).im) Filter.atTop (𝓝 (f z).im) :=
    (Complex.continuous_im.tendsto _).comp (hlim z hz)
  have hF_im_le : ∀ᶠ X in Filter.atTop, (F X z).im ≤ 0 := by
    filter_upwards [hF] with X hFX
    exact hFX z hz
  exact le_of_tendsto him_tendsto hF_im_le

end OverflowResidueRH
