import MisterPremise.MathlibImports

/-! The exact radius-dependent cutoff used by MISTERPREMISE. -/

set_option autoImplicit false
noncomputable section

namespace MisterPremise

def factorThreshold (r R : ℝ) : ℝ :=
  (R - 1 / 2) * (R ^ 2 + r ^ 2) / (2 * r * R ^ 2)

def thresholdValues (r : ℝ) : Set ℝ :=
  {v | ∃ R : ℝ, (85 / 2 : ℝ) ≤ R ∧ v = factorThreshold r R}

/-- This is precisely the infimum in the analytic statement, not a replacement
by a fixed angular cutoff. -/
def kappa (r : ℝ) : ℝ := sInf (thresholdValues r)

theorem thresholdValues_nonempty (r : ℝ) : (thresholdValues r).Nonempty := by
  exact ⟨factorThreshold r (85 / 2), 85 / 2, le_rfl, rfl⟩

theorem factorThreshold_lower_bound {r R : ℝ} (hr : 0 < r)
    (hR : (85 / 2 : ℝ) ≤ R) : (84 / 85 : ℝ) ≤ factorThreshold r R := by
  have hRpos : 0 < R := by linarith
  have hd : 0 < 2 * r * R ^ 2 := by positivity
  unfold factorThreshold
  apply (le_div_iff₀ hd).2
  have h₁ : 0 ≤ (R - 1 / 2) * (R - r) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h₂ : 0 ≤ (r * R / 85) * (2 * R - 85) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [h₁, h₂]

theorem thresholdValues_bddBelow {r : ℝ} (hr : 0 < r) :
    BddBelow (thresholdValues r) := by
  refine ⟨84 / 85, ?_⟩
  rintro v ⟨R, hR, rfl⟩
  exact factorThreshold_lower_bound hr hR

theorem lower_bound_le_kappa {r : ℝ} (hr : 0 < r) :
    (84 / 85 : ℝ) ≤ kappa r := by
  apply le_csInf (thresholdValues_nonempty r)
  rintro v ⟨R, hR, rfl⟩
  exact factorThreshold_lower_bound hr hR

theorem kappa_le_factorThreshold {r R : ℝ} (hr : 0 < r)
    (hR : (85 / 2 : ℝ) ≤ R) : kappa r ≤ factorThreshold r R := by
  exact csInf_le (thresholdValues_bddBelow hr) ⟨R, hR, rfl⟩

theorem factorThreshold_self {r : ℝ} (hr : r ≠ 0) :
    factorThreshold r r = (r - 1 / 2) / r := by
  unfold factorThreshold
  field_simp
  ring

theorem kappa_lt_one {r : ℝ} (hr : (255 / 7 : ℝ) < r) : kappa r < 1 := by
  have hrpos : 0 < r := by linarith
  by_cases hR : (85 / 2 : ℝ) ≤ r
  · apply lt_of_le_of_lt (kappa_le_factorThreshold hrpos hR)
    rw [factorThreshold_self hrpos.ne']
    apply (div_lt_iff₀ hrpos).2
    linarith
  · apply lt_of_le_of_lt (kappa_le_factorThreshold hrpos (le_refl (85 / 2)))
    have hrhi : r < (85 / 2 : ℝ) := lt_of_not_ge hR
    have hprod : 0 < (r - 255 / 7) * (595 / 12 - r) :=
      mul_pos (by linarith) (by linarith)
    unfold factorThreshold
    apply (div_lt_iff₀ (by positivity : 0 < 2 * r * (85 / 2 : ℝ) ^ 2)).2
    nlinarith [hprod]

theorem neg_kappa_mem_Ioo {r : ℝ} (hr : (255 / 7 : ℝ) < r) :
    -kappa r ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hlow := lower_bound_le_kappa (by linarith : 0 < r)
  have hhigh := kappa_lt_one hr
  constructor <;> linarith

/-- For a zero below radius `85/2`, the lower height bound gives the stronger
comparison used to locate that zero relative to the infimum cutoff. -/
theorem factorThreshold_at_anchor_le {r : ℝ}
    (hr : (169 / 4 : ℝ) < r) (hhi : r ≤ (85 / 2 : ℝ)) :
    factorThreshold r (85 / 2) ≤ 169 / (2 * r) - 1 := by
  have hrpos : 0 < r := by linarith
  have hprod : 0 ≤ ((85 / 2 : ℝ) - r) * (42 * r + 10795 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hden : 0 < 2 * r * (85 / 2 : ℝ) ^ 2 := by positivity
  unfold factorThreshold
  apply (div_le_iff₀ hden).2
  have heq : (169 / (2 * r) - 1) * (2 * r * (85 / 2 : ℝ) ^ 2) =
      (169 - 2 * r) * (85 / 2 : ℝ) ^ 2 := by
    field_simp
  rw [heq]
  nlinarith [hprod]

/-- Every potential off-line zero lies strictly to the left of the exact
radius-dependent cutoff. Here `g` is its height and `h` its horizontal offset. -/
theorem square_angle_lt_neg_kappa {g h : ℝ}
    (hg : (169 / 4 : ℝ) < g ^ 2) (hh : h ^ 2 < (1 / 4 : ℝ)) :
    (h ^ 2 - g ^ 2) / (g ^ 2 + h ^ 2) < -kappa (g ^ 2 + h ^ 2) := by
  let r := g ^ 2 + h ^ 2
  have hr : (169 / 4 : ℝ) < r := by dsimp [r]; nlinarith [sq_nonneg h]
  have hrpos : 0 < r := by linarith
  suffices hk : kappa r < (g ^ 2 - h ^ 2) / r by
    change (h ^ 2 - g ^ 2) / r < -kappa r
    have heq : (h ^ 2 - g ^ 2) / r = -((g ^ 2 - h ^ 2) / r) := by ring
    rw [heq]
    exact neg_lt_neg hk
  by_cases hR : (85 / 2 : ℝ) ≤ r
  · apply lt_of_le_of_lt (kappa_le_factorThreshold hrpos hR)
    rw [factorThreshold_self hrpos.ne']
    apply (div_lt_div_iff_of_pos_right hrpos).2
    dsimp [r]
    nlinarith
  · have hhi : r ≤ (85 / 2 : ℝ) := le_of_lt (lt_of_not_ge hR)
    apply lt_of_le_of_lt ((kappa_le_factorThreshold hrpos (le_refl (85 / 2))).trans
      (factorThreshold_at_anchor_le hr hhi))
    have heq : 169 / (2 * r) - 1 = ((169 / 2 : ℝ) - r) / r := by
      field_simp
    rw [heq]
    apply (div_lt_div_iff_of_pos_right hrpos).2
    dsimp [r]
    nlinarith

end MisterPremise
