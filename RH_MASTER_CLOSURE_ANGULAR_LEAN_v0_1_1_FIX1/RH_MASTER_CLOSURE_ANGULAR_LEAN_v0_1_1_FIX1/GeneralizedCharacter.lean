import HausdorffKernel

namespace GPBKQRKernel

/-- Forward phase-free scale character. -/
noncomputable def forwardCharacter (sigma : ℝ) (n : ℕ) : ℝ :=
  (phaseFreeGain sigma) ^ n

/-- Backward phase-free scale character. -/
noncomputable def backwardCharacter (sigma : ℝ) (n : ℕ) : ℝ :=
  (phaseFreeGain (reflect sigma)) ^ n

/-- Exact one-step generalized eigencharacter recursion. -/
theorem forwardCharacter_succ (sigma : ℝ) (n : ℕ) :
    forwardCharacter sigma (n + 1) =
      phaseFreeGain sigma * forwardCharacter sigma n := by
  simp [forwardCharacter, pow_succ]
  ring

/-- Reflection turns the backward character into reciprocal powers. -/
theorem backwardCharacter_eq_inv_pow (sigma : ℝ) (n : ℕ) :
    backwardCharacter sigma n = ((phaseFreeGain sigma)⁻¹) ^ n := by
  simp [backwardCharacter, phaseFreeGain_reflect]

/-- Forward and backward values are exact reciprocals at every depth. -/
theorem forward_mul_backward (sigma : ℝ) (n : ℕ) :
    forwardCharacter sigma n * backwardCharacter sigma n = 1 := by
  rw [backwardCharacter_eq_inv_pow]
  unfold forwardCharacter
  have hne : phaseFreeGain sigma ≠ 0 := ne_of_gt (phaseFreeGain_pos sigma)
  rw [← mul_pow]
  simp [hne]

/-- Exact exponential type of the bilateral generalized character. -/
noncomputable def characterType (sigma : ℝ) : ℝ :=
  |Real.log (phaseFreeGain sigma)|

/-- Exponential type is precisely distance from the center, in dyadic units. -/
theorem characterType_formula (sigma : ℝ) :
    characterType sigma =
      2 * Real.log 2 * |centered sigma| := by
  unfold characterType
  rw [log_phaseFreeGain]
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    le_of_lt (Real.log_pos (by norm_num))
  rw [abs_mul, abs_mul, abs_of_nonneg hlog]
  norm_num
  ring

/-- Reflection preserves exponential type. -/
theorem characterType_reflect (sigma : ℝ) :
    characterType (reflect sigma) = characterType sigma := by
  rw [characterType_formula, characterType_formula, centered_reflect, abs_neg]

/-- Type vanishes exactly at the center. -/
theorem characterType_eq_zero_iff (sigma : ℝ) :
    characterType sigma = 0 ↔ sigma = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have hform := characterType_formula sigma
    rw [h] at hform
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have habs : |centered sigma| = 0 := by nlinarith
    have hc : centered sigma = 0 := abs_eq_zero.mp habs
    unfold centered at hc
    linarith
  · intro hs
    subst sigma
    simp [characterType, phaseFreeGain, centered, dyadicScale]

/-- Positive-direction exponential rate. -/
noncomputable def forwardRate (sigma : ℝ) : ℝ :=
  max (Real.log (phaseFreeGain sigma)) 0

/-- Negative-direction exponential rate. -/
noncomputable def backwardRate (sigma : ℝ) : ℝ :=
  max (- Real.log (phaseFreeGain sigma)) 0

/-- Signed rate difference is the exact logarithmic gain. -/
theorem forwardRate_sub_backwardRate (sigma : ℝ) :
    forwardRate sigma - backwardRate sigma =
      Real.log (phaseFreeGain sigma) := by
  unfold forwardRate backwardRate
  let x := Real.log (phaseFreeGain sigma)
  by_cases hx : 0 ≤ x
  · have hnx : -x ≤ 0 := neg_nonpos.mpr hx
    rw [max_eq_left hx, max_eq_right hnx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hnx : 0 ≤ -x := neg_nonneg.mpr hx'
    rw [max_eq_right hx', max_eq_left hnx]
    ring

/-- Sum of directional rates equals the bilateral exponential type. -/
theorem forwardRate_add_backwardRate (sigma : ℝ) :
    forwardRate sigma + backwardRate sigma = characterType sigma := by
  unfold forwardRate backwardRate characterType
  let x := Real.log (phaseFreeGain sigma)
  by_cases hx : 0 ≤ x
  · have hnx : -x ≤ 0 := neg_nonpos.mpr hx
    rw [max_eq_left hx, max_eq_right hnx, abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hnx : 0 ≤ -x := neg_nonneg.mpr hx'
    rw [max_eq_right hx', max_eq_left hnx, abs_of_nonpos hx']
    ring

/-- Exact signed recovery of the centered coordinate from the two directional rates. -/
theorem centered_eq_rate_difference (sigma : ℝ) :
    centered sigma =
      (forwardRate sigma - backwardRate sigma) / (2 * Real.log 2) := by
  rw [forwardRate_sub_backwardRate, log_phaseFreeGain]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog]

/-- Exact recovery of the original real coordinate. -/
theorem sigma_eq_half_add_rate_difference (sigma : ℝ) :
    sigma = (1 / 2 : ℝ) +
      (forwardRate sigma - backwardRate sigma) / (2 * Real.log 2) := by
  have hc := centered_eq_rate_difference sigma
  unfold centered at hc
  linarith

/-- A canonical weight strictly larger than the exact bilateral type. -/
noncomputable def canonicalRiggedWeight (sigma : ℝ) : ℝ :=
  characterType sigma + 1

/-- Canonical rigged weight has unit margin over the exact type. -/
theorem characterType_lt_canonicalRiggedWeight (sigma : ℝ) :
    characterType sigma < canonicalRiggedWeight sigma := by
  unfold canonicalRiggedWeight
  linarith

/-- Forward geometric ratio at the canonical rigged weight. -/
noncomputable def forwardRiggedRatio (sigma : ℝ) : ℝ :=
  Real.exp
    (2 * (Real.log (phaseFreeGain sigma) - canonicalRiggedWeight sigma))

/-- Backward geometric ratio at the canonical rigged weight. -/
noncomputable def backwardRiggedRatio (sigma : ℝ) : ℝ :=
  Real.exp
    (2 * (-Real.log (phaseFreeGain sigma) - canonicalRiggedWeight sigma))

/-- Forward rigged ratio lies strictly between zero and one. -/
theorem forwardRiggedRatio_mem_unit (sigma : ℝ) :
    0 ≤ forwardRiggedRatio sigma ∧ forwardRiggedRatio sigma < 1 := by
  constructor
  · exact le_of_lt (Real.exp_pos _)
  · apply (Real.exp_lt_one_iff).2
    unfold canonicalRiggedWeight characterType
    have hle : Real.log (phaseFreeGain sigma) ≤
        |Real.log (phaseFreeGain sigma)| := le_abs_self _
    linarith

/-- Backward rigged ratio lies strictly between zero and one. -/
theorem backwardRiggedRatio_mem_unit (sigma : ℝ) :
    0 ≤ backwardRiggedRatio sigma ∧ backwardRiggedRatio sigma < 1 := by
  constructor
  · exact le_of_lt (Real.exp_pos _)
  · apply (Real.exp_lt_one_iff).2
    unfold canonicalRiggedWeight characterType
    have hle : -Real.log (phaseFreeGain sigma) ≤
        |Real.log (phaseFreeGain sigma)| := neg_le_abs _
    linarith

/-- The canonical forward weighted square character is summable. -/
theorem canonical_forward_weighted_summable (sigma : ℝ) :
    Summable (fun n : ℕ => (forwardRiggedRatio sigma) ^ n) := by
  rcases forwardRiggedRatio_mem_unit sigma with ⟨h0, h1⟩
  exact summable_geometric_of_lt_one h0 h1

/-- The canonical backward weighted square character is summable. -/
theorem canonical_backward_weighted_summable (sigma : ℝ) :
    Summable (fun n : ℕ => (backwardRiggedRatio sigma) ^ n) := by
  rcases backwardRiggedRatio_mem_unit sigma with ⟨h0, h1⟩
  exact summable_geometric_of_lt_one h0 h1

end GPBKQRKernel
