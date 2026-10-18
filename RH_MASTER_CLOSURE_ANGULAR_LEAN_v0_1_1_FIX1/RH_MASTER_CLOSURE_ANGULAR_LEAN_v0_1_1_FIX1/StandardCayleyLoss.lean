import CayleyConstruction

namespace GPBKQRKernel

/-- The incoming/reference energy attached to arbitrary complex jet data. -/
noncomputable def jetEnergyMinus (Y2 : ℂ) : ℝ :=
  2 * ‖Y2‖ ^ 2

/-- The outgoing/two-scale energy attached to arbitrary complex jet data. -/
noncomputable def jetEnergyPlus (Y2 Y4 : ℂ) : ℝ :=
  ‖Y4 - 2 * Y2‖ ^ 2

/-- Total two-port jet energy. -/
noncomputable def jetTotalEnergy (Y2 Y4 : ℂ) : ℝ :=
  jetEnergyPlus Y2 Y4 + jetEnergyMinus Y2

/-- Signed imbalance between the two jet energies. -/
noncomputable def jetEnergyImbalance (Y2 Y4 : ℂ) : ℝ :=
  jetEnergyPlus Y2 Y4 - jetEnergyMinus Y2

/-- The standard Cayley loss of arbitrary complex two-scale jet data.

This definition is completely independent of zeta, RH, passivity, or a
literal `K₂` realization.  If the total energy vanishes, Lean's field
convention makes the quotient zero. -/
noncomputable def jetCayleyLoss (Y2 Y4 : ℂ) : ℝ :=
  (jetEnergyImbalance Y2 Y4) ^ 2 / jetTotalEnergy Y2 Y4

/-- The reference jet energy is nonnegative without a premise. -/
theorem jetEnergyMinus_nonneg (Y2 : ℂ) :
    0 ≤ jetEnergyMinus Y2 := by
  unfold jetEnergyMinus
  positivity

/-- The outgoing jet energy is nonnegative without a premise. -/
theorem jetEnergyPlus_nonneg (Y2 Y4 : ℂ) :
    0 ≤ jetEnergyPlus Y2 Y4 := by
  unfold jetEnergyPlus
  positivity

/-- Total jet energy is nonnegative without a premise. -/
theorem jetTotalEnergy_nonneg (Y2 Y4 : ℂ) :
    0 ≤ jetTotalEnergy Y2 Y4 := by
  unfold jetTotalEnergy
  exact add_nonneg (jetEnergyPlus_nonneg Y2 Y4) (jetEnergyMinus_nonneg Y2)

/-- A nonzero first jet makes the reference energy strictly positive. -/
theorem jetEnergyMinus_pos {Y2 : ℂ} (hY2 : Y2 ≠ 0) :
    0 < jetEnergyMinus Y2 := by
  unfold jetEnergyMinus
  have hnorm : 0 < ‖Y2‖ := norm_pos_iff.mpr hY2
  positivity

/-- A nonzero first jet makes the total two-port energy strictly positive. -/
theorem jetTotalEnergy_pos {Y2 Y4 : ℂ} (hY2 : Y2 ≠ 0) :
    0 < jetTotalEnergy Y2 Y4 := by
  unfold jetTotalEnergy
  have hplus : 0 ≤ jetEnergyPlus Y2 Y4 := jetEnergyPlus_nonneg Y2 Y4
  have hminus : 0 < jetEnergyMinus Y2 := jetEnergyMinus_pos hY2
  linarith

/-- **Frozen A-Tier-Anchoring-03 standard endpoint.**

For arbitrary complex jet data, the explicitly constructed Cayley loss is
nonnegative.  There are no hypotheses: in particular no RH, zero predicate,
passivity, contractivity, saturation, or analytic `K₂` binding is used. -/
theorem jetCayleyLoss_nonneg (Y2 Y4 : ℂ) :
    0 ≤ jetCayleyLoss Y2 Y4 := by
  unfold jetCayleyLoss
  exact div_nonneg (sq_nonneg (jetEnergyImbalance Y2 Y4))
    (jetTotalEnergy_nonneg Y2 Y4)

/-- Vanishing energy imbalance gives zero Cayley loss.  This is an algebraic
one-way statement only; no claim is made that any actual Riemann jet is
balanced. -/
theorem jetCayleyLoss_eq_zero_of_balance {Y2 Y4 : ℂ}
    (hbalance : jetEnergyPlus Y2 Y4 = jetEnergyMinus Y2) :
    jetCayleyLoss Y2 Y4 = 0 := by
  unfold jetCayleyLoss jetEnergyImbalance
  rw [hbalance]
  simp

/-- Premise-free certificate collecting the standard loss anchor. -/
theorem standardCayleyLossAnchor_certificate (Y2 Y4 : ℂ) :
    0 ≤ jetEnergyMinus Y2 ∧
    0 ≤ jetEnergyPlus Y2 Y4 ∧
    0 ≤ jetTotalEnergy Y2 Y4 ∧
    0 ≤ jetCayleyLoss Y2 Y4 := by
  exact ⟨jetEnergyMinus_nonneg Y2,
    jetEnergyPlus_nonneg Y2 Y4,
    jetTotalEnergy_nonneg Y2 Y4,
    jetCayleyLoss_nonneg Y2 Y4⟩

end GPBKQRKernel
