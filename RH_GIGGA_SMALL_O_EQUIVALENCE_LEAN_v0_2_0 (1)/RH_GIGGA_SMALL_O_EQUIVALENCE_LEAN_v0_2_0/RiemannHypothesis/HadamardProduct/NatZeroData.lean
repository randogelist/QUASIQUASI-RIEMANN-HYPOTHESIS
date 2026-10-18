/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.LogDerivative

/-!
# Natural-number-indexed zero data

For a sequence indexed by `ℕ`, inverse-square summability and nonvanishing
already force the zero locations to escape every bounded set. This removes
the separate eventual-escape field from the public hypotheses of the paper's
sequential canonical-product theorems.
-/

namespace OverflowResidueRH

open Filter Topology

/-- Minimal inverse-square data for a natural-number-indexed nonzero zero
sequence. -/
structure NatHadamardZeroInvSqData (zeroLoc : ℕ → ℂ) : Prop where
  zero_ne : ∀ i : ℕ, zeroLoc i ≠ 0
  inv_sq_summable : Summable fun i : ℕ => (‖zeroLoc i‖ ^ 2)⁻¹

/-- Inverse-square summability of a nonzero sequence forces its norms to
escape every fixed bound along the cofinite filter. -/
theorem NatHadamardZeroInvSqData.eventually_large
    {zeroLoc : ℕ → ℂ} (H : NatHadamardZeroInvSqData zeroLoc)
    (s : ℂ) :
    ∀ᶠ i in Filter.cofinite, 2 * ‖s‖ ≤ ‖zeroLoc i‖ := by
  let R : ℝ := 2 * ‖s‖
  by_cases hR : R = 0
  · filter_upwards with i
    change R ≤ ‖zeroLoc i‖
    rw [hR]
    exact norm_nonneg (zeroLoc i)
  · have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      positivity
    have hR_pos : 0 < R := lt_of_le_of_ne hR_nonneg (Ne.symm hR)
    have heps_pos : 0 < (R ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hR_pos)
    have htendsto :
        Tendsto (fun i : ℕ => (‖zeroLoc i‖ ^ 2)⁻¹)
          Filter.cofinite (𝓝 0) :=
      H.inv_sq_summable.tendsto_cofinite_zero
    have hsmall :
        ∀ᶠ i : ℕ in Filter.cofinite,
          (‖zeroLoc i‖ ^ 2)⁻¹ < (R ^ 2)⁻¹ :=
      htendsto.eventually_lt_const heps_pos
    filter_upwards [hsmall] with i hi
    have hnorm_pos : 0 < ‖zeroLoc i‖ := norm_pos_iff.mpr (H.zero_ne i)
    have hsquare : R ^ 2 < ‖zeroLoc i‖ ^ 2 :=
      (inv_lt_inv₀ (sq_pos_of_pos hnorm_pos) (sq_pos_of_pos hR_pos)).mp hi
    have hlt : R < ‖zeroLoc i‖ := by nlinarith
    exact le_of_lt (by simpa [R] using hlt)

/-- Minimal natural-number-indexed data supplies the general Hadamard zero
package; eventual escape is derived rather than assumed. -/
theorem NatHadamardZeroInvSqData.toHadamardZeroInvSqSummability
    {zeroLoc : ℕ → ℂ} (H : NatHadamardZeroInvSqData zeroLoc) :
    HadamardZeroInvSqSummability zeroLoc :=
  { zero_ne := H.zero_ne
    inv_sq_summable := H.inv_sq_summable
    eventually_large := H.eventually_large }

end OverflowResidueRH
