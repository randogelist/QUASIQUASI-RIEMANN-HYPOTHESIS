import Migration.EndpointTransfer
import Bridge.UniformDepthPositivityRH04

namespace Merger04.Migration

open Merger04.Regularization

/-- This module imports the user's existing compiled frozen core. It does not
    redeclare, overwrite, or regularize any frozen definition. -/
theorem FROZEN_BASE_EQ_RAW_PROFILE :
    NativeSoloboloContinuant.actualWidderBase = baseMoment rawXi := rfl

theorem FROZEN_STEP_EQ_PROFILE (n : ℕ) (f : ℝ → ℝ) :
    NativeSoloboloContinuant.widderStep n f = step n f := rfl

/-- Structural induction checks the exact old recursive hierarchy. -/
theorem FROZEN_TOWER_EQ_RAW_PROFILE (n : ℕ) :
    NativeSoloboloContinuant.widderTower
        NativeSoloboloContinuant.actualWidderBase n =
      tower (baseMoment rawXi) n := by
  induction n with
  | zero => exact FROZEN_BASE_EQ_RAW_PROFILE
  | succ n ih =>
      change NativeSoloboloContinuant.widderStep n
          (NativeSoloboloContinuant.widderTower
            NativeSoloboloContinuant.actualWidderBase n) =
        step n (tower (baseMoment rawXi) n)
      rw [FROZEN_STEP_EQ_PROFILE, ih]

theorem FROZEN_MOMENT_EQ_RAW_PROFILE (a : ℝ) (n : ℕ) :
    NativeSoloboloContinuant.actualWidderMoment a n = moment rawXi a n := by
  exact congrFun (FROZEN_TOWER_EQ_RAW_PROFILE n) a

/-- Definitive equality check of the imported frozen US and the raw profile. -/
theorem FROZEN_US_IFF_RAW_PROFILE_US :
    NativeSoloboloContinuant.ActualCofinalUniformDepthPositive ↔ RawProfileUS := by
  constructor
  · intro h K
    obtain ⟨n, hnK, hn⟩ := h K
    refine ⟨n, hnK, ?_⟩
    intro a ha
    rw [← FROZEN_MOMENT_EQ_RAW_PROFILE a n]
    exact hn a ha
  · intro h K
    obtain ⟨n, hnK, hn⟩ := h K
    refine ⟨n, hnK, ?_⟩
    intro a ha
    rw [FROZEN_MOMENT_EQ_RAW_PROFILE a n]
    exact hn a ha

/-- The frozen source predicate remains unchanged. Only the forward migration
    is proved; the reverse exceptional-anchor behavior is not asserted. -/
theorem FROZEN_US_IMPLIES_REGULARIZED_US
    (hUS : NativeSoloboloContinuant.ActualCofinalUniformDepthPositive) :
    RegularizedUS := by
  exact RAW_PROFILE_US_IMPLIES_REGULARIZED_US
    (FROZEN_US_IFF_RAW_PROFILE_US.mp hUS)

end Merger04.Migration
