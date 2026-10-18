import Bridge.ActualWidderCore
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace NativeSoloboloContinuant

/-- Uniform positivity at one fixed actual Widder depth. -/
def ActualUniformDepthPositive (N : Nat) : Prop :=
  ∀ a : ℝ, 0 < a → 0 ≤ actualWidderMoment a N

/-- One positive depth at or beyond K. -/
def ActualUniformDepthPositiveBeyond (K : Nat) : Prop :=
  ∃ N : Nat, K ≤ N ∧ ActualUniformDepthPositive N

/-- Frozen Merger_04 source condition US. -/
def ActualCofinalUniformDepthPositive : Prop :=
  ∀ K : Nat, ActualUniformDepthPositiveBeyond K

/-- Eventual-negative obstruction pattern. -/
def ActualEventuallyDepthNegative : Prop :=
  ∃ K : Nat, ∀ N : Nat, K ≤ N →
    ∃ a : ℝ, 0 < a ∧ actualWidderMoment a N < 0

/-- One positive depth beyond an eventual-negativity threshold is impossible. -/
theorem ONE_UNIFORM_DEPTH_BEYOND_THRESHOLD_EXCLUDES_EVENTUAL_NEGATIVITY
    (K N : Nat)
    (hKN : K ≤ N)
    (hpos : ActualUniformDepthPositive N)
    (hneg : ∀ M : Nat, K ≤ M →
      ∃ a : ℝ, 0 < a ∧ actualWidderMoment a M < 0) :
    False := by
  rcases hneg N hKN with ⟨a, ha, hlt⟩
  exact (not_lt_of_ge (hpos a ha)) hlt

/-- US excludes the eventual-negative obstruction. -/
theorem COFINAL_UNIFORM_DEPTH_POSITIVITY_EXCLUDES_EVENTUAL_NEGATIVITY
    (hpos : ActualCofinalUniformDepthPositive) :
    ¬ ActualEventuallyDepthNegative := by
  rintro ⟨K, hneg⟩
  rcases hpos K with ⟨N, hKN, hN⟩
  exact ONE_UNIFORM_DEPTH_BEYOND_THRESHOLD_EXCLUDES_EVENTUAL_NEGATIVITY
    K N hKN hN hneg

end NativeSoloboloContinuant
