import Migration.ActualLocalPoleBinding

namespace Merger04.ForwardLocalPole

open NativeSoloboloNegativity Merger04.Migration Merger04.LocalPole

/--
The only remaining forward analytic theorem after the actual-zero and local-pole
construction have been derived.  It is deliberately local: no zero enumeration,
no summable global channel envelope, no Stieltjes representation and no Hadamard
product are part of the statement.

The intended proof is the parameterized symmetric-product Taylor identity plus
finite pole subtraction and a Cauchy coefficient bound.
-/
def ActualLocalPoleForcesDirectNegativity : Prop :=
  ∀ P : ActualXiInteriorSimplePole,
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      ∃ a : ℝ, a ∈ xiRegularAnchors ∧ xiWidderDirect a n < 0

/-- The local coefficient theorem converts the already-derived actual interior
    pole into eventual negativity for the endpoint-safe regularized profile. -/
theorem LOCAL_POLE_DOMINANCE_IMPLIES_REGULARIZED_EVENTUAL_NEGATIVITY
    (hlocal : ActualLocalPoleForcesDirectNegativity) :
    ¬ _root_.RiemannHypothesis →
      ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
        ∃ a : ℝ, 0 < a ∧ moment Merger04.Regularization.entireXi a n < 0 := by
  intro hnot
  rcases NOT_RH_GIVES_ACTUAL_XI_INTERIOR_SIMPLE_POLE hnot with ⟨P, _⟩
  rcases hlocal P with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro n hn
  rcases hK n hn with ⟨a, haReg, haNeg⟩
  refine ⟨a, haReg.1, ?_⟩
  rw [REGULARIZED_MOMENT_EQ_XI_DIRECT_ON_REGULAR_ANCHORS a haReg n]
  exact haNeg

/-- !!! Merger_04 forward reduction with the old global `ChannelPeakData`
    interface removed. -/
theorem FROZEN_US_IMPLIES_RH_FROM_LOCAL_POLE
    (hlocal : ActualLocalPoleForcesDirectNegativity)
    (hUS : NativeSoloboloContinuant.ActualCofinalUniformDepthPositive) :
    _root_.RiemannHypothesis := by
  have hReg : RegularizedUS := FROZEN_US_IMPLIES_REGULARIZED_US hUS
  by_contra hnot
  rcases LOCAL_POLE_DOMINANCE_IMPLIES_REGULARIZED_EVENTUAL_NEGATIVITY hlocal hnot with
    ⟨K, hK⟩
  rcases hReg K with ⟨N, hKN, hN⟩
  rcases hK N hKN with ⟨a, ha, hneg⟩
  exact (not_lt_of_ge (hN a ha)) hneg

/-- Exact contrapositive. -/
theorem NOT_RH_IMPLIES_NOT_FROZEN_US_FROM_LOCAL_POLE
    (hlocal : ActualLocalPoleForcesDirectNegativity) :
    ¬ _root_.RiemannHypothesis →
      ¬ NativeSoloboloContinuant.ActualCofinalUniformDepthPositive := by
  intro hnot hUS
  exact hnot (FROZEN_US_IMPLIES_RH_FROM_LOCAL_POLE hlocal hUS)

end Merger04.ForwardLocalPole
