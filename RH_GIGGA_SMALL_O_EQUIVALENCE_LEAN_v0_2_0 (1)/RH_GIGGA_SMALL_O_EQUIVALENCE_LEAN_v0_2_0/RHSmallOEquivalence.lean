import ReverseCutoff
import ScalarConverse

/-!
# The angular little-o premise is equivalent to native RH

The forward implication is the previously verified closure. The reverse
implication uses the same concrete integral and finite multiplicity-bearing
critical-line cutoffs; no further input is introduced.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RHSmallO

/-- RH implies precisely the angular little-o premise used in the closure. -/
theorem small_o_of_rh (hRH : _root_.RiemannHypothesis) : SmallOPremise := by
  exact RHScalarLittleO.isLittleO_of_normalized_integral_and_cutoff_tendsto
    I criticalLineCutoff q1 normalized_integral_tendsto
    (cutoff_tendsto_of_RH hRH)

/-- The sole research premise is equivalent to Mathlib's literal RH. -/
theorem small_o_iff_RH : SmallOPremise ↔ _root_.RiemannHypothesis :=
  ⟨rh_of_small_o, small_o_of_rh⟩

/-- Native RH is equivalent to the concrete angular little-o remainder. -/
theorem rh_iff_small_o : _root_.RiemannHypothesis ↔ SmallOPremise :=
  small_o_iff_RH.symm

/-- The equivalence with the literal angular integral hypothesis expanded. -/
theorem rh_iff_angular_integral_isLittleO :
    _root_.RiemannHypothesis ↔
      (fun r : ℝ => AngularMaster.angularI r - Real.pi * r * criticalLineCutoff r)
        =o[𝓝[>] 0] (fun r : ℝ => r) := by
  exact rh_iff_small_o

end RHSmallO
