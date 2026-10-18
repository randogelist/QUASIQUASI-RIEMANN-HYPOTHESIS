import ScalarLittleO

/-!
The converse scalar limit calculation for the same literal little-o premise.
This helper has no number-theoretic assumptions; the native endpoint supplies
both limits from proved analytic results and the Riemann hypothesis.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RHScalarLittleO

/-- Matching normalized integral and cutoff limits give the little-o remainder. -/
theorem isLittleO_of_normalized_integral_and_cutoff_tendsto
    (I S : ℝ → ℝ) (q : ℝ)
    (hI : Tendsto (fun r => I r / r) zeroRight (𝓝 (Real.pi * q)))
    (hS : Tendsto S zeroRight (𝓝 q)) :
    (fun r => I r - Real.pi * r * S r) =o[zeroRight] (fun r : ℝ => r) := by
  have hquot : Tendsto (fun r => I r / r - Real.pi * S r)
      zeroRight (𝓝 0) := by
    simpa using hI.sub ((tendsto_const_nhds (x := Real.pi)).mul hS)
  have heq : (fun r => I r / r - Real.pi * S r) =ᶠ[zeroRight]
      (fun r => (I r - Real.pi * r * S r) / r) := by
    filter_upwards [eventually_pos_zeroRight] with r hr
    field_simp [ne_of_gt hr]
  have hgf : ∀ᶠ r : ℝ in zeroRight, r = 0 → I r - Real.pi * r * S r = 0 := by
    filter_upwards [eventually_pos_zeroRight] with r hr hz
    exact (ne_of_gt hr hz).elim
  exact (Asymptotics.isLittleO_iff_tendsto' hgf).2 (hquot.congr' heq)

end RHScalarLittleO
