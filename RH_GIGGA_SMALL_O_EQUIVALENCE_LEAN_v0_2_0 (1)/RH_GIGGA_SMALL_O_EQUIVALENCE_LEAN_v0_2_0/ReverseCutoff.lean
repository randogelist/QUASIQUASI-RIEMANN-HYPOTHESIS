import RHSmallO
import Mathlib.Topology.Algebra.Order.Field

/-!
Under the native Riemann hypothesis every actual opposite-pair occurrence
lies on the real pullback axis.  Its fixed positive height is eventually
included in the cutoff as the radius tends to zero through positive values.
The already proved summable spectral weights dominate all cutoff terms.
-/

noncomputable section
open Filter Set
open scoped Classical Topology BigOperators

namespace RHSmallO

open AngularMaster OverflowResidueRH

/-- Native RH makes every actual opposite-pair representative real. -/
theorem all_representatives_real_of_native_RH
    (hRH : _root_.RiemannHypothesis) (i : SpectralIndex) :
    (actualPairZero i).im = 0 := by
  exact riemannHypothesis_iff_entireXiPullback_zeros_real.mp hRH _
    (entireXiPullbackZeroOccurrenceLoc_is_zero _)

/-- A fixed height is eventually included in the cutoff `1/r`. -/
theorem eventually_height_le_cutoff (i : SpectralIndex) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ‖actualPairZero i‖ ≤ 1 / r := by
  have h := (tendsto_inv_nhdsGT_zero :
      Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] 0) atTop).eventually
    (eventually_ge_atTop ‖actualPairZero i‖)
  simpa only [one_div] using h

/-- Under RH each cutoff summand eventually equals its full spectral weight. -/
theorem criticalLineCutoffTerm_eventually_eq_of_RH
    (hRH : _root_.RiemannHypothesis) (i : SpectralIndex) :
    (fun r : ℝ => criticalLineCutoffTerm r i) =ᶠ[𝓝[>] 0]
      fun _ => spectralWeight i := by
  filter_upwards [eventually_height_le_cutoff i] with r hr
  exact if_pos ⟨all_representatives_real_of_native_RH hRH i, hr⟩

/-- The actual finite critical-line cutoff saturates the origin trace under RH. -/
theorem cutoff_tendsto_of_RH (hRH : _root_.RiemannHypothesis) :
    Tendsto criticalLineCutoff (𝓝[>] 0) (𝓝 q1) := by
  classical
  have htrace : q1 = ∑' i : SpectralIndex, spectralWeight i := by
    simpa only [q1, spectralWeight] using
      actual_theta_origin_real_trace
  have hupper (r : ℝ) : criticalLineCutoff r ≤ q1 := by
    rw [htrace]
    exact (criticalLineCutoffTerm_summable r).tsum_le_tsum
      (criticalLineCutoffTerm_le r) spectralWeight_summable
  have hsum : Tendsto (fun s : Finset SpectralIndex => ∑ i ∈ s, spectralWeight i)
      atTop (𝓝 q1) := by
    rw [htrace]
    exact spectralWeight_summable.hasSum
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs⟩ := ((Metric.tendsto_nhds.mp hsum) ε hε).exists
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ i ∈ s, criticalLineCutoffTerm r i = spectralWeight i :=
    (s.eventually_all).mpr
      (fun i _ => criticalLineCutoffTerm_eventually_eq_of_RH hRH i)
  filter_upwards [hev] with r hr
  have hlower : (∑ i ∈ s, spectralWeight i) ≤ criticalLineCutoff r := by
    calc
      _ = ∑ i ∈ s, criticalLineCutoffTerm r i :=
        Finset.sum_congr rfl (fun i hi => (hr i hi).symm)
      _ ≤ _ := (criticalLineCutoffTerm_summable r).sum_le_tsum s
        (fun i _ => criticalLineCutoffTerm_nonneg r i)
  rw [Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (hupper r))]
  have hs' : q1 - (∑ i ∈ s, spectralWeight i) < ε := by
    rw [Real.dist_eq] at hs
    have hle := neg_le_abs ((∑ i ∈ s, spectralWeight i) - q1)
    linarith
  linarith

end RHSmallO
