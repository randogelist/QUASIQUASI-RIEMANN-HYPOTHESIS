import AngularMaster.ActualProfile

/-!
The exact Riemann normalization can be used without first assuming that its
real-axis denominator never vanishes.  The Master implies angular monotonicity
at every regular radius; analyticity makes those radii dense, and continuity
extends monotonicity to all radii.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace AngularMaster

/-- The frozen Riemann denominator, expressed by a real nonnegative norm. -/
def frozenNormalizer (r : ℝ) : ℝ := ‖AWPIRH.theta (r : ℂ)‖

/-- Both original frozen logarithmic Master inequalities. -/
def frozenLogMaster (ε : ℝ) : Prop := LogMaster ε frozenNormalizer actualProfile

/-- Nonzero entire theta cannot vanish on any interval of the real axis. -/
theorem theta_real_nonzero_frequently (r : ℝ) :
    ∃ᶠ (t : ℝ) in 𝓝 r, AWPIRH.theta (t : ℂ) ≠ 0 := by
  by_contra hn
  have he : ∀ᶠ (t : ℝ) in 𝓝 r, AWPIRH.theta (t : ℂ) = 0 := by
    simpa only [not_not] using (not_frequently.mp hn)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hz : ∀ t ∈ Icc (r - δ / 2) (r + δ / 2), AWPIRH.theta (t : ℂ) = 0 := by
    intro t ht
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hzero := entire_eq_zero_of_zero_arc AWPIRH.theta_entire
    Complex.continuous_ofReal Complex.ofReal_injective (by linarith : r - δ / 2 < r + δ / 2) hz
  exact AWPIRH.theta_one_ne_zero (by rw [hzero]; rfl)

theorem actualProfile_radial_continuous (x : ℝ) :
    Continuous (fun r : ℝ => actualProfile r x) := by
  have hc : Continuous (fun r : ℝ => circlePoint r x) := by
    unfold circlePoint
    fun_prop
  exact Complex.continuous_normSq.comp (AWPIRH.theta_continuous.comp hc)

/-- At a regular radius, the frozen Master gives ordinary angular monotonicity. -/
theorem frozen_logMaster_monotone_at_regular_radius {ε r : ℝ}
    (hε : 0 < ε) (h : frozenLogMaster ε) (hr : 0 < r)
    (hne : AWPIRH.theta (r : ℂ) ≠ 0) :
    MonotoneOn (actualProfile r) angularInterval := by
  have hS : 0 < frozenNormalizer r := norm_pos_iff.mpr hne
  apply monotoneOn_of_deriv_nonneg (convex_Icc (-1 : ℝ) 1)
    (actualProfile_continuousOn r hr)
  · simpa only [angularInterval, interior_Icc] using actualProfile_interior_differentiable r hr
  · intro x hx
    have hxi : x ∈ Ioo (-1 : ℝ) 1 := by
      simpa only [angularInterval, interior_Icc] using hx
    have hxc : x ∈ angularInterval := ⟨hxi.1.le, hxi.2.le⟩
    have hdiff : DifferentiableWithinAt ℝ (actualProfile r) angularInterval x :=
      ((actualProfile_interior_differentiable r hr x hxi).differentiableAt
        (isOpen_Ioo.mem_nhds hxi)).differentiableWithinAt
    have hflux : 0 ≤ masterFlux ε frozenNormalizer actualProfile r x :=
      (h r hr x hxc).2.trans (h r hr x hxc).1
    have hd := (masterFlux_nonnegative_iff hε hS
      (actualProfile_nonnegative_all r x) hxc hdiff).mp hflux
    change 0 ≤ derivWithin (actualProfile r) (Icc (-1) 1) x at hd
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hxi.1 hxi.2)] at hd
    exact hd

/-- Continuity in radius removes possible zero denominators from the reverse
    implication. No nonvanishing assumption is required here. -/
theorem frozen_logMaster_angular_monotone {ε : ℝ}
    (hε : 0 < ε) (h : frozenLogMaster ε) :
    ∀ r : ℝ, 0 < r → MonotoneOn (actualProfile r) angularInterval := by
  intro r hr x hx y hy hxy
  have hf : ∃ᶠ (t : ℝ) in 𝓝 r, AWPIRH.theta (t : ℂ) ≠ 0 ∧ 0 < t :=
    (theta_real_nonzero_frequently r).and_eventually (eventually_gt_nhds hr)
  have hle : ∃ᶠ (t : ℝ) in 𝓝 r, actualProfile t x ≤ actualProfile t y :=
    hf.mono fun t ht => frozen_logMaster_monotone_at_regular_radius hε h ht.2 ht.1 hx hy hxy
  exact le_of_tendsto_of_tendsto_of_frequently
    (actualProfile_radial_continuous x).continuousAt.tendsto
    (actualProfile_radial_continuous y).continuousAt.tendsto hle

/-- The exact frozen Riemann logarithmic Master implies native RH with no
    positive-denominator hypothesis. -/
theorem frozen_logMaster_implies_native_RH {ε : ℝ}
    (hε : 0 < ε) (h : frozenLogMaster ε) : _root_.RiemannHypothesis :=
  native_RH_of_actual_angular_monotone (frozen_logMaster_angular_monotone hε h)

/-- RH itself rules out any denominator zero at positive real radius. -/
theorem frozenNormalizer_positive_of_native_RH (hRH : _root_.RiemannHypothesis) :
    NormalizerPositive frozenNormalizer := by
  intro r hr
  apply norm_pos_iff.mpr
  intro hz
  have hloc := (native_RH_iff_theta_zeros_nonpositive.mp hRH) (r : ℂ) hz
  have hnonpos : r ≤ 0 := by simpa using hloc.2
  exact (not_le_of_gt hr) hnonpos

end AngularMaster
