import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
A general analytic zero-exclusion theorem behind angular monotonicity.
No assertion about the location of zeros is assumed: the proof uses the identity
principle for analytic functions and the real part of the circle parameter.
-/

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

namespace AngularMaster

/-- Upper semicircle, parametrized by the normalized real coordinate. -/
def circlePoint (r x : ℝ) : ℂ :=
  (r : ℂ) * ((x : ℂ) + Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ))

/-- Squared modulus on a circle, in angular coordinate `x = cos θ`. -/
def angularNormSq (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  Complex.normSq (f (circlePoint r x))

@[simp] theorem circlePoint_re (r x : ℝ) : (circlePoint r x).re = r * x := by
  simp [circlePoint, Complex.mul_re]

@[simp] theorem circlePoint_im (r x : ℝ) :
    (circlePoint r x).im = r * Real.sqrt (1 - x ^ 2) := by
  simp [circlePoint, Complex.mul_im]

theorem continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
  unfold circlePoint
  continuity

theorem injective_circlePoint {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (circlePoint r) := by
  intro x y h
  have h' := congrArg Complex.re h
  simp only [circlePoint_re] at h'
  exact mul_left_cancel₀ hr h'

/-- A nonconstant continuous injective arc of zeros forces an entire function
    to vanish identically. This is the only analytic uniqueness input. -/
theorem entire_eq_zero_of_zero_arc {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hinj : Function.Injective γ) {a b : ℝ} (hab : a < b)
    (hz : ∀ x ∈ Icc a b, f (γ x) = 0) : f = 0 := by
  have ht : Tendsto γ (𝓝[>] a) (𝓝[≠] γ a) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    change γ x ≠ γ a
    exact fun h => (ne_of_gt hx) (hinj h)
  have he : ∀ᶠ x in 𝓝[>] a, f (γ x) = 0 := by
    have hb : ∀ᶠ x in 𝓝[>] a, x < b :=
      nhdsWithin_le_nhds (eventually_lt_nhds hab)
    filter_upwards [self_mem_nhdsWithin, hb] with x hx hxb
    exact hz x ⟨le_of_lt hx, le_of_lt hxb⟩
  exact hf.eq_of_frequently_eq analyticOnNhd_const (ht.frequently he.frequently)

/-- Under angular monotonicity, the only possible zero on the upper semicircle
    is at its left endpoint. -/
theorem circle_zero_only_left {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ w, f w ≠ 0)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Icc (-1) 1)
    (hm : MonotoneOn (angularNormSq f r) (Icc (-1) 1))
    (hz : f (circlePoint r x) = 0) : x = -1 := by
  by_contra hxa
  have hlt : -1 < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
  have harc : ∀ y ∈ Icc (-1) x, f (circlePoint r y) = 0 := by
    intro y hy
    have hle := hm ⟨hy.1, hy.2.trans hx.2⟩ hx hy.2
    have hnorm : angularNormSq f r x = 0 := by simp [angularNormSq, hz]
    rw [hnorm] at hle
    exact Complex.normSq_eq_zero.mp (le_antisymm hle (Complex.normSq_nonneg _))
  have hzero := entire_eq_zero_of_zero_arc hf (continuous_circlePoint r)
    (injective_circlePoint (ne_of_gt hr)) hlt harc
  obtain ⟨w, hw⟩ := hne
  exact hw (by rw [hzero]; rfl)

/-- Every point of the closed upper half-plane except zero has this circle
    representation. -/
theorem circlePoint_norm_re_div {z : ℂ} (hz : z ≠ 0) (hi : 0 ≤ z.im) :
    circlePoint ‖z‖ (z.re / ‖z‖) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn0 : ‖z‖ ≠ 0 := ne_of_gt hn
  have hsq : 1 - (z.re / ‖z‖) ^ 2 = (z.im / ‖z‖) ^ 2 := by
    have h := Complex.sq_norm_sub_sq_re z
    field_simp [hn0]
    nlinarith
  have hsqrt : Real.sqrt (1 - (z.re / ‖z‖) ^ 2) = z.im / ‖z‖ := by
    rw [hsq, Real.sqrt_sq (div_nonneg hi hn.le)]
  apply Complex.ext
  · simp only [circlePoint_re]
    field_simp [hn0]
  · simp only [circlePoint_im, hsqrt]
    field_simp [hn0]

/-- The angular monotonicity criterion excludes every zero away from the
    nonpositive real axis. -/
theorem zeros_nonpositive_of_angular_monotone {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ w, f w ≠ 0)
    (hconj : ∀ z, f z = 0 → f (conj z) = 0)
    (hm : ∀ r : ℝ, 0 < r → MonotoneOn (angularNormSq f r) (Icc (-1) 1)) :
    ∀ z : ℂ, f z = 0 → z.im = 0 ∧ z.re ≤ 0 := by
  have hupper : ∀ z : ℂ, 0 ≤ z.im → f z = 0 → z.im = 0 ∧ z.re ≤ 0 := by
    intro z hi hz
    by_cases hz0 : z = 0
    · subst z
      simp
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hbounds := abs_le.mp (Complex.abs_re_le_norm z)
    have hx : z.re / ‖z‖ ∈ Icc (-1 : ℝ) 1 := by
      constructor
      · apply (le_div_iff₀ hn).mpr
        simpa using hbounds.1
      · apply (div_le_iff₀ hn).mpr
        simpa using hbounds.2
    have hrepr := circlePoint_norm_re_div hz0 hi
    have hleft := circle_zero_only_left hf hne hn hx (hm ‖z‖ hn) (by rw [hrepr]; exact hz)
    have hre : z.re = -‖z‖ := by
      have h := (div_eq_iff (ne_of_gt hn)).mp hleft
      linarith
    have him : z.im = 0 := by
      have h := Complex.sq_norm_sub_sq_re z
      rw [hre] at h
      nlinarith [sq_nonneg z.im]
    exact ⟨him, by rw [hre]; exact neg_nonpos.mpr hn.le⟩
  intro z hz
  by_cases hi : 0 ≤ z.im
  · exact hupper z hi hz
  · have hcz : f (conj z) = 0 := hconj z hz
    have hci : 0 ≤ (conj z).im := by simp; linarith
    have h := hupper (conj z) hci hcz
    simpa using h

end AngularMaster
