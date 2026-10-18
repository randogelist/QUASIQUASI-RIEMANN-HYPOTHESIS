import AngularMaster.ActualProfile

/-!
# Local angular positivity and zero exclusion

This module localizes the existing angular zero-exclusion argument from
`[-1, 1]` to `[a, 1]`. The actual-theta application retains angular positivity
as an explicit hypothesis; it assumes neither RH nor a zero-product identity.
-/

noncomputable section
open Set
open scoped ComplexConjugate

namespace AngularMaster

/-- On an increasing squared-modulus arc, a zero cannot occur strictly to the
right of the left endpoint. The proof uses an arc of zeros and analyticity. -/
theorem circle_ne_zero_of_angular_monotone_cutoff {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ w, f w ≠ 0)
    {a r x : ℝ} (hr : 0 < r) (hax : a < x) (hx1 : x ≤ 1)
    (hm : MonotoneOn (angularNormSq f r) (Icc a 1)) :
    f (circlePoint r x) ≠ 0 := by
  intro hz
  have harc : ∀ y ∈ Icc a x, f (circlePoint r y) = 0 := by
    intro y hy
    have hle := hm ⟨hy.1, hy.2.trans hx1⟩ ⟨hax.le, hx1⟩ hy.2
    have hnorm : angularNormSq f r x = 0 := by
      simp [angularNormSq, hz]
    rw [hnorm] at hle
    exact Complex.normSq_eq_zero.mp
      (le_antisymm hle (Complex.normSq_nonneg _))
  have hzero := entire_eq_zero_of_zero_arc hf (continuous_circlePoint r)
    (injective_circlePoint (ne_of_gt hr)) hax harc
  obtain ⟨w, hw⟩ := hne
  exact hw (by rw [hzero]; rfl)

/-- A localized angular monotonicity certificate excludes zeros in the full
conjugation-symmetric sector `a < re z / ‖z‖`. -/
theorem ne_zero_of_angular_monotone_cutoff {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ w, f w ≠ 0)
    (hconj : ∀ z, f z = 0 → f (conj z) = 0)
    {a : ℝ}
    (hm : ∀ r : ℝ, 0 < r → MonotoneOn (angularNormSq f r) (Icc a 1))
    {z : ℂ} (hz0 : z ≠ 0) (hx : a < z.re / ‖z‖) :
    f z ≠ 0 := by
  have hupper : ∀ w : ℂ, w ≠ 0 → 0 ≤ w.im →
      a < w.re / ‖w‖ → f w ≠ 0 := by
    intro w hw0 hwi hwx
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hx1 : w.re / ‖w‖ ≤ 1 := by
      apply (div_le_iff₀ hn).mpr
      simpa using (abs_le.mp (Complex.abs_re_le_norm w)).2
    have hnv := circle_ne_zero_of_angular_monotone_cutoff hf hne hn hwx hx1
      (hm ‖w‖ hn)
    rw [circlePoint_norm_re_div hw0 hwi] at hnv
    exact hnv
  by_cases hi : 0 ≤ z.im
  · exact hupper z hz0 hi hx
  · intro hz
    have hcz0 : conj z ≠ 0 := by
      intro h
      apply hz0
      have hc := congrArg conj h
      simpa using hc
    have hci : 0 ≤ (conj z).im := by
      simp only [Complex.conj_im]
      linarith
    have hcx : a < (conj z).re / ‖conj z‖ := by
      simpa using hx
    exact hupper (conj z) hcz0 hci hcx (hconj z hz)

/-- The original actual angular derivative is nonnegative above a cutoff.
Only interior angles are required; no endpoint derivative hypothesis is used. -/
def CutoffDerivativeNonnegative (a : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ Ioo a 1,
    0 ≤ angularDerivative actualProfile r x

/-- Actual interior derivative positivity supplies monotonicity on `[a,1]`.
Continuity at the endpoints comes from the existing entire-theta construction. -/
theorem actualProfile_monotoneOn_cutoff {a : ℝ}
    (ha : -1 ≤ a) (hderiv : CutoffDerivativeNonnegative a)
    (r : ℝ) (hr : 0 < r) :
    MonotoneOn (actualProfile r) (Icc a 1) := by
  have hint : DifferentiableOn ℝ (actualProfile r) (Ioo a 1) := by
    apply (actualProfile_interior_differentiable r hr).mono
    intro x hx
    exact ⟨lt_of_le_of_lt ha hx.1, hx.2⟩
  apply monotoneOn_of_deriv_nonneg (convex_Icc a 1)
    (actualProfile_continuous r).continuousOn
  · simpa only [interior_Icc] using hint
  · intro x hx
    have hxcut : x ∈ Ioo a 1 := by
      simpa only [interior_Icc] using hx
    have hxglobal : x ∈ Ioo (-1 : ℝ) 1 :=
      ⟨lt_of_le_of_lt ha hxcut.1, hxcut.2⟩
    have hd := hderiv r hr x hxcut
    change 0 ≤ derivWithin (actualProfile r) (Icc (-1) 1) x at hd
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hxglobal.1 hxglobal.2)] at hd
    exact hd

/-- Conditional zero exclusion for the actual Mathlib-backed theta on both
halves of the angular sector. Positivity is the sole research hypothesis. -/
theorem actual_theta_ne_zero_of_angular_cutoff {a : ℝ}
    (ha : -1 ≤ a) (hderiv : CutoffDerivativeNonnegative a)
    {z : ℂ} (hz0 : z ≠ 0) (hx : a < z.re / ‖z‖) :
    AWPIRH.theta z ≠ 0 := by
  exact ne_zero_of_angular_monotone_cutoff AWPIRH.theta_entire
    ⟨1, AWPIRH.theta_one_ne_zero⟩ (fun z hz => theta_zero_conj hz)
    (actualProfile_monotoneOn_cutoff ha hderiv) hz0 hx

end AngularMaster
