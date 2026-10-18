import AngularMaster.ActualProfile
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set Filter
open scoped Topology

namespace TaylorsProdigy

/-- Transport of strict positivity toward the critical endpoint. This is an
intermediate proposition, later proved from the finite-rate premise. -/
def AngularSlopePositivePropagatesLeft : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ Ioo (-1 : ℝ) 1,
    ∀ y ∈ Ioo (-1 : ℝ) 1, x ≤ y →
      0 < deriv (AngularMaster.actualProfile r) y →
      0 < deriv (AngularMaster.actualProfile r) x

/-- A squared-modulus zero is stationary. The conclusion uses the ordinary
derivative and does not assume an angular endpoint derivative. -/
theorem actual_slope_zero_of_profile_zero {r x : ℝ}
    (hz : AngularMaster.actualProfile r x = 0) :
    deriv (AngularMaster.actualProfile r) x = 0 := by
  have hm : IsLocalMin (AngularMaster.actualProfile r) x := by
    exact Filter.Eventually.of_forall (fun y => by
      rw [hz]
      exact AngularMaster.actualProfile_nonnegative_all r y)
  exact hm.deriv_eq_zero

/-- No external positive seed is needed: an alleged zero supplies, by analytic
uniqueness and the mean-value theorem, a positive slope to its right. -/
theorem actual_no_zero_on_interior_circle
    (htransport : AngularSlopePositivePropagatesLeft)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AWPIRH.theta (AngularMaster.circlePoint r x) ≠ 0 := by
  intro hz
  have hpx : AngularMaster.actualProfile r x = 0 := by
    simp [AngularMaster.actualProfile, AngularMaster.angularNormSq, hz]
  have hb : ∃ b ∈ Ioc x 1,
      AWPIRH.theta (AngularMaster.circlePoint r b) ≠ 0 := by
    by_contra hn
    have harc : ∀ b ∈ Icc x 1,
        AWPIRH.theta (AngularMaster.circlePoint r b) = 0 := by
      intro b hbb
      by_cases hbx : b = x
      · simpa [hbx] using hz
      · by_contra hne
        exact hn ⟨b, ⟨lt_of_le_of_ne hbb.1 (Ne.symm hbx), hbb.2⟩, hne⟩
    have hall := AngularMaster.entire_eq_zero_of_zero_arc AWPIRH.theta_entire
      (AngularMaster.continuous_circlePoint r)
      (AngularMaster.injective_circlePoint (ne_of_gt hr)) hx.2 harc
    exact AWPIRH.theta_one_ne_zero (by rw [hall]; rfl)
  obtain ⟨b, hb, hbn⟩ := hb
  have hpb : 0 < AngularMaster.actualProfile r b := by
    change 0 < Complex.normSq _
    exact Complex.normSq_pos.mpr hbn
  have hd : DifferentiableOn ℝ (AngularMaster.actualProfile r) (Ioo x b) := by
    apply (AngularMaster.actualProfile_interior_differentiable r hr).mono
    intro y hy
    exact ⟨hx.1.trans hy.1, hy.2.trans_le hb.2⟩
  obtain ⟨y, hy, hdy⟩ := exists_deriv_eq_slope (AngularMaster.actualProfile r)
    hb.1 (AngularMaster.actualProfile_continuous r).continuousOn hd
  have hpos : 0 < deriv (AngularMaster.actualProfile r) y := by
    rw [hdy, hpx, sub_zero]
    exact div_pos hpb (sub_pos.mpr hb.1)
  have hleft := htransport r hr x hx y
    ⟨hx.1.trans hy.1, hy.2.trans_le hb.2⟩ hy.1.le hpos
  rw [actual_slope_zero_of_profile_zero hpx] at hleft
  exact lt_irrefl 0 hleft

end TaylorsProdigy
