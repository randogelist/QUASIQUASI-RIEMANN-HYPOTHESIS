import AngularMaster.QQRHUnconditional
import AngularMaster.AnalyticExtension
import AngularMaster.SecondFullXAnchor

/-! Public QQRH interface. All analytic definitions and proofs are included. -/

noncomputable section

/-- Actual-zeta zero exclusion in the critical-strip wedge of slope `m`. -/
abbrev QQRH (m : ℝ) : Prop := AngularMaster.QQRH m

namespace QQRH

abbrev cutoff (m : ℝ) : ℝ := AngularMaster.slopeCutoff m
abbrev profile (r x : ℝ) : ℝ := AngularMaster.actualProfile r x

theorem cutoff_two : cutoff 2 = -(3 / 5 : ℝ) :=
  AngularMaster.slopeCutoff_two

/-- The general construction from the actual angular derivative certificate. -/
theorem of_positivity {m : ℝ} (hm : 0 < m)
    (hP : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      cutoff m < x → x < 1 → 0 ≤ deriv (profile r) x) :
    _root_.QQRH m :=
  AngularMaster.QQRH_of_deriv_nonnegative hm hP

/-- Unconditional slope-two positivity for the actual entire-theta profile. -/
theorem positivity_two (r : ℝ) (hr : 0 < r) (x : ℝ)
    (hx : -(3 / 5 : ℝ) < x) (hx1 : x < 1) :
    0 ≤ deriv (profile r) x :=
  AngularMaster.actual_deriv_nonnegative_above_neg_three_fifths r hr x hx hx1

/-- QQRH(2), through the positivity construction, with no research premise. -/
theorem two : _root_.QQRH 2 := by
  apply of_positivity (by norm_num : (0 : ℝ) < 2)
  simpa only [cutoff_two] using positivity_two

theorem cutoff_ten : cutoff 10 = -(99 / 101 : ℝ) :=
  AngularMaster.slopeCutoff_ten

theorem cutoff_eleven : cutoff 11 = -(60 / 61 : ℝ) :=
  AngularMaster.slopeCutoff_eleven

/-- The analytic extension of the actual angular derivative certificate. -/
theorem positivity_eleven (r : ℝ) (hr : 0 < r) (x : ℝ)
    (hx : -(60 / 61 : ℝ) < x) (hx1 : x < 1) :
    0 ≤ deriv (profile r) x :=
  AngularMaster.actual_deriv_nonnegative_above_neg_sixty_sixtyone r hr x hx hx1

/-- QQRH(11), explicitly constructed from the proved positivity theorem. -/
theorem eleven : _root_.QQRH 11 := by
  apply of_positivity (by norm_num : (0 : ℝ) < 11)
  simpa only [cutoff_eleven] using positivity_eleven

theorem positivity_ten (r : ℝ) (hr : 0 < r) (x : ℝ)
    (hx : -(99 / 101 : ℝ) < x) (hx1 : x < 1) :
    0 ≤ deriv (profile r) x :=
  positivity_eleven r hr x (by linarith) hx1

theorem ten : _root_.QQRH 10 := by
  apply of_positivity (by norm_num : (0 : ℝ) < 10)
  simpa only [cutoff_ten] using positivity_ten

/-- The quantitative family supported by the analytic bound, via positivity. -/
theorem of_sq_lt_122 {m : ℝ} (hm : 1 ≤ m) (hcap : m ^ 2 < 122) :
    _root_.QQRH m :=
  AngularMaster.QQRH_of_sq_lt_122 hm hcap

/-- Exact radius of the second full-x-range anchor. -/
abbrev secondFullXRadius : ℝ := AngularMaster.secondFullXRadius

theorem second_full_x_radius : secondFullXRadius = (255 / 7 : ℝ) := rfl

/-- Full closed angular interval at every positive radius up to `255/7`. -/
theorem second_full_x_monotone (r : ℝ) (hr : 0 < r)
    (hR : r ≤ 255 / 7) : MonotoneOn (profile r) (Set.Icc (-1) 1) :=
  AngularMaster.actualProfile_second_full_x_monotone hr hR

/-- Second full-x-range anchor: unconditional actual angular positivity. -/
theorem second_full_x_range_anchor (r : ℝ) (hr : 0 < r)
    (hR : r ≤ 255 / 7) (x : ℝ) (hx : -1 < x) (hx1 : x < 1) :
    0 ≤ deriv (profile r) x :=
  AngularMaster.actual_deriv_second_full_x_anchor hr hR hx hx1

/-- Strict profile positivity, including both angular endpoints and radius zero. -/
theorem second_full_x_positive (r : ℝ) (hr : 0 ≤ r)
    (hR : r ≤ 255 / 7) (x : ℝ) (hx : -1 ≤ x) (hx1 : x ≤ 1) :
    0 < profile r x :=
  AngularMaster.actualProfile_second_full_x_pos hr hR hx hx1

end QQRH
