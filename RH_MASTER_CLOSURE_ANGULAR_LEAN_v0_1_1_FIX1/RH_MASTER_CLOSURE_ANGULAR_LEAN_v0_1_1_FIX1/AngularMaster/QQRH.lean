import AngularMaster.AngularCutoff
import AngularMaster.QQRHGeometry

/-!
# QQRH from angular positivity

This is the conditional implication requested for the actual theta profile.
The sign condition is an explicit premise. No RH hypothesis is used, and
this module does not assert the sign condition unconditionally.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

/-- Angular positivity above the slope cutoff excludes actual zeta zeros in
the corresponding critical-strip wedge. -/
theorem QQRH_of_angular_positivity {m : ℝ} (hm : 0 < m)
    (hP : CutoffDerivativeNonnegative (slopeCutoff m)) : QQRH m := by
  apply QQRH_of_theta_sector_nonvanishing hm
  intro z hz hx
  exact actual_theta_ne_zero_of_angular_cutoff
    (slopeCutoff_mem_Ioo hm).1.le hP hz hx

/-- The same implication using the ordinary derivative on the open interval,
exactly as in the displayed mathematical criterion. -/
theorem QQRH_of_deriv_nonnegative {m : ℝ} (hm : 0 < m)
    (hP : ∀ r : ℝ, 0 < r → ∀ x : ℝ, slopeCutoff m < x → x < 1 →
      0 ≤ deriv (actualProfile r) x) : QQRH m := by
  apply QQRH_of_angular_positivity hm
  intro r hr x hx
  have hleft : -1 < x := lt_trans (slopeCutoff_mem_Ioo hm).1 hx.1
  change 0 ≤ derivWithin (actualProfile r) (Set.Icc (-1) 1) x
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hleft hx.2)]
  exact hP r hr x hx.1 hx.2

/-- Exact slope-two specialization; the cutoff is the rational number -3/5. -/
theorem QQRH_two_of_angular_positivity
    (hP : CutoffDerivativeNonnegative (-(3 / 5 : ℝ))) : QQRH 2 := by
  apply QQRH_of_angular_positivity (by norm_num : (0 : ℝ) < 2)
  simpa only [slopeCutoff_two] using hP

/-- The requested slope-two statement with the ordinary interior derivative. -/
theorem QQRH_two_of_deriv_nonnegative
    (hP : ∀ r : ℝ, 0 < r → ∀ x : ℝ, -(3 / 5 : ℝ) < x → x < 1 →
      0 ≤ deriv (actualProfile r) x) : QQRH 2 := by
  apply QQRH_of_deriv_nonnegative (by norm_num : (0 : ℝ) < 2)
  simpa only [slopeCutoff_two] using hP

end AngularMaster
