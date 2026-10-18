import QQRH

#print QQRH
#print AngularMaster.QQRH
#print QQRH.cutoff
#print AngularMaster.slopeCutoff
#print QQRH.profile
#print AngularMaster.actualProfile
#print AWPIRH.theta
#print AWPIRH.xi

#check QQRH.cutoff_two
#check QQRH.of_positivity
#check QQRH.positivity_two
#print QQRH.two

#print axioms QQRH.cutoff_two
#print axioms QQRH.of_positivity
#print axioms QQRH.positivity_two
#print axioms QQRH.two

example : QQRH.cutoff 2 = -(3 / 5 : ℝ) := QQRH.cutoff_two

example : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
    -(3 / 5 : ℝ) < x → x < 1 →
    0 ≤ deriv (AngularMaster.actualProfile r) x := QQRH.positivity_two

/-- The exported proposition is literally about Mathlib's Riemann zeta. -/
example : ∀ s : ℂ, 0 < s.re → s.re < 1 →
    |s.im| < 2 * |s.re - 1 / 2| → riemannZeta s ≠ 0 := QQRH.two

#check QQRH.cutoff_ten
#check QQRH.cutoff_eleven
#check QQRH.positivity_eleven
#check QQRH.of_sq_lt_122
#print QQRH.eleven

#print axioms AngularMaster.hurwitzThetaMellinKernel_sharper_upper_bound
#print axioms AngularMaster.actual_completedZeta₀_norm_le_one_thirtyone
#print axioms AngularMaster.norm_mul_sub_one_le_im_sq_add_half
#print axioms AngularMaster.actual_xi_zero_height_lt
#print axioms AngularMaster.actual_cutoff_nonnegative_of_zero_height
#print axioms QQRH.cutoff_ten
#print axioms QQRH.cutoff_eleven
#print axioms QQRH.positivity_eleven
#print axioms QQRH.eleven
#print axioms QQRH.ten
#print axioms QQRH.of_sq_lt_122

example : QQRH.cutoff 11 = -(60 / 61 : ℝ) := QQRH.cutoff_eleven

example : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
    -(60 / 61 : ℝ) < x → x < 1 →
    0 ≤ deriv (AngularMaster.actualProfile r) x := QQRH.positivity_eleven

example : ∀ s : ℂ, 0 < s.re → s.re < 1 →
    |s.im| < 11 * |s.re - 1 / 2| → riemannZeta s ≠ 0 := QQRH.eleven

example (m : ℝ) (hm : 1 ≤ m) (hcap : m ^ 2 < 122) : QQRH m :=
  QQRH.of_sq_lt_122 hm hcap

-- The second full-x-range anchor is closed over the proved analytic height gap.
#check AngularMaster.actual_xi_zero_thirteen_halves_lt_abs_im
#check QQRH.second_full_x_radius
#check QQRH.second_full_x_monotone
#check QQRH.second_full_x_range_anchor
#check QQRH.second_full_x_positive

#print axioms AngularMaster.actual_xi_zero_thirteen_halves_lt_abs_im
#print axioms AngularMaster.hurwitzThetaMellinKernel_anchor_upper_bound
#print axioms AngularMaster.integral_Ioi_one_rpow_neg_exp_le
#print axioms AngularMaster.norm_mellin_le_paired_endpoint
#print axioms AngularMaster.actual_completedZeta₀_norm_le_nine_three_eightyfive
#print axioms AngularMaster.monotoneOn_normSq_conjugateFactor_circle_of_height
#print axioms AngularMaster.actualProfile_sq_symmetric_product_values
#print axioms AngularMaster.actual_theta_second_full_x_ne_zero
#print axioms AngularMaster.actual_theta_ne_zero_closed_disk_of_height
#print axioms QQRH.second_full_x_radius
#print axioms QQRH.second_full_x_monotone
#print axioms QQRH.second_full_x_range_anchor
#print axioms QQRH.second_full_x_positive

example : ∀ r : ℝ, 0 < r → r ≤ 255 / 7 → ∀ x : ℝ,
    -1 < x → x < 1 → 0 ≤ deriv (AngularMaster.actualProfile r) x :=
  QQRH.second_full_x_range_anchor

example : MonotoneOn (QQRH.profile (255 / 7)) (Set.Icc (-1) 1) :=
  QQRH.second_full_x_monotone _ (by norm_num) (by norm_num)

example : ∀ r : ℝ, 0 ≤ r → r ≤ 255 / 7 → ∀ x : ℝ,
    -1 ≤ x → x ≤ 1 → 0 < AngularMaster.actualProfile r x :=
  QQRH.second_full_x_positive
