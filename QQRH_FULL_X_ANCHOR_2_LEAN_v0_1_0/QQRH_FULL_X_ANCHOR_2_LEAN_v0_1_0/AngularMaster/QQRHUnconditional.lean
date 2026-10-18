import AngularMaster.QQRH
import AngularMaster.LowHeightGeometry
import AngularMaster.SectorPositivity
import AngularMaster.ZeroFreeSeed

/-!
# Unconditional slope-two angular positivity and QQRH

An explicit theta-kernel estimate supplies the weak zero-height bound.
Complex conjugate factors then prove positivity of the actual angular profile.
The final zero exclusion uses the original positivity-to-QQRH implication.
Neither positivity nor RH is assumed in any endpoint below.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

theorem actualComplexScale_sector_two (i : ActualPairIndex) :
    -(actualComplexScale i).re / ‖actualComplexScale i‖ ≤ -(3 / 5 : ℝ) :=
  actualComplexScale_sector_of_zero_height
    (fun _ hz => actual_xi_zero_one_lt_abs_im hz) i

/-- The slope-two positivity premise is now discharged for the actual profile. -/
theorem actual_cutoff_two_nonnegative :
    CutoffDerivativeNonnegative (-(3 / 5 : ℝ)) :=
  actual_cutoffDerivativeNonnegative_of_complexScale_sector
    (by norm_num) (by norm_num) actualComplexScale_sector_two

/-- Ordinary interior derivative form of the unconditional positivity theorem. -/
theorem actual_deriv_nonnegative_above_neg_three_fifths
    (r : ℝ) (hr : 0 < r) (x : ℝ)
    (hx : -(3 / 5 : ℝ) < x) (hx1 : x < 1) :
    0 ≤ deriv (actualProfile r) x := by
  have h := actual_cutoff_two_nonnegative r hr x ⟨hx, hx1⟩
  change 0 ≤ derivWithin (actualProfile r) (Set.Icc (-1) 1) x at h
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith : -1 < x) hx1)] at h
  exact h

/-- Unconditional actual-zeta exclusion, obtained through angular positivity. -/
theorem QQRH_two : QQRH 2 :=
  QQRH_two_of_angular_positivity actual_cutoff_two_nonnegative

end AngularMaster
