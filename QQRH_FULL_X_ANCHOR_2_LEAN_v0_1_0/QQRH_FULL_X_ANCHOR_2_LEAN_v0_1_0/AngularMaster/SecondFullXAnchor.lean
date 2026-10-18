import AngularMaster.AnchorHeight
import AngularMaster.FullXProduct

/-!
The second full-x-range anchor for the literal entire-theta profile.
The height gap is proved from the theta Mellin integral in AnchorHeight.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace AngularMaster

def secondFullXRadius : ℝ := 255 / 7

theorem actualProfile_second_full_x_monotone {r : ℝ}
    (hr : 0 < r) (hR : r ≤ secondFullXRadius) :
    MonotoneOn (actualProfile r) (Icc (-1) 1) :=
  actualProfile_monotoneOn_full_of_height
    (fun _ hz => actual_xi_zero_thirteen_halves_lt_abs_im hz) hr hR

theorem actual_deriv_second_full_x_anchor {r : ℝ}
    (hr : 0 < r) (hR : r ≤ secondFullXRadius)
    {x : ℝ} (hx : -1 < x) (hx1 : x < 1) :
    0 ≤ deriv (actualProfile r) x :=
  actual_deriv_nonnegative_full_of_height
    (fun _ hz => actual_xi_zero_thirteen_halves_lt_abs_im hz) hr hR hx hx1

theorem actual_theta_second_full_x_ne_zero {r : ℝ}
    (hr : 0 < r) (hR : r ≤ secondFullXRadius)
    {x : ℝ} (hx : -1 < x) (hx1 : x ≤ 1) :
    AWPIRH.theta (circlePoint r x) ≠ 0 :=
  actual_theta_circle_ne_zero_full_of_height
    (fun _ hz => actual_xi_zero_thirteen_halves_lt_abs_im hz) hr hR hx hx1

theorem actualProfile_second_full_x_pos {r : ℝ}
    (hr : 0 ≤ r) (hR : r ≤ secondFullXRadius)
    {x : ℝ} (hx : -1 ≤ x) (hx1 : x ≤ 1) :
    0 < actualProfile r x :=
  actualProfile_pos_closed_of_height
    (fun _ hz => actual_xi_zero_thirteen_halves_lt_abs_im hz) hr hR ⟨hx, hx1⟩

end AngularMaster
