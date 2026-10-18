import RHMaster.AngularBridge
import AngularMaster.AnalyticExtension
import AngularMaster.SecondFullXAnchor

/-!
# Strongest retained angular coverage and the residual sign frontier

The proved height gap 13/2 improves the slope certificate to 13 and the angular
cutoff to -84/85. Equality at slope 13 is permitted: the height gap theorem is
strict, and the height-to-cutoff transport accepts exactly H = 13/2.

Combining this global angular sector with the proved radius slab 255/7 leaves
only r > 255/7 and -1 < x <= -84/85 as an equivalent sign frontier for RH.
No assertion that the residual sign condition holds is made.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace RHMaster

theorem slopeCutoff_thirteen :
    AngularMaster.slopeCutoff 13 = -(84 / 85 : ℝ) := by
  norm_num [AngularMaster.slopeCutoff]

/-- The existing strict analytic height gap supplies slope 13 itself. -/
theorem actual_cutoff_thirteen_nonnegative :
    AngularMaster.CutoffDerivativeNonnegative (-(84 / 85 : ℝ)) := by
  have h := AngularMaster.actual_cutoff_nonnegative_of_zero_height
    (H := 13 / 2) (by norm_num)
    (fun _ hz => AngularMaster.actual_xi_zero_thirteen_halves_lt_abs_im hz)
  simpa only [show (2 : ℝ) * (13 / 2) = 13 by norm_num,
    slopeCutoff_thirteen] using h

/-- Actual-zeta wedge exclusion at slope 13, without a research premise. -/
theorem QQRH_thirteen : AngularMaster.QQRH 13 := by
  apply AngularMaster.QQRH_of_angular_positivity (by norm_num : (0 : ℝ) < 13)
  simpa only [slopeCutoff_thirteen] using actual_cutoff_thirteen_nonnegative

theorem actualAngularSlope_nonnegative_above_neg_eightyfour_eightyfive
    {r x : ℝ} (hr : 0 < r) (hx : -(84 / 85 : ℝ) < x) (hx1 : x < 1) :
    0 ≤ AngularRegularity.actualAngularSlope r x := by
  have hxglobal : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
  rw [regularity_actualAngularSlope_eq_master hxglobal]
  exact actual_cutoff_thirteen_nonnegative r hr x ⟨hx, hx1⟩

/-- The strongest retained full-angular radius slab, in FIX9 notation. -/
theorem actualAngularSlope_nonnegative_on_second_full_x_slab
    {r x : ℝ} (hr : 0 < r) (hR : r ≤ 255 / 7)
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ AngularRegularity.actualAngularSlope r x :=
  AngularMaster.actual_deriv_second_full_x_anchor hr hR hx.1 hx.2

theorem actualProfile_positive_on_second_full_x_slab
    {r x : ℝ} (hr : 0 ≤ r) (hR : r ≤ 255 / 7)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < AngularRegularity.actualProfile r x :=
  AngularMaster.actualProfile_second_full_x_pos hr hR hx.1 hx.2

/-- Union of the finite radius slab and the unbounded-radius angular sector. -/
theorem actualAngularSlope_nonnegative_on_known_region
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hcovered : r ≤ 255 / 7 ∨ -(84 / 85 : ℝ) < x) :
    0 ≤ AngularRegularity.actualAngularSlope r x := by
  rcases hcovered with hR | hangle
  · exact actualAngularSlope_nonnegative_on_second_full_x_slab hr hR hx
  · exact actualAngularSlope_nonnegative_above_neg_eightyfour_eightyfive hr hangle hx.2

/-- Exact remaining sign condition after using both proved coverage regions. -/
def AngularResidualNonnegative : Prop :=
  ∀ r : ℝ, (255 / 7 : ℝ) < r → ∀ x ∈ Ioo (-1 : ℝ) 1,
    x ≤ -(84 / 85 : ℝ) → 0 ≤ AngularRegularity.actualAngularSlope r x

theorem actualInteriorSlopeNonnegative_of_residual
    (h : AngularResidualNonnegative) : ActualInteriorSlopeNonnegative := by
  intro r hr x hx
  by_cases hR : r ≤ 255 / 7
  · exact actualAngularSlope_nonnegative_on_second_full_x_slab hr hR hx
  · by_cases hangle : -(84 / 85 : ℝ) < x
    · exact actualAngularSlope_nonnegative_above_neg_eightyfour_eightyfive hr hangle hx.2
    · exact h r (lt_of_not_ge hR) x hx (le_of_not_gt hangle)

theorem native_RH_of_angularResidualNonnegative
    (h : AngularResidualNonnegative) : _root_.RiemannHypothesis :=
  native_RH_of_actualInteriorSlopeNonnegative
    (actualInteriorSlopeNonnegative_of_residual h)

/-- An unconditional equivalence; the residual sign condition is still open. -/
theorem native_RH_iff_angularResidualNonnegative :
    _root_.RiemannHypothesis ↔ AngularResidualNonnegative := by
  constructor
  · intro hRH r hr x hx hangle
    exact native_RH_implies_actualInteriorSlopeNonnegative hRH r
      (by linarith) x hx
  · exact native_RH_of_angularResidualNonnegative

end RHMaster
