import AngularMaster.Chain
import AngularMaster.QQRHUnconditional
import AngularRegularity

/-!
# The actual angular closure interface

The Master and FIX9 regularity packages use definitionally identical circle
coordinates and squared-modulus profiles. Their derivative conventions agree
on the open angular interval. This module connects the proved equivalence to
the ordinary FIX9 derivative and derives a one-input closure theorem from
absence of positive stationary points.

The research premise `ActualNoRegularAngularStationary` is retained explicitly.
It is not proved here, and no simple-zero assumption is used.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace RHMaster

/-- Both developments use exactly the same upper semicircle map. -/
theorem regularity_circlePoint_eq_master (r x : ℝ) :
    AngularRegularity.circlePoint r x = AngularMaster.circlePoint r x := rfl

/-- Both actual profiles are the same literal squared modulus of theta. -/
theorem regularity_actualProfile_eq_master :
    AngularRegularity.actualProfile = AngularMaster.actualProfile := rfl

/-- Ordinary derivatives agree globally because their underlying functions do. -/
theorem regularity_actualAngularSlope_eq_deriv (r x : ℝ) :
    AngularRegularity.actualAngularSlope r x =
      deriv (AngularMaster.actualProfile r) x := rfl

/-- The within-derivative convention agrees with FIX9 at interior angles. -/
theorem regularity_actualAngularSlope_eq_master {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    AngularRegularity.actualAngularSlope r x =
      AngularMaster.angularDerivative AngularMaster.actualProfile r x := by
  exact AngularRegularity.angularSlope_eq_derivWithin hx

/-- The single global positivity premise in the actual FIX9 coordinates. -/
def ActualInteriorSlopeNonnegative : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ Ioo (-1 : ℝ) 1,
    0 ≤ AngularRegularity.actualAngularSlope r x

theorem native_RH_implies_actualInteriorSlopeNonnegative
    (hRH : _root_.RiemannHypothesis) : ActualInteriorSlopeNonnegative := by
  have hmaster := AngularMaster.native_RH_iff_actual_profileMaster.mp hRH
  have hderiv := AngularMaster.derivativeNonnegative_of_profileMaster hmaster
  intro r hr x hx
  rw [regularity_actualAngularSlope_eq_master hx]
  exact hderiv r hr x ⟨hx.1.le, hx.2.le⟩

/-- Interior positivity suffices: no endpoint derivative sign is an input. -/
theorem native_RH_of_actualInteriorSlopeNonnegative
    (h : ActualInteriorSlopeNonnegative) : _root_.RiemannHypothesis := by
  have hcut : AngularMaster.CutoffDerivativeNonnegative (-1) := by
    intro r hr x hx
    rw [← regularity_actualAngularSlope_eq_master hx]
    exact h r hr x hx
  exact AngularMaster.native_RH_of_actual_angular_monotone
    (AngularMaster.actualProfile_monotoneOn_cutoff le_rfl hcut)

/-- The ordinary FIX9 sign condition is exactly equivalent to native RH. -/
theorem native_RH_iff_actualInteriorSlopeNonnegative :
    _root_.RiemannHypothesis ↔ ActualInteriorSlopeNonnegative :=
  ⟨native_RH_implies_actualInteriorSlopeNonnegative,
    native_RH_of_actualInteriorSlopeNonnegative⟩

/-- Expanded form, exposing every quantifier in the global sign condition. -/
theorem native_RH_iff_actualAngularSlope_nonnegative :
    _root_.RiemannHypothesis ↔
      ∀ r : ℝ, 0 < r → ∀ x ∈ Ioo (-1 : ℝ) 1,
        0 ≤ AngularRegularity.actualAngularSlope r x :=
  native_RH_iff_actualInteriorSlopeNonnegative

/-- The already proved slope-two sector transferred to FIX9. -/
theorem actualAngularSlope_nonnegative_above_neg_three_fifths
    {r x : ℝ} (hr : 0 < r) (hx : -(3 / 5 : ℝ) < x) (hx1 : x < 1) :
    0 ≤ AngularRegularity.actualAngularSlope r x :=
  AngularMaster.actual_deriv_nonnegative_above_neg_three_fifths r hr x hx hx1

/-- Zero-free radii give strictly positive values on the closed semicircle. -/
theorem actualProfile_pos_of_no_zeroRadius {r x : ℝ}
    (hr : 0 ≤ r) (hx : x ∈ Icc (-1 : ℝ) 1)
    (hfree : ¬ AngularRegularity.zeroRadius AWPIRH.theta r) :
    0 < AngularRegularity.actualProfile r x := by
  apply (AngularRegularity.profile_pos_iff AWPIRH.theta r x).mpr
  intro hz
  apply hfree
  refine ⟨AngularRegularity.circlePoint r x, hz, ?_⟩
  exact AngularMaster.circlePoint_norm r x hr hx

/-- A negative witness would force a positive stationary point after a small
radial perturbation. The entire-theta radius gap is essential: it ensures the
stationary point is a regular point, rather than a theta zero. -/
theorem actualInteriorSlopeNonnegative_of_noRegularAngularStationary
    (hN : AngularRegularity.ActualNoRegularAngularStationary) :
    ActualInteriorSlopeNonnegative := by
  intro r hr x hx
  by_contra hnot
  have hneg : AngularRegularity.actualAngularSlope r x < 0 := lt_of_not_ge hnot
  have hx0 : x < 0 := by
    by_contra hn
    have hnonneg := actualAngularSlope_nonnegative_above_neg_three_fifths
      hr (by linarith : -(3 / 5 : ℝ) < x) hx.2
    exact (not_lt_of_ge hnonneg) hneg
  obtain ⟨ε, hε, hnear⟩ :=
    AngularRegularity.actual_negative_on_nearby_zeroFree_circles hr hx hneg
  have hδ : 0 < ε / 2 := by positivity
  have hδε : ε / 2 < ε := by linarith
  obtain ⟨hr', hleft, _, hfree, _⟩ := hnear (ε / 2) hδ hδε
  have hxzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hposzero : 0 < AngularRegularity.actualProfile (r - ε / 2) 0 :=
    actualProfile_pos_of_no_zeroRadius hr'.le (by norm_num) hfree
  have hzeroNonneg : 0 ≤ AngularRegularity.actualAngularSlope (r - ε / 2) 0 :=
    actualAngularSlope_nonnegative_above_neg_three_fifths hr'
      (by norm_num) (by norm_num)
  have hzeroNe : AngularRegularity.actualAngularSlope (r - ε / 2) 0 ≠ 0 :=
    hN (r - ε / 2) hr' 0 hxzero hposzero
  have hright : 0 < AngularRegularity.actualAngularSlope (r - ε / 2) 0 :=
    lt_of_le_of_ne hzeroNonneg (Ne.symm hzeroNe)
  have hcont : ContinuousOn
      (AngularRegularity.actualAngularSlope (r - ε / 2)) (Icc x 0) := by
    apply (AngularRegularity.actualAngularSlope_continuousOn (r - ε / 2)).mono
    intro y hy
    exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 (by norm_num)⟩
  obtain ⟨y, hy, hstationary⟩ :=
    AngularRegularity.exists_interior_zero_of_sign_bracket
      (A := AngularRegularity.actualAngularSlope) (r := r - ε / 2)
      hx0 hcont hleft hright
  have hyglobal : y ∈ Ioo (-1 : ℝ) 1 :=
    ⟨lt_trans hx.1 hy.1, lt_trans hy.2 (by norm_num)⟩
  have hypositive : 0 < AngularRegularity.actualProfile (r - ε / 2) y :=
    actualProfile_pos_of_no_zeroRadius hr'.le
      ⟨hyglobal.1.le, hyglobal.2.le⟩ hfree
  exact hN (r - ε / 2) hr' y hyglobal hypositive hstationary

/-- One explicit research premise closes the regularity-to-native-RH route. -/
theorem native_RH_of_noRegularAngularStationary
    (hN : AngularRegularity.ActualNoRegularAngularStationary) :
    _root_.RiemannHypothesis :=
  native_RH_of_actualInteriorSlopeNonnegative
    (actualInteriorSlopeNonnegative_of_noRegularAngularStationary hN)

/-- Equivalent formulation of the same single research premise. -/
theorem native_RH_of_angularStationaryZero
    (hS : AngularRegularity.AngularStationaryZero AWPIRH.theta) :
    _root_.RiemannHypothesis :=
  native_RH_of_noRegularAngularStationary
    ((AngularRegularity.noRegularAngularStationary_iff_stationaryZero AWPIRH.theta).mpr hS)

/-- Failure of native RH forces a positive angular stationary point. This
does not assert that such a point exists; it exposes the contraposed frontier. -/
theorem positive_stationary_of_not_native_RH
    (hnot : ¬ _root_.RiemannHypothesis) :
    ∃ r : ℝ, 0 < r ∧ ∃ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 ∧
      0 < AngularRegularity.actualProfile r x ∧
        AngularRegularity.actualAngularSlope r x = 0 := by
  apply (AngularRegularity.not_noRegularAngularStationary_iff AWPIRH.theta).mp
  intro hN
  exact hnot (native_RH_of_noRegularAngularStationary hN)

end RHMaster
