import MisterPremise.Premise
import MisterPremise.Geometry
import MisterPremise.Continuation
import MisterPremise.ActualRegularity

/-!
# RH is equivalent to MISTERPREMISE

For the forward closure, a hypothetical nonreal theta zero lies strictly in the
premise region. Analytic uniqueness and the mean value theorem give a positive
angular slope immediately to its right. The one-sided continuation theorem
then contradicts the vanishing angular slope at that zero.

Conversely RH supplies an analytic, nonnegative, monotone angular slope
extension. Its endpoint-weighted logarithmic derivative has a removable
singularity of finite order, and compactness supplies the required constant.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexConjugate

namespace MisterPremise

/-- Every nonempty interior angular interval contains a positive profile value.
Otherwise the nonzero entire theta would vanish on an injective arc. -/
theorem exists_profile_pos_on_interval {r u v : ℝ}
    (hr : 0 < r) (hu : -1 < u) (huv : u < v) (hv : v < 1) :
    ∃ t ∈ Ioo u v, 0 < P r t := by
  by_contra hn
  push_neg at hn
  let a := (2 * u + v) / 3
  let b := (u + 2 * v) / 3
  have hab : a < b := by dsimp [a, b]; linarith
  have hz : ∀ t ∈ Icc a b,
      AWPIRH.theta (AngularMaster.circlePoint r t) = 0 := by
    intro t ht
    have htuv : t ∈ Ioo u v := by
      dsimp [a, b] at ht
      constructor <;> linarith [ht.1, ht.2]
    have heq : P r t = 0 :=
      le_antisymm (hn t htuv) (AngularRegularity.actualProfile_nonnegative r t)
    exact (AngularRegularity.actualProfile_eq_zero_iff r t).mp heq
  have heq := AngularMaster.entire_eq_zero_of_zero_arc AWPIRH.theta_entire
    (AngularMaster.continuous_circlePoint r)
    (AngularMaster.injective_circlePoint hr.ne') hab hz
  exact AWPIRH.theta_one_ne_zero (by rw [heq]; rfl)

/-- To the right of a profile zero there is a strictly positive angular slope
before any chosen later interior angle. -/
theorem exists_slope_pos_right_of_zero {r x b : ℝ}
    (hr : 0 < r) (hx : -1 < x) (hxb : x < b) (hb : b < 1)
    (hz : P r x = 0) : ∃ y ∈ Ioo x b, 0 < A r y := by
  obtain ⟨t, ht, hpt⟩ := exists_profile_pos_on_interval hr hx hxb hb
  have hdiff : DifferentiableOn ℝ (P r) (Ioo x t) := by
    intro y hy
    exact (AngularRegularity.actualProfile_differentiableAt
      ⟨hx.trans hy.1, hy.2.trans (ht.2.trans hb)⟩).differentiableWithinAt
  obtain ⟨y, hy, hder⟩ := exists_deriv_eq_slope (P r) ht.1
    (AngularRegularity.actualProfile_continuous r).continuousOn hdiff
  refine ⟨y, ⟨hy.1, hy.2.trans ht.2⟩, ?_⟩
  change 0 < deriv (P r) y
  rw [hder, hz, sub_zero]
  exact div_pos hpt (sub_pos.mpr ht.1)

/-- The finite bound excludes a profile zero strictly inside its own domain. -/
theorem profile_ne_zero_of_MISTERPREMISE
    (h : MISTERPREMISE) {r x : ℝ} (hr : (255 / 7 : ℝ) < r)
    (hx : -1 < x) (hxb : x < -kappa r) : P r x ≠ 0 := by
  intro hz
  have hrpos : 0 < r := by linarith
  have hb := neg_kappa_mem_Ioo hr
  obtain ⟨y, hy, hpy⟩ := exists_slope_pos_right_of_zero hrpos hx hxb hb.2 hz
  obtain ⟨M, hM, hbound⟩ := h r hr
  have hy1 : y < 1 := hy.2.trans hb.2
  have hcont : ContinuousOn (A r) (Ioc (-1 : ℝ) y) :=
    (AngularRegularity.actualAngularSlope_continuousOn r).mono
      (fun t ht => ⟨ht.1, ht.2.trans_lt hy1⟩)
  have hdiff : ∀ t ∈ Ioo (-1 : ℝ) y, DifferentiableAt ℝ (A r) t := by
    intro t ht
    exact actualAngularSlope_differentiableAt ⟨ht.1, ht.2.trans hy1⟩
  have hbound' : ∀ t ∈ Ioc (-1 : ℝ) y, 0 < A r t →
      (1 + t) * deriv (A r) t ≤ M * A r t := by
    intro t ht hp
    exact hbound t ⟨ht.1, ht.2.trans hy.2.le⟩ hp
  have hp := positive_on_Ioc_of_weighted_deriv_upper_bound
    (hx.trans hy.1) hcont hdiff hpy hM.le hbound' x ⟨hx, hy.1.le⟩
  have hs : A r x = 0 :=
    AngularRegularity.actual_zero_is_stationary ⟨hx, hxb.trans hb.2⟩ hz
  exact (ne_of_gt hp) hs

theorem theta_no_upper_zero_of_MISTERPREMISE
    (h : MISTERPREMISE) {z : ℂ} (hi : 0 < z.im) : AWPIRH.theta z ≠ 0 := by
  intro hz
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq] at hi
  obtain ⟨hr, hx, hxb⟩ := theta_nonreal_zero_in_premise_region hz hi.ne'
  apply profile_ne_zero_of_MISTERPREMISE h hr hx hxb
  apply (AngularRegularity.actualProfile_eq_zero_iff _ _).mpr
  change AWPIRH.theta (AngularMaster.circlePoint ‖z‖ (z.re / ‖z‖)) = 0
  rw [AngularMaster.circlePoint_norm_re_div hz0 hi.le]
  exact hz

/-- Exact closure to Mathlib's native Riemann hypothesis, from one premise. -/
theorem RiemannHypothesis_of_MISTERPREMISE
    (h : MISTERPREMISE) : _root_.RiemannHypothesis := by
  apply AngularMaster.native_RH_iff_theta_zeros_nonpositive.mpr
  intro z hz
  have him : z.im = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hi | hi
    · have hconj : 0 < (conj z).im := by simp; linarith
      exact theta_no_upper_zero_of_MISTERPREMISE h hconj
        (AngularMaster.theta_zero_conj hz)
    · exact theta_no_upper_zero_of_MISTERPREMISE h hi hz
  refine ⟨him, ?_⟩
  have hr := theta_zero_radius_large hz
  have hn : 0 < ‖z‖ := by linarith
  have hk := lower_bound_le_kappa hn
  have ha := theta_zero_angle_lt_neg_kappa hz
  have hneg : z.re / ‖z‖ < 0 := by linarith
  have hre := (div_lt_iff₀ hn).mp hneg
  linarith

/-- RH proves the existence of finite radius-dependent constants; no simple-zero
assumption or global bound in the radius is required. -/
theorem MISTERPREMISE_of_RiemannHypothesis
    (hRH : _root_.RiemannHypothesis) : MISTERPREMISE := by
  intro r hr
  have hb := neg_kappa_mem_Ioo hr
  exact actualAngularSlope_weighted_bound_of_RH hRH (by linarith) hb.1 hb.2

theorem MISTERPREMISE_iff_RiemannHypothesis :
    MISTERPREMISE ↔ _root_.RiemannHypothesis :=
  ⟨RiemannHypothesis_of_MISTERPREMISE, MISTERPREMISE_of_RiemannHypothesis⟩

theorem RiemannHypothesis_iff_MISTERPREMISE :
    _root_.RiemannHypothesis ↔ MISTERPREMISE :=
  MISTERPREMISE_iff_RiemannHypothesis.symm

end MisterPremise
