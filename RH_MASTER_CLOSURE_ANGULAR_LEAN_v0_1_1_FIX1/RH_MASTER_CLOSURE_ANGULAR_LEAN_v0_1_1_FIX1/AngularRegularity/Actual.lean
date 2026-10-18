import AWPIRH.ThetaEntire
import AngularRegularity.Calculus
import AngularRegularity.DerivativeFormula
import AngularRegularity.Topology
import AngularRegularity.RadiusIsolation
import AngularRegularity.Targets

/-!
Instantiation at the literal Mathlib-backed theta retained from the supplied
angular package. Every analytic hypothesis in the generic first-derivative
regularity interface is discharged here by theta_differentiable.
No research sign property is instantiated.
-/

noncomputable section
open Set
open scoped Topology
namespace AngularRegularity

def actualProfile : ℝ → ℝ → ℝ := profile AWPIRH.theta

def actualAngularSlope : ℝ → ℝ → ℝ := angularSlope AWPIRH.theta

theorem actualProfile_nonnegative (r x : ℝ) : 0 ≤ actualProfile r x :=
  profile_nonnegative AWPIRH.theta r x

theorem actualProfile_eq_zero_iff (r x : ℝ) :
    actualProfile r x = 0 ↔ AWPIRH.theta (circlePoint r x) = 0 :=
  profile_eq_zero_iff AWPIRH.theta r x

theorem actualProfile_continuous_joint :
    Continuous (fun p : ℝ × ℝ => actualProfile p.1 p.2) :=
  profile_continuous_joint AWPIRH.theta_continuous

theorem actualProfile_continuous (r : ℝ) : Continuous (actualProfile r) :=
  profile_continuous AWPIRH.theta_continuous r

theorem actualProfile_differentiableAt {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (actualProfile r) x :=
  profile_differentiableAt (AWPIRH.theta_differentiable _) hx

theorem actualProfile_radial_differentiableAt (r x : ℝ) :
    DifferentiableAt ℝ (fun t => actualProfile t x) r :=
  profile_radial_differentiableAt (AWPIRH.theta_differentiable _)

theorem actualProfile_contDiffOn :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => actualProfile p.1 p.2) interiorDomain :=
  profile_contDiffOn_of_differentiable AWPIRH.theta_differentiable

theorem actualAngularSlope_continuousOn (r : ℝ) :
    ContinuousOn (actualAngularSlope r) (Ioo (-1 : ℝ) 1) :=
  angularSlope_continuousOn AWPIRH.theta_differentiable r

theorem actualAngularSlope_radial_continuous {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Continuous (fun r => actualAngularSlope r x) :=
  angularSlope_radial_continuous AWPIRH.theta_differentiable hx

theorem actualAngularSlope_joint_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => actualAngularSlope p.1 p.2) interiorDomain :=
  angularSlope_joint_continuousOn AWPIRH.theta_differentiable

theorem interiorDomain_isOpen : IsOpen interiorDomain := by
  change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ -1 < p.2 ∧ p.2 < 1}
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const))

theorem actual_negative_region_isOpen :
    IsOpen {p : ℝ × ℝ | p ∈ interiorDomain ∧ actualAngularSlope p.1 p.2 < 0} :=
  negative_region_isOpen interiorDomain_isOpen actualAngularSlope_joint_continuousOn

theorem actualAngularSlope_eq_re {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    actualAngularSlope r x =
      2 * (deriv AWPIRH.theta (circlePoint r x) * circleVelocity r x *
        star (AWPIRH.theta (circlePoint r x))).re :=
  angularSlope_eq_re (AWPIRH.theta_differentiable _) hx

theorem actualAngularSlope_mul_sqrt_eq {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.sqrt (1 - x ^ 2) * actualAngularSlope r x =
      2 * (circlePoint r x * deriv AWPIRH.theta (circlePoint r x) *
        star (AWPIRH.theta (circlePoint r x))).im :=
  angularSlope_mul_sqrt_eq (AWPIRH.theta_differentiable _) hx

theorem actual_stationary_iff_im {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    actualAngularSlope r x = 0 ↔
      (circlePoint r x * deriv AWPIRH.theta (circlePoint r x) *
        star (AWPIRH.theta (circlePoint r x))).im = 0 :=
  angularSlope_eq_zero_iff_im (AWPIRH.theta_differentiable _) hx

theorem actual_zero_is_stationary {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hz : actualProfile r x = 0) :
    actualAngularSlope r x = 0 :=
  angularSlope_eq_zero_of_zero (AWPIRH.theta_differentiable _) hx
    ((actualProfile_eq_zero_iff r x).mp hz)

theorem actual_negative_witness_two_sided {r₀ x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hneg : actualAngularSlope r₀ x < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε →
      actualAngularSlope (r₀ - δ) x < 0 ∧ actualAngularSlope (r₀ + δ) x < 0 :=
  negative_witness_two_sided (actualAngularSlope_radial_continuous hx).continuousAt hneg

/-- Actual theta has isolated zero radii, using its proved nonzero value at 1. -/
theorem actual_radiusGap (r₀ : ℝ) : radiusGap AWPIRH.theta r₀ :=
  radiusGap_of_analytic_nonzero AWPIRH.theta_entire
    ⟨1, AWPIRH.theta_one_ne_zero⟩ r₀

theorem actual_no_zeroRadius_two_sided (r₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ¬ zeroRadius AWPIRH.theta (r₀ - δ) ∧
      ¬ zeroRadius AWPIRH.theta (r₀ + δ) :=
  no_zeroRadius_two_sided_of_analytic_nonzero AWPIRH.theta_entire
    ⟨1, AWPIRH.theta_one_ne_zero⟩ r₀

/-- The two local facts coexist: a negative slope persists on nearby distinct
positive radii even though those circles have no theta zeros. -/
theorem actual_negative_on_nearby_zeroFree_circles {r₀ x : ℝ}
    (hr₀ : 0 < r₀) (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hneg : actualAngularSlope r₀ x < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      0 < r₀ - δ ∧
      actualAngularSlope (r₀ - δ) x < 0 ∧
      actualAngularSlope (r₀ + δ) x < 0 ∧
      ¬ zeroRadius AWPIRH.theta (r₀ - δ) ∧
      ¬ zeroRadius AWPIRH.theta (r₀ + δ) := by
  obtain ⟨εn, hn, hnegative⟩ := actual_negative_witness_two_sided hx hneg
  obtain ⟨εz, hz, hzeroFree⟩ := actual_no_zeroRadius_two_sided r₀
  refine ⟨min r₀ (min εn εz), lt_min_iff.mpr ⟨hr₀, lt_min_iff.mpr ⟨hn, hz⟩⟩, ?_⟩
  intro δ hδ hδε
  have hδr : δ < r₀ := lt_of_lt_of_le hδε (min_le_left _ _)
  have hδnz : δ < min εn εz := lt_of_lt_of_le hδε (min_le_right _ _)
  have hδn : |δ| < εn := by
    rw [abs_of_pos hδ]
    exact lt_of_lt_of_le hδnz (min_le_left _ _)
  have hδz : δ < εz := lt_of_lt_of_le hδnz (min_le_right _ _)
  exact ⟨sub_pos.mpr hδr, (hnegative δ hδn).1, (hnegative δ hδn).2,
    (hzeroFree δ hδ hδz).1, (hzeroFree δ hδ hδz).2⟩

/-- Exact regular-stationarity research interface for the actual profile.
This is a definition, not an assertion that the property holds. -/
def ActualNoRegularAngularStationary : Prop :=
  NoRegularAngularStationary AWPIRH.theta

end AngularRegularity
