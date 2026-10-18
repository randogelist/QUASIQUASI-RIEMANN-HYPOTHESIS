import AngularRegularity.Calculus
import AngularRegularity.StationaryAlgebra

/-!
Named research properties and logical relations between them.
No theorem in this module proves any property for the actual theta function.
The word regular means that the profile value is strictly positive.
-/

noncomputable section
open Set
open scoped ComplexConjugate
namespace AngularRegularity

def NoRegularAngularStationary (f : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ Ioo (-1 : ℝ) 1,
    0 < profile f r x → angularSlope f r x ≠ 0

def AngularStationaryZero (f : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ Ioo (-1 : ℝ) 1,
    angularSlope f r x = 0 → profile f r x = 0

def StationaryCurvatureNonpositive (f : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ Ioo (-1 : ℝ) 1,
    0 < profile f r x → angularSlope f r x = 0 →
      deriv (angularSlope f r) x ≤ 0

def EventualIntegerCurvatureNonnegative (f : ℂ → ℂ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, 0 < z.im →
    levelFunction f (n : ℝ) z = 0 →
      0 ≤ (z * deriv (levelFunction f (n : ℝ)) z * conj (f z)).re

/-- These two proposed properties are equivalent purely by nonnegativity of
the squared modulus. This does not instantiate either property. -/
theorem noRegularAngularStationary_iff_stationaryZero (f : ℂ → ℂ) :
    NoRegularAngularStationary f ↔ AngularStationaryZero f := by
  constructor
  · intro h r hr x hx hs
    by_contra hp
    have hpos : 0 < profile f r x :=
      lt_of_le_of_ne (profile_nonnegative f r x) (Ne.symm hp)
    exact h r hr x hx hpos hs
  · intro h r hr x hx hp hs
    exact (ne_of_gt hp) (h r hr x hx hs)

/-- Conditional logical weakening only. -/
theorem stationaryCurvatureNonpositive_of_noRegularAngularStationary
    {f : ℂ → ℂ} (h : NoRegularAngularStationary f) :
    StationaryCurvatureNonpositive f := by
  intro r hr x hx hp hs
  exact False.elim (h r hr x hx hp hs)

/-- Exact meaning of failure of the named research property. -/
theorem not_noRegularAngularStationary_iff (f : ℂ → ℂ) :
    ¬ NoRegularAngularStationary f ↔
      ∃ r : ℝ, 0 < r ∧ ∃ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 ∧
        0 < profile f r x ∧ angularSlope f r x = 0 := by
  classical
  constructor
  · intro h
    by_contra hw
    apply h
    intro r hr x hx hp hs
    exact hw ⟨r, hr, x, hx, hp, hs⟩
  · rintro ⟨r, hr, x, hx, hp, hs⟩ h
    exact h r hr x hx hp hs

end AngularRegularity
