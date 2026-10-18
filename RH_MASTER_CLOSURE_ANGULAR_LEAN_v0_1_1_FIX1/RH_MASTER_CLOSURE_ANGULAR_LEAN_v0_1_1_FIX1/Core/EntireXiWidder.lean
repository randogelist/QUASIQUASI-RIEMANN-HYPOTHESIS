import Core.MathlibXiSlitTheta
import Mathlib

namespace NativeSoloboloNegativity

noncomputable section

/-- The genuine entire xi, not the totalized product with completed zeta. -/
def xiEntire : ℂ → ℂ := NativeSolobolo.mathlibXi

@[simp] theorem XI_ENTIRE_ZERO : xiEntire 0 = (1 / 2 : ℂ) := by
  norm_num [xiEntire, NativeSolobolo.mathlibXi]

@[simp] theorem XI_ENTIRE_ONE : xiEntire 1 = (1 / 2 : ℂ) := by
  norm_num [xiEntire, NativeSolobolo.mathlibXi]

theorem XI_ENTIRE_DIFFERENTIABLE : Differentiable ℂ xiEntire :=
  NativeSolobolo.MATHLIB_XI_DIFFERENTIABLE

/-- Compatibility with the meromorphic completion is restricted to its domain. -/
theorem XI_EQ_RAW_COMPLETION_AWAY_FROM_POLES (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiEntire s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have h10 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold xiEntire NativeSolobolo.mathlibXi
  rw [completedRiemannZeta_eq]
  field_simp [h0, h10] <;> ring

/-- The real centered slice, now regular at x=1/2. -/
def xiRealSlice (x : ℝ) : ℝ :=
  (xiEntire ((1 / 2 : ℂ) + (x : ℂ))).re

@[simp] theorem XI_REAL_SLICE_HALF : xiRealSlice (1 / 2) = 1 / 2 := by
  norm_num [xiRealSlice, xiEntire, NativeSolobolo.mathlibXi]

/-- R(a)=F'(sqrt(a))/(2 sqrt(a) F(sqrt(a))).
The theorem that this is theta'/theta is NOT assumed in this definition. -/
def xiR (a : ℝ) : ℝ :=
  deriv xiRealSlice (Real.sqrt a) /
    (2 * Real.sqrt a * xiRealSlice (Real.sqrt a))

def xiWidderBase (a : ℝ) : ℝ :=
  4 * a * deriv (fun t : ℝ => t * xiR t) a

def widderStep (n : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  let m : ℝ := (n + 1 : ℕ)
  2 / (m * (2 * m + 1)) *
    (m ^ 2 * f a - a * deriv f a - a ^ 2 * deriv (deriv f) a)

def widderTower (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n + 1 => widderStep n (widderTower f n)

def xiWidderMoment (a : ℝ) (n : ℕ) : ℝ :=
  widderTower xiWidderBase n a

@[simp] theorem XI_WIDDER_ZERO (a : ℝ) :
    xiWidderMoment a 0 = xiWidderBase a := rfl

/-- The direct high-derivative formula is retained as a separate actual object.
Its all-depth equality with the recursive tower is a remaining analytic proof. -/
def xiWidderDirect (a : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (4 * a) ^ (n + 1) / ((2 * n + 1).factorial : ℝ) *
    iteratedDeriv (2 * n + 1) (fun t : ℝ => t ^ (n + 1) * xiR t) a

/-- The logical cofinal criterion is restated for the repaired xi family.
No equality with the older incorrectly totalized family is silently used. -/
def UniformDepthPositive (n : ℕ) : Prop :=
  ∀ a : ℝ, 0 < a → 0 ≤ xiWidderMoment a n

def CofinalUniformDepthPositive : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ UniformDepthPositive N

def EventuallyDepthNegative : Prop :=
  ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∃ a : ℝ, 0 < a ∧ xiWidderMoment a N < 0

theorem COFINAL_POSITIVITY_EXCLUDES_EVENTUAL_NEGATIVITY
    (hpos : CofinalUniformDepthPositive) : ¬ EventuallyDepthNegative := by
  rintro ⟨K, hK⟩
  rcases hpos K with ⟨N, hKN, hN⟩
  rcases hK N hKN with ⟨a, ha, hneg⟩
  exact (not_lt_of_ge (hN a ha)) hneg

end
end NativeSoloboloNegativity
