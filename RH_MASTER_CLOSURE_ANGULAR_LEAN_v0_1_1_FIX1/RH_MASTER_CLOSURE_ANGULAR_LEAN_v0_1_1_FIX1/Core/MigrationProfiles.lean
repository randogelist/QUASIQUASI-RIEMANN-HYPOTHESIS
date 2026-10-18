import Core.RegularizedXi

namespace Merger04.Migration

open Merger04.Regularization

/-- Real centered slice, with the same argument order as the frozen core. -/
noncomputable def realSlice (F : ℂ → ℂ) (x : ℝ) : ℝ :=
  (F ((x + (1 / 2 : ℝ) : ℝ) : ℂ)).re

noncomputable def scaleD (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  a * deriv f a

noncomputable def scaleD2 (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  scaleD (fun x => scaleD f x) a

noncomputable def step (n : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  let d : ℝ := ((2 * n + 3 : ℕ) : ℝ)
  (2 / (m * d)) * (m ^ 2 * f a - scaleD2 f a)

noncomputable def tower (base : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => base
  | n + 1 => step n (tower base n)

noncomputable def centeredR (F : ℂ → ℂ) (a : ℝ) : ℝ :=
  let x := Real.sqrt a
  deriv (realSlice F) x / (2 * x * realSlice F x)

noncomputable def baseMoment (F : ℂ → ℂ) (a : ℝ) : ℝ :=
  4 * a * deriv (fun t : ℝ => t * centeredR F t) a

noncomputable def moment (F : ℂ → ℂ) (a : ℝ) (n : ℕ) : ℝ :=
  tower (baseMoment F) n a

/-- Same quantifier order as frozen uniform-depth positivity. -/
def UniformPositive (F : ℂ → ℂ) (n : ℕ) : Prop :=
  ∀ a : ℝ, 0 < a → 0 ≤ moment F a n

def CofinalPositive (F : ℂ → ℂ) : Prop :=
  ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ UniformPositive F n

/-- Companion profile only; the frozen namespace is imported separately. -/
abbrev RawProfileUS : Prop := CofinalPositive rawXi

/-- New regularized predicate; not a redefinition of the frozen US. -/
abbrev RegularizedUS : Prop := CofinalPositive entireXi

end Merger04.Migration
