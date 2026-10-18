import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace NativeSoloboloContinuant

open Complex

/-- Log-scale derivative D = a d/da. -/
noncomputable def logScaleD (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  a * deriv f a

/-- Second log-scale derivative D^2. -/
noncomputable def logScaleD2 (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  logScaleD (fun x => logScaleD f x) a

/-- SOLOBOLO Widder step. -/
noncomputable def widderStep (n : Nat) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  let m : ℝ := ((n + 1 : Nat) : ℝ)
  let d : ℝ := ((2 * n + 3 : Nat) : ℝ)
  (2 / (m * d)) * (m^2 * f a - logScaleD2 f a)

/-- Definitionally generated Widder tower. -/
noncomputable def widderTower (base : ℝ → ℝ) : Nat → ℝ → ℝ
  | 0 => base
  | n + 1 => widderStep n (widderTower base n)

/-- Mathlib completed-zeta version of xi, up to a harmless nonzero constant. -/
noncomputable def actualXi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta s

/-- Real centered xi slice. -/
noncomputable def actualCenteredXi (x : ℝ) : ℝ :=
  (actualXi ((x + (1 / 2 : ℝ) : ℝ) : ℂ)).re

/-- Positive-axis centered logarithmic derivative. -/
noncomputable def actualCenteredR (a : ℝ) : ℝ :=
  let x := Real.sqrt a
  deriv actualCenteredXi x / (2 * x * actualCenteredXi x)

/-- Actual depth-zero Widder moment. -/
noncomputable def actualWidderBase (a : ℝ) : ℝ :=
  4 * a * deriv (fun t : ℝ => t * actualCenteredR t) a

/-- Actual Mathlib-xi Widder sequence used by IMPLICATION_RH_04. -/
noncomputable def actualWidderMoment (a : ℝ) (n : Nat) : ℝ :=
  widderTower actualWidderBase n a

end NativeSoloboloContinuant
