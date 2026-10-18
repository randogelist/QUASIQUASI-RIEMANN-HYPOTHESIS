import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
The exact angular interval and within-derivative convention needed by the
QQRH route. Endpoint derivatives are defined but are not positivity premises.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

/-- The angular coordinate is `x = cos θ`. -/
def angularInterval : Set ℝ := Set.Icc (-1) 1

/-- The literal within derivative on the full angular interval. -/
def angularDerivative (P : ℝ → ℝ → ℝ) (r x : ℝ) : ℝ :=
  derivWithin (P r) angularInterval x

end AngularMaster
