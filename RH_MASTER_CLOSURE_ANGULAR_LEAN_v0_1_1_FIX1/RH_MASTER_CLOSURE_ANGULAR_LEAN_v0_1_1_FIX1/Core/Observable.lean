import Mathlib

namespace NativeSolobolo

/-- The scalar Cayley observable used by the direct SOLOBOLO route. -/
structure GPObservable (Value : Type) where
  eval : ℝ → ℝ → Option Value

/-- Positive Cayley anchor. -/
def PositiveAnchor (a : ℝ) : Prop := 0 < a

/-- Interior Cayley radius. -/
def InteriorRadius (r : ℝ) : Prop := 0 < r ∧ r < 1

/--
Centered nontrivial-zero geometry.  For an actual xi-instantiation,
`beta z = Re rho - 1/2` and `gamma z = Im rho`.
Nontrivial zeros have nonzero imaginary part.
-/
structure CenteredXiGeometry where
  Zero : Type
  beta : Zero → ℝ
  gamma : Zero → ℝ
  gamma_ne_zero : ∀ z : Zero, gamma z ≠ 0

/-- RH in centered-zero coordinates: every nontrivial zero has beta = 0. -/
def RiemannHypothesis (X : CenteredXiGeometry) : Prop :=
  ∀ z : X.Zero, X.beta z = 0

/-- Natural positive Cayley anchor attached to a centered zero. -/
def CenteredXiGeometry.anchor (X : CenteredXiGeometry) (z : X.Zero) : ℝ :=
  X.beta z ^ 2 + X.gamma z ^ 2

/-- Interior-radius candidate attached to a centered zero. -/
noncomputable def CenteredXiGeometry.radius (X : CenteredXiGeometry) (z : X.Zero) : ℝ :=
  X.gamma z ^ 2 / X.anchor z

/-- Reciprocal Cayley coordinate q = a / gamma^2. -/
noncomputable def CenteredXiGeometry.cayleyQ (X : CenteredXiGeometry) (z : X.Zero) : ℝ :=
  X.anchor z / (X.gamma z ^ 2)

end NativeSolobolo
