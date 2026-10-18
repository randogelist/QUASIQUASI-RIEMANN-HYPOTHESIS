import Core.Observable

namespace NativeSolobolo

/--
!! ANALYTIC GEOMETRY FRONTIER
The local logarithmic-derivative/Cayley calculation for the actual GP observable:
an off-critical-line centered zero produces a pole at its canonical (a,r).

The radius and positivity statements are *not* assumed here; they are proved in
`Derivations/Geometry/CayleyRadius.lean`.  This structure isolates only the local
analytic Laurent-to-pole identification.
-/
structure ThetaCayleyPoleRealization
    {Value : Type}
    (X : CenteredXiGeometry)
    (G : GPObservable Value) where
  pole_at_offline : ∀ z : X.Zero,
    X.beta z ≠ 0 →
    G.eval (X.anchor z) (X.radius z) = none

namespace Frontier

/-- Explicit analytic frontier; no global axiom is declared. -/
def GeometryFrontier
    {Value : Type}
    (X : CenteredXiGeometry)
    (G : GPObservable Value) : Prop :=
  Nonempty (ThetaCayleyPoleRealization X G)

end Frontier
end NativeSolobolo
