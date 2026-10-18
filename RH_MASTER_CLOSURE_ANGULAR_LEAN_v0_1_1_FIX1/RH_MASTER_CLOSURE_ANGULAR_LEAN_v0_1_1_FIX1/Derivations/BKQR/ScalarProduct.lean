namespace NativeSolobolo.Derivations.BKQR

/-- Minimal scalar-product geometry used by SOLOBOLO. -/
structure ScalarProductGeometry (Scalar Vec : Type) where
  inner : Vec → Vec → Scalar
  nonnegative : Scalar → Prop
  normSq : Vec → Scalar
  normSq_eq_inner_self : ∀ x : Vec, normSq x = inner x x
  normSq_nonnegative : ∀ x : Vec, nonnegative (normSq x)

end NativeSolobolo.Derivations.BKQR
