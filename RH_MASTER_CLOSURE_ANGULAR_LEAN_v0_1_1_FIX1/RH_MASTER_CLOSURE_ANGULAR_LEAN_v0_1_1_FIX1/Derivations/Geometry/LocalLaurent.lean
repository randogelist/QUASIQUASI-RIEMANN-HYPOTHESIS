import Derivations.Geometry.CayleyRadius

namespace NativeSolobolo.Derivations.Geometry

open NativeSolobolo

/--
! Algebraic local model of a zero of finite positive multiplicity.
The intended analytic instantiation is
  theta(z) = (z-z0)^m h(z)
with h(z0) != 0, and `regularPrime` the derivative of h.
No analytic axiom is built into this structure.
-/
structure LocalZeroFactorization where
  z0 : ℂ
  multiplicity : Nat
  multiplicity_pos : 0 < multiplicity
  regular : ℂ → ℂ
  regularPrime : ℂ → ℂ

/-- Local theta model attached to a factorization. -/
def LocalZeroFactorization.thetaModel
    (F : LocalZeroFactorization) (z : ℂ) : ℂ :=
  (z - F.z0) ^ F.multiplicity * F.regular z

/-- Algebraic derivative model of the local theta factorization. -/
def LocalZeroFactorization.thetaPrimeModel
    (F : LocalZeroFactorization) (z : ℂ) : ℂ :=
  (F.multiplicity : ℂ) * (z - F.z0) ^ (F.multiplicity - 1) * F.regular z +
    (z - F.z0) ^ F.multiplicity * F.regularPrime z

/-- Local logarithmic derivative model. -/
noncomputable def LocalZeroFactorization.logDerivModel
    (F : LocalZeroFactorization) (z : ℂ) : ℂ :=
  F.thetaPrimeModel z / F.thetaModel z

/--
!!! LOCAL LOG-DERIVATIVE DECOMPOSITION
Away from the zero and away from zeros of the regular factor, the local model is
  theta'/theta = m/(z-z0) + h'/h.
This is the exact Laurent principal-part identity needed by SOLOBOLO.
-/
theorem LOCAL_LOG_DERIVATIVE_DECOMPOSITION
    (F : LocalZeroFactorization)
    (z : ℂ)
    (hz : z - F.z0 ≠ 0)
    (hh : F.regular z ≠ 0) :
    F.logDerivModel z =
      (F.multiplicity : ℂ) / (z - F.z0) +
        F.regularPrime z / F.regular z := by
  have hm : F.multiplicity ≠ 0 := Nat.ne_of_gt F.multiplicity_pos
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
  unfold LocalZeroFactorization.logDerivModel
    LocalZeroFactorization.thetaPrimeModel
    LocalZeroFactorization.thetaModel
  rw [hk]
  simp only [Nat.succ_sub_one]
  rw [pow_succ]
  field_simp [hz, hh]

/--
!!! PRINCIPAL PART IS EXACTLY THE MULTIPLICITY
After subtracting the regular logarithmic derivative, multiplication by z-z0
returns the positive integer multiplicity.
-/
theorem LOCAL_LOG_DERIVATIVE_PRINCIPAL_PART
    (F : LocalZeroFactorization)
    (z : ℂ)
    (hz : z - F.z0 ≠ 0)
    (hh : F.regular z ≠ 0) :
    (z - F.z0) *
      (F.logDerivModel z - F.regularPrime z / F.regular z) =
        (F.multiplicity : ℂ) := by
  rw [LOCAL_LOG_DERIVATIVE_DECOMPOSITION F z hz hh]
  field_simp [hz]
  ring

/--
A scalar Option-valued model of the Cayley principal term m*q/(1-r*q).
`none` records its genuine denominator pole.
-/
noncomputable def cayleyPrincipalEval
    (m : Nat) (q r : ℝ) : Option ℝ :=
  if 1 - r * q = 0 then none
  else some ((m : ℝ) * q / (1 - r * q))

/-- !!! A reciprocal Cayley radius is exactly a pole of the principal term. -/
theorem CAYLEY_PRINCIPAL_NONE_AT_RECIPROCAL
    (m : Nat) (q r : ℝ)
    (hqr : q * r = 1) :
    cayleyPrincipalEval m q r = none := by
  have hrq : r * q = 1 := by
    simpa [mul_comm] using hqr
  simp [cayleyPrincipalEval, hrq]

/--
!!! OFF-LINE ZERO -> EXPLICIT INTERIOR PRINCIPAL-TERM POLE
The entire arithmetic/Cayley part of the pole construction is now internal.
-/
theorem OFFLINE_ZERO_GIVES_CAYLEY_PRINCIPAL_POLE
    (X : CenteredXiGeometry)
    (z : X.Zero)
    (hb : X.beta z ≠ 0)
    (m : Nat) :
    InteriorRadius (X.radius z) ∧
      cayleyPrincipalEval m (X.cayleyQ z) (X.radius z) = none := by
  constructor
  · exact OFFLINE_ZERO_GIVES_INTERIOR_RADIUS X z hb
  · exact CAYLEY_PRINCIPAL_NONE_AT_RECIPROCAL m (X.cayleyQ z) (X.radius z)
      (CAYLEY_Q_MUL_RADIUS X z)

end NativeSolobolo.Derivations.Geometry
