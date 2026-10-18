import Frontier.FreeEnergyFrontier

namespace NativeSolobolo

open Derivations.BKQR

/--
!! Real scalar-product geometry with the two universal Hilbert-space inequalities
needed by the BKQR defect/Gram construction.

These are geometry laws, not RH-specific positivity assumptions:
* real nonnegativity of a diagonal norm square;
* squared Cauchy--Schwarz.
-/
structure RealGramGeometry (Vec : Type) extends ScalarProductGeometry ℝ Vec where
  normSq_nonnegative_real : ∀ x : Vec, 0 ≤ normSq x
  cauchy_sq : ∀ x y : Vec, (inner x y) ^ 2 ≤ normSq x * normSq y

/-- Elementary iterate used for an abstract BKQR orbit. -/
def orbitIter {Vec : Type} (T : Vec → Vec) : Nat → Vec → Vec
  | 0, v => v
  | n + 1, v => T (orbitIter T n v)

@[simp] theorem orbitIter_zero {Vec : Type} (T : Vec → Vec) (v : Vec) :
    orbitIter T 0 v = v := rfl

@[simp] theorem orbitIter_succ {Vec : Type} (T : Vec → Vec) (n : Nat) (v : Vec) :
    orbitIter T (n + 1) v = T (orbitIter T n v) := rfl

/--
!!! BKQR CONTRACTIVE MATRIX-COEFFICIENT ORBIT.
This is the reduced analytic interface suggested by the Cayley--Widder radius
criterion.  The actual GP/Widder moment sequence is represented as
  mu_n(a) = <u_a, T_a^n u_a>_Q
with pointwise Q-contractivity of T_a.

No positivity of `mu_n`, no all-moment square hypothesis, and no final
`mu_0^2-mu_n^2` inequality is assumed.
-/
structure BKQRContractiveOrbit
    {Vec : Type}
    (Q : RealGramGeometry Vec)
    (mu : ℝ → Nat → ℝ) where
  u : ℝ → Vec
  T : ℝ → Vec → Vec
  base_moment : ∀ a : ℝ, mu a 0 = Q.normSq (u a)
  moment_coeff : ∀ a : ℝ, ∀ n : Nat,
    mu a n = Q.inner (u a) (orbitIter (T a) n (u a))
  contractive : ∀ a : ℝ, ∀ x : Vec,
    Q.normSq (T a x) ≤ Q.normSq x

namespace Frontier

/--
!!! Reduced BKQR frontier for a scalar moment family.
Construct a real Gram geometry and a contractive matrix-coefficient orbit.
The defect-square theorem is downstream and is NOT part of this frontier.
-/
def BKQRContractiveOrbitFrontier (mu : ℝ → Nat → ℝ) : Prop :=
  ∃ Vec : Type,
  ∃ Q : RealGramGeometry Vec,
    Nonempty (BKQRContractiveOrbit Q mu)

/-- Specialization to the definitionally generated Widder tower. -/
def BKQRWidderContractiveOrbitFrontier (base : ℝ → ℝ) : Prop :=
  BKQRContractiveOrbitFrontier (fun a n => widderTower base n a)

end Frontier
end NativeSolobolo
