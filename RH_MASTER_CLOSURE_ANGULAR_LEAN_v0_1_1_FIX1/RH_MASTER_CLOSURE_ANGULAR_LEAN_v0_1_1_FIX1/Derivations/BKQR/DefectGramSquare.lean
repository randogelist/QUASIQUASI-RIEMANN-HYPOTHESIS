import Frontier.ContractiveOrbitFrontier

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo

variable {Vec : Type}
variable {Q : RealGramGeometry Vec}
variable {mu : ℝ → Nat → ℝ}

/-- Orbit vector at depth `n`. -/
def orbitVec (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) : Vec :=
  orbitIter (M.T a) n (M.u a)

/-- Q-energy of the base vector. -/
def orbitBaseEnergy (M : BKQRContractiveOrbit Q mu) (a : ℝ) : ℝ :=
  Q.normSq (M.u a)

/-- Q-energy of the depth-n orbit vector. -/
def orbitDepthEnergy (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) : ℝ :=
  Q.normSq (orbitVec M a n)

/-- Matrix coefficient at depth n. -/
def orbitCoefficient (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) : ℝ :=
  Q.inner (M.u a) (orbitVec M a n)

/-- Hopf/contraction contribution to the final defect. -/
def hopfDefect (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) : ℝ :=
  orbitBaseEnergy M a * (orbitBaseEnergy M a - orbitDepthEnergy M a n)

/-- Gram/Cauchy contribution to the final defect. -/
def gramDefect (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) : ℝ :=
  orbitBaseEnergy M a * orbitDepthEnergy M a n - orbitCoefficient M a n ^ 2

/-- The canonical two-channel BKQR defect vector. -/
noncomputable def defectGramVector
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) : ℝ × ℝ :=
  (Real.sqrt (hopfDefect M a n), Real.sqrt (gramDefect M a n))

/-- Euclidean norm-square on the two orthogonal defect channels. -/
def pairNormSq (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- !! Pointwise contractivity propagates to every orbit depth. -/
theorem ORBIT_DEPTH_ENERGY_LE_BASE
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) :
    orbitDepthEnergy M a n ≤ orbitBaseEnergy M a := by
  induction n with
  | zero =>
      simp [orbitDepthEnergy, orbitBaseEnergy, orbitVec]
  | succ n ih =>
      unfold orbitDepthEnergy orbitVec
      change Q.normSq (M.T a (orbitIter (M.T a) n (M.u a))) ≤ Q.normSq (M.u a)
      exact le_trans (M.contractive a (orbitIter (M.T a) n (M.u a))) ih

/-- !! The Hopf contraction channel is nonnegative. -/
theorem HOPF_DEFECT_NONNEGATIVE
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) :
    0 ≤ hopfDefect M a n := by
  unfold hopfDefect
  exact mul_nonneg
    (Q.normSq_nonnegative_real (M.u a))
    (sub_nonneg.mpr (ORBIT_DEPTH_ENERGY_LE_BASE M a n))

/-- !! The Gram/Cauchy channel is nonnegative. -/
theorem GRAM_DEFECT_NONNEGATIVE
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) :
    0 ≤ gramDefect M a n := by
  unfold gramDefect orbitBaseEnergy orbitDepthEnergy orbitCoefficient orbitVec
  exact sub_nonneg.mpr (Q.cauchy_sq (M.u a) (orbitIter (M.T a) n (M.u a)))

/--
!!! BKQR DEFECT-GRAM SQUARE.
The desired 2x2 determinant defect is not assumed.  It is the sum of the
Hopf contraction defect and the Gram/Cauchy defect, hence the Euclidean square
of the two-channel vector constructed above.
-/
theorem MOMENT_DEFECT_IS_BKQR_PAIR_SQUARE
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) :
    (mu a 0) ^ 2 - (mu a n) ^ 2 = pairNormSq (defectGramVector M a n) := by
  have hHopf : 0 ≤ hopfDefect M a n := HOPF_DEFECT_NONNEGATIVE M a n
  have hGram : 0 ≤ gramDefect M a n := GRAM_DEFECT_NONNEGATIVE M a n
  rw [M.base_moment a, M.moment_coeff a n]
  change
    orbitBaseEnergy M a ^ 2 - orbitCoefficient M a n ^ 2 =
      pairNormSq (defectGramVector M a n)
  unfold pairNormSq defectGramVector
  simp only [Prod.fst, Prod.snd]
  rw [Real.sq_sqrt hHopf, Real.sq_sqrt hGram]
  unfold hopfDefect gramDefect
  ring

/-- !!! Consequently every contractive BKQR orbit satisfies the 2x2 Gram defect inequality. -/
theorem MOMENT_DEFECT_NONNEGATIVE
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) :
    0 ≤ (mu a 0) ^ 2 - (mu a n) ^ 2 := by
  rw [MOMENT_DEFECT_IS_BKQR_PAIR_SQUARE M a n]
  unfold pairNormSq
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- !!! Squared matrix coefficients are bounded by the squared base moment. -/
theorem MOMENT_SQ_LE_BASE_SQ
    (M : BKQRContractiveOrbit Q mu) (a : ℝ) (n : Nat) :
    (mu a n) ^ 2 ≤ (mu a 0) ^ 2 := by
  exact sub_nonneg.mp (MOMENT_DEFECT_NONNEGATIVE M a n)

/--
!!! Widder specialization: a contractive BKQR realization of the generated
Widder tower automatically produces the desired defect square at every depth.
-/
theorem WIDDER_DEFECT_IS_BKQR_PAIR_SQUARE
    (base : ℝ → ℝ)
    (M : BKQRContractiveOrbit Q (fun a n => widderTower base n a))
    (a : ℝ) (n : Nat) :
    (widderTower base 0 a) ^ 2 - (widderTower base n a) ^ 2 =
      pairNormSq (defectGramVector M a n) := by
  exact MOMENT_DEFECT_IS_BKQR_PAIR_SQUARE M a n

end NativeSolobolo.Derivations.BKQR
