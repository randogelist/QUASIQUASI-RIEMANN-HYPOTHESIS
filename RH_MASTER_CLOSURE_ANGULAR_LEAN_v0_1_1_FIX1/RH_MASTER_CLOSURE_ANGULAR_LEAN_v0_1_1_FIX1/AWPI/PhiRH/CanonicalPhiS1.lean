import AWPI.PhiRH.PhiS1Series

namespace AWPI.PhiRH.CanonicalPhiS1

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.NativeZetaSupport
open AWPI.PhiRH.S1Prefactor
open AWPI.PhiRH.PhiS1Series
open AWPI.PhiRH.ShiftedSliceFrontier
open AWPI.PhiRH.TransverseFrontier
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.ActivityFrontier

/-- Canonical migrated u=1 Phi value, defined directly from the paired cell sum.

Each pair is
  4 * 2^(-s) * ((2k+1)^(-s) - (2k+2)^(-s)),
which is exactly the paired form of the supplied alternating u=1 cell series.
This definition does not mention zeta. -/
noncomputable def canonicalPhiS1 (s : ℂ) : ℂ :=
  ∑' (k : ℕ),
    ((4 : ℂ) * ((2 : ℂ) ^ (-s))) *
      (dirichletTerm s (2 * k) - dirichletTerm s (2 * k + 1))

/-- In the half-plane of absolute convergence, the direct paired-cell sum is
exactly the factorized `phiS1CellSeries` used in v0.2.10. -/
theorem canonicalPhiS1_eq_phiS1CellSeries {s : ℂ} (hs : 1 < s.re) :
    canonicalPhiS1 s = phiS1CellSeries s := by
  unfold canonicalPhiS1 phiS1CellSeries etaPairSeries
  rw [tsum_mul_left]

/-- Hence the canonical migrated Phi slice satisfies the S1-zeta factorization
on the absolute-convergence half-plane. -/
theorem canonicalPhiS1_eq_s1Prefactor_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    canonicalPhiS1 s = s1Prefactor s * riemannZeta s := by
  rw [canonicalPhiS1_eq_phiS1CellSeries hs]
  exact phiS1CellSeries_eq_s1Prefactor_mul_zeta hs

/-- At the shifted point of every nontrivial zeta zero, the canonical migrated
Phi slice has the exact S1 factorization. -/
theorem shifted_canonicalPhiS1_factorization
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    canonicalPhiS1 (rho + 1) =
      s1Prefactor (rho + 1) * riemannZeta (rho + 1) := by
  have hre : 0 < rho.re := nontrivialZetaZero_re_pos rho hz
  have hs : 1 < (rho + 1).re := by
    simpa using add_lt_add_right hre 1
  exact canonicalPhiS1_eq_s1Prefactor_mul_zeta hs

/-- The shifted-slice nonvanishing theorem is now premise-free for the
canonical migrated Phi slice. -/
theorem shifted_canonicalPhiS1_ne_zero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    canonicalPhiS1 (rho + 1) ≠ 0 := by
  exact shiftedSlice_nonzero_of_phi_zeta_value_identity
    canonicalPhiS1 rho hz (shifted_canonicalPhiS1_factorization rho hz)

/-- Native RH closure after the Phi-S1 cell-series binding frontier has vanished.

The shifted Phi object is no longer a parameter: it is the canonical paired
cell sum `canonicalPhiS1`, derived from the supplied u=1 cells.  The remaining
frontiers are exactly:
  1. transverse norm-square identity;
  2. plus binding-scale nonvanishing;
  3. minus binding-scale nonvanishing;
  4. plus exact-to-negative-square tail upper bound;
  5. minus exact-to-negative-square tail upper bound;
  6. joint KQ tail decay.
-/
theorem MATHLIB_RH_OF_SIX_CANONICAL_PHI_FRONTIER_LEAVES
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (transverseNorm2_identity :
      ∀ rho : ℂ, NontrivialZetaZero rho →
        phiTransverseJet rho =
          rhoNorm2 rho * shiftedPhiNorm2 canonicalPhiS1 rho)
    (plusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → plusJetScale rho ≠ 0)
    (minusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → minusJetScale rho ≠ 0)
    (plusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetPlus plusJetScale phiTransverseJet rho) ^ 2 -
            (boundJetPlus plusJetScale phiTransverseJet rho) ^ 2 ≤
          -(finitePlusSquare n rho) ^ 2 +
            actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im)
    (minusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetMinus minusJetScale phiTransverseJet rho) ^ 2 -
            (boundJetMinus minusJetScale phiTransverseJet rho) ^ 2 ≤
          -(finiteMinusSquare n rho) ^ 2 +
            actualKQMinusSource n rho.re rho.im *
              actualKQMinusSource n rho.re rho.im)
    (jointTailDecay :
      ∀ (rho : ℂ) (eps : ℝ), NontrivialZetaZero rho → 0 < eps →
        ∃ n : ℕ,
          actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im ≤ eps ∧
          actualKQMinusSource n rho.re rho.im *
              actualKQMinusSource n rho.re rho.im ≤ eps) :
    RiemannHypothesis := by
  apply MATHLIB_RH_OF_SEVEN_SHIFTED_SLICE_FRONTIER_LEAVES
    canonicalPhiS1 phiTransverseJet plusJetScale minusJetScale
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho hz
    exact shifted_canonicalPhiS1_ne_zero rho hz
  · exact transverseNorm2_identity
  · exact plusBindingScale_nonzero
  · exact minusBindingScale_nonzero
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.CanonicalPhiS1
