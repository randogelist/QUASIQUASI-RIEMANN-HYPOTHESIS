import AWPI.PhiRH.TransverseFrontier

namespace AWPI.PhiRH.ShiftedSliceFrontier

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.FiveLeafSurface
open AWPI.PhiRH.ActivityFrontier
open AWPI.PhiRH.TransverseFrontier

/-- Literal shifted-slice norm-square.  The current native Lean frontier uses
    the actual complex shifted value rather than an arbitrary positive real
    observable. -/
def shiftedPhiNorm2 (phiS1 : ℂ → ℂ) (rho : ℂ) : ℝ :=
  Complex.normSq (phiS1 (rho + 1))

/-- Mathlib turns nonvanishing of the shifted complex Phi value directly into
    strict positivity of its norm-square.  Thus the former
    `shiftedPhiNorm2_positive` premise disappears. -/
theorem shiftedPhiNorm2_pos_of_shiftedSlice_nonzero
    (phiS1 : ℂ → ℂ) (rho : ℂ)
    (hshift : phiS1 (rho + 1) ≠ 0) :
    0 < shiftedPhiNorm2 phiS1 rho := by
  unfold shiftedPhiNorm2
  exact (RCLike.normSq_pos).2 hshift

/--
Native RH closure with the arbitrary shifted-norm positivity premise removed.

The shifted analytic input is now exactly the theorem-atlas frontier
`Phi(1,rho+1) != 0`, represented by `phiS1 (rho + 1) != 0`.  Its norm-square
positivity is derived by Mathlib.
-/
theorem MATHLIB_RH_OF_SEVEN_SHIFTED_SLICE_FRONTIER_LEAVES
    (phiS1 : ℂ → ℂ)
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (shiftedSlice_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → phiS1 (rho + 1) ≠ 0)
    (transverseNorm2_identity :
      ∀ rho : ℂ, NontrivialZetaZero rho →
        phiTransverseJet rho = rhoNorm2 rho * shiftedPhiNorm2 phiS1 rho)
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
  apply MATHLIB_RH_OF_SEVEN_TRUE_TRANSVERSE_FRONTIER_LEAVES
    phiTransverseJet (shiftedPhiNorm2 phiS1) plusJetScale minusJetScale
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho hz
    exact shiftedPhiNorm2_pos_of_shiftedSlice_nonzero
      phiS1 rho (shiftedSlice_nonzero rho hz)
  · exact transverseNorm2_identity
  · exact plusBindingScale_nonzero
  · exact minusBindingScale_nonzero
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.ShiftedSliceFrontier
