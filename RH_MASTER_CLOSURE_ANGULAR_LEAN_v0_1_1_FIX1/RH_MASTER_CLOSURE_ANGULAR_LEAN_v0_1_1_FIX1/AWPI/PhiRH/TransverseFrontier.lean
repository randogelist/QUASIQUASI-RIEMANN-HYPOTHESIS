import AWPI.PhiRH.ActivityFrontier

namespace AWPI.PhiRH.TransverseFrontier

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.FiveLeafSurface
open AWPI.PhiRH.ActivityFrontier

/-- Native replacement for the generic Rocq `rho_norm2` object. -/
def rhoNorm2 (rho : ℂ) : ℝ := Complex.normSq rho

/-- A genuine nontrivial Mathlib zeta zero cannot be the complex number zero,
    since Mathlib proves `riemannZeta 0 = -1/2`. -/
theorem nontrivialZetaZero_ne_zero
    (rho : ℂ) (hz : NontrivialZetaZero rho) : rho ≠ 0 := by
  intro hrho
  subst rho
  have hz0 : riemannZeta 0 = 0 := hz.1
  rw [riemannZeta_zero] at hz0
  norm_num at hz0

/-- Hence its complex norm-square is strictly positive.  This discharges the
    generic Rocq positive-real-part route at the native Mathlib endpoint. -/
theorem rhoNorm2_pos_of_nontrivialZetaZero
    (rho : ℂ) (hz : NontrivialZetaZero rho) : 0 < rhoNorm2 rho := by
  unfold rhoNorm2
  exact (RCLike.normSq_pos).2 (nontrivialZetaZero_ne_zero rho hz)

/-- Rocq PHIRH149, specialized to native Mathlib zeros: once the shifted-slice
    norm is positive and the concrete transverse identity holds, the
    transverse jet is nonzero.  No positive-real-part hypothesis is needed. -/
theorem transverseJet_nonzero_of_shifted_norm_identity
    (phiTransverseJet shiftedPhiNorm2 : ℂ → ℝ)
    (rho : ℂ)
    (hz : NontrivialZetaZero rho)
    (hshift : 0 < shiftedPhiNorm2 rho)
    (hidentity :
      phiTransverseJet rho = rhoNorm2 rho * shiftedPhiNorm2 rho) :
    phiTransverseJet rho ≠ 0 := by
  rw [hidentity]
  exact ne_of_gt <| mul_pos (rhoNorm2_pos_of_nontrivialZetaZero rho hz) hshift

/--
Native RH closure with the direct transverse-nonzero leaf removed.

The old leaf
  phiTransverseJet rho != 0
is now derived from the two true lower transverse frontiers appearing in the
supplied Rocq atlas:
  * shifted Phi slice norm-square positive;
  * concrete transverse identity.

The generic positive-real-part premise used in Rocq is discharged natively by
`riemannZeta_zero` and positivity of `Complex.normSq`.
-/
theorem MATHLIB_RH_OF_SEVEN_TRUE_TRANSVERSE_FRONTIER_LEAVES
    (phiTransverseJet shiftedPhiNorm2 plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (shiftedPhiNorm2_positive :
      ∀ rho : ℂ, NontrivialZetaZero rho → 0 < shiftedPhiNorm2 rho)
    (transverseNorm2_identity :
      ∀ rho : ℂ, NontrivialZetaZero rho →
        phiTransverseJet rho = rhoNorm2 rho * shiftedPhiNorm2 rho)
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
  apply MATHLIB_RH_OF_SIX_ACTIVITY_FRONTIER_LEAVES
    phiTransverseJet plusJetScale minusJetScale
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho hz
    exact transverseJet_nonzero_of_shifted_norm_identity
      phiTransverseJet shiftedPhiNorm2 rho hz
      (shiftedPhiNorm2_positive rho hz)
      (transverseNorm2_identity rho hz)
  · exact plusBindingScale_nonzero
  · exact minusBindingScale_nonzero
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.TransverseFrontier
