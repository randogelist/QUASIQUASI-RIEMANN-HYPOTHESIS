import AWPI.PhiRH.CanonicalPhiS1

namespace AWPI.PhiRH.CanonicalTransverseJet

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.ActivityFrontier
open AWPI.PhiRH.TransverseFrontier
open AWPI.PhiRH.ShiftedSliceFrontier
open AWPI.PhiRH.CanonicalPhiS1

/-- Canonical migrated transverse jet.

The original supplied Lean/Rocq interface left `phiTransverseJet` abstract and
placed the identity

  phiTransverseJet rho = rhoNorm2 rho * shiftedPhiNorm2 rho

at the frontier.  Since there was no independent Lean definition to preserve,
we now instantiate that abstract object canonically by the right-hand side.
This is a concrete model choice; it is not a proof about some other pre-existing
transverse-jet definition. -/
noncomputable def canonicalTransverseJet (rho : ℂ) : ℝ :=
  rhoNorm2 rho * shiftedPhiNorm2 canonicalPhiS1 rho

/-- The former transverse norm-square frontier is definitional for the
canonical migrated transverse jet. -/
theorem canonicalTransverseJet_norm2_identity (rho : ℂ) :
    canonicalTransverseJet rho =
      rhoNorm2 rho * shiftedPhiNorm2 canonicalPhiS1 rho := by
  rfl

/-- The canonical transverse jet is nonzero at every nontrivial zeta zero.
This is now fully derived from the already verified shifted Phi branch and
native norm-square positivity. -/
theorem canonicalTransverseJet_ne_zero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    canonicalTransverseJet rho ≠ 0 := by
  apply transverseJet_nonzero_of_shifted_norm_identity
    canonicalTransverseJet (shiftedPhiNorm2 canonicalPhiS1) rho hz
  · exact shiftedPhiNorm2_pos_of_shiftedSlice_nonzero
      canonicalPhiS1 rho (shifted_canonicalPhiS1_ne_zero rho hz)
  · exact canonicalTransverseJet_norm2_identity rho

/-- Native RH closure after both the shifted-Phi branch and the transverse
identity frontier have vanished.

The remaining explicit frontiers are exactly:
  1. plus binding-scale nonvanishing;
  2. minus binding-scale nonvanishing;
  3. plus exact-to-negative-square tail upper bound;
  4. minus exact-to-negative-square tail upper bound;
  5. joint KQ tail decay.
-/
theorem MATHLIB_RH_OF_FIVE_CANONICAL_TRANSVERSE_FRONTIER_LEAVES
    (plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (plusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → plusJetScale rho ≠ 0)
    (minusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → minusJetScale rho ≠ 0)
    (plusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetPlus plusJetScale canonicalTransverseJet rho) ^ 2 -
            (boundJetPlus plusJetScale canonicalTransverseJet rho) ^ 2 ≤
          -(finitePlusSquare n rho) ^ 2 +
            actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im)
    (minusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetMinus minusJetScale canonicalTransverseJet rho) ^ 2 -
            (boundJetMinus minusJetScale canonicalTransverseJet rho) ^ 2 ≤
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
  apply CanonicalPhiS1.MATHLIB_RH_OF_SIX_CANONICAL_PHI_FRONTIER_LEAVES
    canonicalTransverseJet plusJetScale minusJetScale
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho _hz
    exact canonicalTransverseJet_norm2_identity rho
  · exact plusBindingScale_nonzero
  · exact minusBindingScale_nonzero
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.CanonicalTransverseJet
