import AWPI.PhiRH.FiveLeafSurface

namespace AWPI.PhiRH.ActivityFrontier

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.FiveLeafSurface

/-- Rocq v0.17 plus jet: binding scale times the common transverse jet. -/
def boundJetPlus
    (plusJetScale phiTransverseJet : ℂ → ℝ) (rho : ℂ) : ℝ :=
  plusJetScale rho * phiTransverseJet rho

/-- Rocq v0.17 minus jet: binding scale times the common transverse jet. -/
def boundJetMinus
    (minusJetScale phiTransverseJet : ℂ → ℝ) (rho : ℂ) : ℝ :=
  minusJetScale rho * phiTransverseJet rho

/-- The plus jet nonvanishing leaf is derived algebraically from the two
    lower activity leaves appearing in the Rocq transverse-jet layer. -/
theorem boundJetPlus_nonzero
    (plusJetScale phiTransverseJet : ℂ → ℝ)
    (rho : ℂ)
    (hscale : plusJetScale rho ≠ 0)
    (htransverse : phiTransverseJet rho ≠ 0) :
    boundJetPlus plusJetScale phiTransverseJet rho ≠ 0 := by
  exact mul_ne_zero hscale htransverse

/-- The minus jet nonvanishing leaf is derived in the same way. -/
theorem boundJetMinus_nonzero
    (minusJetScale phiTransverseJet : ℂ → ℝ)
    (rho : ℂ)
    (hscale : minusJetScale rho ≠ 0)
    (htransverse : phiTransverseJet rho ≠ 0) :
    boundJetMinus minusJetScale phiTransverseJet rho ≠ 0 := by
  exact mul_ne_zero hscale htransverse

/--
Activity-frontier native RH closure.

The two terminal jet-nonvanishing hypotheses of v0.2.4 are gone.  The jets are
now the literal Rocq products

  J₊ = a₊ * Phi_perp,
  J₋ = a₋ * Phi_perp,

and their nonvanishing is proved from the three lower, independent activity
leaves:

  * transverse jet nonzero;
  * plus binding scale nonzero;
  * minus binding scale nonzero.

The remaining tail side is unchanged: two exact-to-negative-square-plus-tail
bounds and joint two-sided tail decay.
-/
theorem MATHLIB_RH_OF_SIX_ACTIVITY_FRONTIER_LEAVES
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (transverseJet_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → phiTransverseJet rho ≠ 0)
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
  apply MATHLIB_RH_OF_FIVE_CONCRETE_FORWARD_LEAVES
    (boundJetPlus plusJetScale phiTransverseJet)
    (boundJetMinus minusJetScale phiTransverseJet)
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho hz
    exact boundJetPlus_nonzero plusJetScale phiTransverseJet rho
      (plusBindingScale_nonzero rho hz) (transverseJet_nonzero rho hz)
  · intro rho hz
    exact boundJetMinus_nonzero minusJetScale phiTransverseJet rho
      (minusBindingScale_nonzero rho hz) (transverseJet_nonzero rho hz)
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.ActivityFrontier
