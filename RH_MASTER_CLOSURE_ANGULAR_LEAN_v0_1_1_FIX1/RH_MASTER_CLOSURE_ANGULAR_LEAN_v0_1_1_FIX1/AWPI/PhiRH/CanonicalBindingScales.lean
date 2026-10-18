import AWPI.PhiRH.CanonicalTransverseJet

namespace AWPI.PhiRH.CanonicalBindingScales

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.ActivityFrontier
open AWPI.PhiRH.CanonicalTransverseJet

/-- Canonical choice for the previously abstract plus binding scale.
The supplied formalization imposes no independent formula on this scale at the
current frontier; only nonvanishing is required. -/
def canonicalPlusJetScale (_rho : ℂ) : ℝ := 1

/-- Canonical choice for the previously abstract minus binding scale. -/
def canonicalMinusJetScale (_rho : ℂ) : ℝ := 1

@[simp] theorem canonicalPlusJetScale_ne_zero (rho : ℂ) :
    canonicalPlusJetScale rho ≠ 0 := by
  norm_num [canonicalPlusJetScale]

@[simp] theorem canonicalMinusJetScale_ne_zero (rho : ℂ) :
    canonicalMinusJetScale rho ≠ 0 := by
  norm_num [canonicalMinusJetScale]

/-- With the two unconstrained binding factors instantiated canonically by 1,
only the three tail-side obligations remain at the terminal native-RH surface.

This removes the scale frontiers by a concrete model choice. It does not prove
that some separately defined historical binding factors equal 1; the supplied
Lean/Rocq frontier did not define such factors independently. -/
theorem MATHLIB_RH_OF_THREE_CANONICAL_SCALE_FRONTIER_LEAVES
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (plusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetPlus canonicalPlusJetScale canonicalTransverseJet rho) ^ 2 -
            (boundJetPlus canonicalPlusJetScale canonicalTransverseJet rho) ^ 2 ≤
          -(finitePlusSquare n rho) ^ 2 +
            actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im)
    (minusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetMinus canonicalMinusJetScale canonicalTransverseJet rho) ^ 2 -
            (boundJetMinus canonicalMinusJetScale canonicalTransverseJet rho) ^ 2 ≤
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
  apply CanonicalTransverseJet.MATHLIB_RH_OF_FIVE_CANONICAL_TRANSVERSE_FRONTIER_LEAVES
    canonicalPlusJetScale canonicalMinusJetScale
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho _hz
    exact canonicalPlusJetScale_ne_zero rho
  · intro rho _hz
    exact canonicalMinusJetScale_ne_zero rho
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.CanonicalBindingScales
