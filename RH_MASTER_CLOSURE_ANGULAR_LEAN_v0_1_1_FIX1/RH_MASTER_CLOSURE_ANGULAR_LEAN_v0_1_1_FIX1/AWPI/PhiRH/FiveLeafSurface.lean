import AWPI.PhiRH.ConcreteLeafSurface

namespace AWPI.PhiRH.FiveLeafSurface

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.NativeLeafSurface

/--
Five-leaf native RH closure.

Compared with v0.2.3, the two finite negative-square identities are no longer
hypotheses.  The finite defects are instantiated definitionally as the
negative terminal squares themselves:

  finitePlusDefect  n rho := -(finitePlusSquare  n rho)^2
  finiteMinusDefect n rho := -(finiteMinusSquare n rho)^2.

Thus the terminal closure requires exactly five mathematical leaves:
  1. plus jet nonvanishing;
  2. minus jet nonvanishing;
  3. plus exact-to-negative-square-plus-tail upper bound;
  4. minus exact-to-negative-square-plus-tail upper bound;
  5. joint two-sided KQ tail decay.

No `Constructor`, `SourceConstructor`, model bundle, negative-square identity,
or scale hypothesis appears in the theorem statement.
-/
theorem MATHLIB_RH_OF_FIVE_CONCRETE_FORWARD_LEAVES
    (jetPlus jetMinus : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (jetPlus_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → jetPlus rho ≠ 0)
    (jetMinus_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → jetMinus rho ≠ 0)
    (plusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) * (jetPlus rho) ^ 2 -
            (jetPlus rho) ^ 2 ≤
          -(finitePlusSquare n rho) ^ 2 +
            actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im)
    (minusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) * (jetMinus rho) ^ 2 -
            (jetMinus rho) ^ 2 ≤
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
  let fdP : ℕ → ℂ → ℝ := fun n rho => -(finitePlusSquare n rho) ^ 2
  let fdM : ℕ → ℂ → ℝ := fun n rho => -(finiteMinusSquare n rho) ^ 2

  apply NativeLeafSurface.MATHLIB_RH_OF_NINE_FORWARD_LEAVES
    (phiKQState jetPlus jetMinus)
    energyPlus energyMinus scale2
    (actualKQPlusSourceOnComplex actualKQPlusSource)
    (actualKQMinusSourceOnComplex actualKQMinusSource)
    True
    fdP fdM finitePlusSquare finiteMinusSquare
  · exact scale2_at_zero
  · exact scale2_strictMono_proved
  · intro rho hz
    simpa [phiKQState, energyPlus] using
      (sq_pos_of_ne_zero (jetPlus_nonzero rho hz))
  · intro rho hz
    simpa [phiKQState, energyMinus] using
      (sq_pos_of_ne_zero (jetMinus_nonzero rho hz))
  · intro n rho _hz
    rfl
  · intro n rho _hz
    rfl
  · intro n rho hz
    simpa [fdP, phiKQState, energyPlus, actualKQPlusSourceOnComplex] using
      plusExactToNegativeSquareTailUpper n rho hz
  · intro n rho hz
    simpa [fdM, phiKQState, energyMinus, actualKQMinusSourceOnComplex] using
      minusExactToNegativeSquareTailUpper n rho hz
  · intro rho eps hz heps
    simpa [actualKQPlusSourceOnComplex, actualKQMinusSourceOnComplex] using
      jointTailDecay rho eps hz heps

end AWPI.PhiRH.FiveLeafSurface
