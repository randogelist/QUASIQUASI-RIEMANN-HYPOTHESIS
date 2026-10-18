import AWPI.PhiRH.NativeLeafSurface
import AWPI.PhiRH.RocqPortModel

namespace AWPI.PhiRH.ConcreteLeafSurface

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.NativeLeafSurface
open AWPI.PhiRH.RocqPortModel

/--
Concrete forward endpoint after discharging the two scale leaves and reducing
square-energy activity to nonvanishing of the two actual jet coordinates.

Exactly seven mathematical closure leaves remain in the theorem statement:
  1. plus jet nonvanishing on nontrivial zeta zeros;
  2. minus jet nonvanishing on nontrivial zeta zeros;
  3-4. the two finite negative-square identities;
  5-6. the two exact-to-finite tail upper bounds;
  7. joint two-sided KQ tail decay.

The four source/residual functions are retained only to instantiate the same
concrete Rocq-port model; once joint tail decay is supplied directly, the
normalized source formula is not otherwise consumed by the terminal closure.
-/
theorem MATHLIB_RH_OF_SEVEN_CONCRETE_FORWARD_LEAVES
    (jetPlus jetMinus : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource
      actualResidualRe actualResidualIm : ℕ → ℝ → ℝ → ℝ)
    (finitePlusDefect finiteMinusDefect
      finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (jetPlus_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → jetPlus rho ≠ 0)
    (jetMinus_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → jetMinus rho ≠ 0)
    (finitePlusNegativeSquare :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        finitePlusDefect n rho = -(finitePlusSquare n rho) ^ 2)
    (finiteMinusNegativeSquare :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        finiteMinusDefect n rho = -(finiteMinusSquare n rho) ^ 2)
    (plusToLimitTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) * (jetPlus rho) ^ 2 -
            (jetPlus rho) ^ 2 ≤
          finitePlusDefect n rho +
            actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im)
    (minusToLimitTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) * (jetMinus rho) ^ 2 -
            (jetMinus rho) ^ 2 ≤
          finiteMinusDefect n rho +
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
  apply MATHLIB_RH_OF_NINE_FORWARD_LEAVES
    (phiKQState jetPlus jetMinus)
    energyPlus energyMinus scale2
    (actualKQPlusSourceOnComplex actualKQPlusSource)
    (actualKQMinusSourceOnComplex actualKQMinusSource)
    (ActualNormalizedDyadicMultiplierSourceFormula
      actualKQPlusSource actualKQMinusSource actualResidualRe actualResidualIm)
    finitePlusDefect finiteMinusDefect finitePlusSquare finiteMinusSquare
  · exact scale2_at_zero
  · exact scale2_strictMono_proved
  · intro rho hz
    simpa [phiKQState, energyPlus] using
      (sq_pos_of_ne_zero (jetPlus_nonzero rho hz))
  · intro rho hz
    simpa [phiKQState, energyMinus] using
      (sq_pos_of_ne_zero (jetMinus_nonzero rho hz))
  · exact finitePlusNegativeSquare
  · exact finiteMinusNegativeSquare
  · intro n rho hz
    simpa [phiKQState, energyPlus, actualKQPlusSourceOnComplex] using
      plusToLimitTailUpper n rho hz
  · intro n rho hz
    simpa [phiKQState, energyMinus, actualKQMinusSourceOnComplex] using
      minusToLimitTailUpper n rho hz
  · intro rho eps hz heps
    simpa [actualKQPlusSourceOnComplex, actualKQMinusSourceOnComplex] using
      jointTailDecay rho eps hz heps

end AWPI.PhiRH.ConcreteLeafSurface
