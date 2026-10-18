import AWPI.PhiRH.LiteralModel

namespace AWPI.PhiRH.NativeLeafSurface

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.LiteralModel

universe v

/--
Minimal forward closure surface after unbundling the original supplied Lean
interfaces.  The theorem statement contains no `Constructor`,
`SourceConstructor`, `Scale2Facts`, or `NormalizedDyadicMultiplierFacts`.

The remaining hypotheses are the nine scalar/limit leaves actually consumed by
the forward closure once joint tail decay has already been established.
-/
theorem MATHLIB_RH_OF_NINE_FORWARD_LEAVES
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop)
    (finitePlusDefect finiteMinusDefect
      finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (scale2_at_zero : scale2 0 = 1)
    (scale2_strictMono : StrictMono scale2)
    (exactPlusActive :
      ∀ rho : ℂ, NontrivialZetaZero rho → 0 < energyPlus (state rho))
    (exactMinusActive :
      ∀ rho : ℂ, NontrivialZetaZero rho → 0 < energyMinus (state rho))
    (finitePlusNegativeSquare :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        finitePlusDefect n rho = -(finitePlusSquare n rho) ^ 2)
    (finiteMinusNegativeSquare :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        finiteMinusDefect n rho = -(finiteMinusSquare n rho) ^ 2)
    (plusToLimitTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) * energyPlus (state rho) -
            energyPlus (state rho) ≤
          finitePlusDefect n rho +
            plusTailSource n rho * plusTailSource n rho)
    (minusToLimitTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) * energyMinus (state rho) -
            energyMinus (state rho) ≤
          finiteMinusDefect n rho +
            minusTailSource n rho * minusTailSource n rho)
    (jointTailDecay :
      ∀ (rho : ℂ) (eps : ℝ), NontrivialZetaZero rho → 0 < eps →
        ∃ n : ℕ,
          plusTailSource n rho * plusTailSource n rho ≤ eps ∧
          minusTailSource n rho * minusTailSource n rho ≤ eps) :
    RiemannHypothesis := by
  let M : Model ℂ Jet :=
    literalZetaModel Jet state energyPlus energyMinus scale2
      plusTailSource minusTailSource sourceFormula

  have scaleFacts : Scale2Facts M := by
    refine
      { PHIRH242_SCALE2_AT_ZERO := ?_
        PHIRH243_SCALE2_STRICTLY_INCREASING := ?_ }
    · simpa [M, literalZetaModel] using scale2_at_zero
    · simpa [M, literalZetaModel] using scale2_strictMono

  have cert : ActualTailCertificate M finitePlusDefect finiteMinusDefect := by
    refine
      { exactPlusActive := ?_
        exactMinusActive := ?_
        finitePlusPassive := ?_
        finiteMinusPassive := ?_
        plusTailNonnegative := Forward.PHIRH270_ACTUAL_PLUS_TAIL_NONNEGATIVE
        minusTailNonnegative := Forward.PHIRH271_ACTUAL_MINUS_TAIL_NONNEGATIVE
        plusToLimitTailUpper := ?_
        minusToLimitTailUpper := ?_
        jointTailDecay := ?_ }
    · intro rho hz
      have hz' : NontrivialZetaZero rho := by
        simpa [M, literalZetaModel] using hz
      simpa [M, literalZetaModel, Model.exactPlusEnergy] using
        exactPlusActive rho hz'
    · intro rho hz
      have hz' : NontrivialZetaZero rho := by
        simpa [M, literalZetaModel] using hz
      simpa [M, literalZetaModel, Model.exactMinusEnergy] using
        exactMinusActive rho hz'
    · intro n rho hz
      have hz' : NontrivialZetaZero rho := by
        simpa [M, literalZetaModel] using hz
      have hsq : 0 ≤ (finitePlusSquare n rho) ^ 2 :=
        sq_nonneg (finitePlusSquare n rho)
      have hid := finitePlusNegativeSquare n rho hz'
      nlinarith
    · intro n rho hz
      have hz' : NontrivialZetaZero rho := by
        simpa [M, literalZetaModel] using hz
      have hsq : 0 ≤ (finiteMinusSquare n rho) ^ 2 :=
        sq_nonneg (finiteMinusSquare n rho)
      have hid := finiteMinusNegativeSquare n rho hz'
      nlinarith
    · intro n rho hz
      have hz' : NontrivialZetaZero rho := by
        simpa [M, literalZetaModel] using hz
      simpa [M, literalZetaModel, Model.exactPlusDefect, Model.gainPlus,
        Model.centered, Model.exactPlusEnergy, Model.plusTail] using
        plusToLimitTailUpper n rho hz'
    · intro n rho hz
      have hz' : NontrivialZetaZero rho := by
        simpa [M, literalZetaModel] using hz
      simpa [M, literalZetaModel, Model.exactMinusDefect, Model.gainMinus,
        Model.centered, Model.exactMinusEnergy, Model.minusTail] using
        minusToLimitTailUpper n rho hz'
    · intro rho eps hz heps
      have hz' : NontrivialZetaZero rho := by
        simpa [M, literalZetaModel] using hz
      simpa [M, literalZetaModel, Model.plusTail, Model.minusTail] using
        jointTailDecay rho eps hz' heps

  have hModelRH : Model.RH M :=
    Forward.PHIRH264_ACTUAL_POINTWISE_KQ_TAIL_CERTIFICATE_IMPLIES_RH
      scaleFacts cert

  apply
    (literalModel_RH_iff_mathlibRiemannHypothesis state energyPlus energyMinus
      scale2 plusTailSource minusTailSource sourceFormula).1
  simpa [M] using hModelRH

/--
Upstream-unbundled surface matching the original v0.1.4 architecture.
Instead of assuming joint tail decay directly, it exposes exactly the three
ingredients formerly hidden behind `NormalizedDyadicMultiplierFacts` and the
constructor source fields: source formula, positive-strip entry, and the
PHIRH233 implication.

No proof bundle appears in this theorem's statement.
-/
theorem MATHLIB_RH_OF_ELEVEN_UPSTREAM_LEAVES
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop)
    (finitePlusDefect finiteMinusDefect
      finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (scale2_at_zero : scale2 0 = 1)
    (scale2_strictMono : StrictMono scale2)
    (normalizedSourceFormula : sourceFormula)
    (zeroInPositiveStrip :
      ∀ rho : ℂ, NontrivialZetaZero rho → 0 < rho.re)
    (exactPlusActive :
      ∀ rho : ℂ, NontrivialZetaZero rho → 0 < energyPlus (state rho))
    (exactMinusActive :
      ∀ rho : ℂ, NontrivialZetaZero rho → 0 < energyMinus (state rho))
    (finitePlusNegativeSquare :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        finitePlusDefect n rho = -(finitePlusSquare n rho) ^ 2)
    (finiteMinusNegativeSquare :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        finiteMinusDefect n rho = -(finiteMinusSquare n rho) ^ 2)
    (plusToLimitTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) * energyPlus (state rho) -
            energyPlus (state rho) ≤
          finitePlusDefect n rho +
            plusTailSource n rho * plusTailSource n rho)
    (minusToLimitTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) * energyMinus (state rho) -
            energyMinus (state rho) ≤
          finiteMinusDefect n rho +
            minusTailSource n rho * minusTailSource n rho)
    (PHIRH233_tailDecay :
      sourceFormula →
      (∀ rho : ℂ, NontrivialZetaZero rho → 0 < rho.re) →
      ∀ (rho : ℂ) (eps : ℝ), NontrivialZetaZero rho → 0 < eps →
        ∃ n : ℕ,
          plusTailSource n rho * plusTailSource n rho ≤ eps ∧
          minusTailSource n rho * minusTailSource n rho ≤ eps) :
    RiemannHypothesis := by
  apply MATHLIB_RH_OF_NINE_FORWARD_LEAVES
    state energyPlus energyMinus scale2 plusTailSource minusTailSource
    sourceFormula finitePlusDefect finiteMinusDefect
    finitePlusSquare finiteMinusSquare
    scale2_at_zero scale2_strictMono
    exactPlusActive exactMinusActive
    finitePlusNegativeSquare finiteMinusNegativeSquare
    plusToLimitTailUpper minusToLimitTailUpper
  exact PHIRH233_tailDecay normalizedSourceFormula zeroInPositiveStrip

end AWPI.PhiRH.NativeLeafSurface
