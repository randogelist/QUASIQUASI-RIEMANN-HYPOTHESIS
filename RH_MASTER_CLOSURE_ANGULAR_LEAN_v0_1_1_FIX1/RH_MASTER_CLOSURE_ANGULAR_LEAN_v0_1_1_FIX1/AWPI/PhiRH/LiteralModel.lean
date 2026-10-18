import AWPI.PhiRH.MathlibBridge

namespace AWPI.PhiRH.LiteralModel

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge

universe v

/--
The generic model with the two RH-semantic fields made literal:
* `isZero` is Mathlib's nontrivial Riemann-zeta-zero predicate;
* `rePart` is `Complex.re`.

The seven remaining model components are still explicit arguments and therefore
remain visible frontiers for later disassembly.
-/
def literalZetaModel
    (Jet : Type v)
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop) : Model ℂ Jet where
  isZero := NontrivialZetaZero
  rePart := fun s => s.re
  state := state
  energyPlus := energyPlus
  energyMinus := energyMinus
  scale2 := scale2
  plusTailSource := plusTailSource
  minusTailSource := minusTailSource
  sourceFormula := sourceFormula

@[simp] theorem literalZetaModel_isZero
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop)
    (s : ℂ) :
    (literalZetaModel Jet state energyPlus energyMinus scale2
      plusTailSource minusTailSource sourceFormula).isZero s ↔
      NontrivialZetaZero s := by
  rfl

@[simp] theorem literalZetaModel_rePart
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop)
    (s : ℂ) :
    (literalZetaModel Jet state energyPlus energyMinus scale2
      plusTailSource minusTailSource sourceFormula).rePart s = s.re := by
  rfl

/-- The Z→ semantic leaf is discharged definitionally for the literal model. -/
theorem literalModel_modelZero_to_zetaZero
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop) :
    ModelZeroImpliesNontrivialZetaZero
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula) := by
  intro s hs
  exact hs

/-- The Z← semantic leaf is discharged definitionally for the literal model. -/
theorem literalModel_zetaZero_to_modelZero
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop) :
    NontrivialZetaZeroImpliesModelZero
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula) := by
  intro s hs
  exact hs

/-- The real-coordinate semantic leaf is discharged definitionally. -/
theorem literalModel_rePart_is_complexRe
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop) :
    ModelRePartIsComplexRe
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula) := by
  intro s
  rfl

/-- For the literal model, generic `Model.RH` is exactly Mathlib RH without
    any semantic bridge premise. -/
theorem literalModel_RH_iff_mathlibRiemannHypothesis
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop) :
    (literalZetaModel Jet state energyPlus energyMinus scale2
      plusTailSource minusTailSource sourceFormula).RH ↔
      RiemannHypothesis := by
  exact modelRH_iff_mathlibRiemannHypothesis_of_semantic_leaves
    (literalModel_modelZero_to_zetaZero state energyPlus energyMinus scale2
      plusTailSource minusTailSource sourceFormula)
    (literalModel_zetaZero_to_modelZero state energyPlus energyMinus scale2
      plusTailSource minusTailSource sourceFormula)
    (literalModel_rePart_is_complexRe state energyPlus energyMinus scale2
      plusTailSource minusTailSource sourceFormula)

/-- Forward endpoint with the abstract `Model` parameter and all three semantic
    leaf premises removed. Seven model components remain explicit. -/
theorem PHIRH286_LITERAL_MODEL_C_IMPLIES_MATHLIB_RH
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop)
    (v23 : NormalizedDyadicMultiplierFacts
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula))
    (scaleFacts : Scale2Facts
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula))
    (hC : Constructor
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula)) :
    RiemannHypothesis := by
  apply (literalModel_RH_iff_mathlibRiemannHypothesis state energyPlus energyMinus
    scale2 plusTailSource minusTailSource sourceFormula).1
  exact Forward.PHIRH286_C_IMPLIES_RH v23 scaleFacts hC

/-- Reverse endpoint with the abstract `Model` parameter and semantic leaves
    removed. -/
theorem PHIRH287_LITERAL_MODEL_BACKGROUND_AND_MATHLIB_RH_IMPLIES_C
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop)
    (hB : Background
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula))
    (hRH : RiemannHypothesis) :
    Constructor
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula) := by
  apply Reverse.PHIRH287_BACKGROUND_AND_RH_IMPLIES_C hB
  exact (literalModel_RH_iff_mathlibRiemannHypothesis state energyPlus energyMinus
    scale2 plusTailSource minusTailSource sourceFormula).2 hRH

/-- Literal-model equivalence under the existing background package. -/
theorem literalModel_constructorIffMathlibRHUnderBackground
    {Jet : Type v}
    (state : ℂ → Jet)
    (energyPlus energyMinus : Jet → ℝ)
    (scale2 : ℝ → ℝ)
    (plusTailSource minusTailSource : ℕ → ℂ → ℝ)
    (sourceFormula : Prop)
    (v23 : NormalizedDyadicMultiplierFacts
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula))
    (scaleFacts : Scale2Facts
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula))
    (hB : Background
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula)) :
    Constructor
      (literalZetaModel Jet state energyPlus energyMinus scale2
        plusTailSource minusTailSource sourceFormula) ↔
      RiemannHypothesis := by
  exact (constructorIffRHUnderBackground v23 scaleFacts hB).trans
    (literalModel_RH_iff_mathlibRiemannHypothesis state energyPlus energyMinus
      scale2 plusTailSource minusTailSource sourceFormula)

end AWPI.PhiRH.LiteralModel
