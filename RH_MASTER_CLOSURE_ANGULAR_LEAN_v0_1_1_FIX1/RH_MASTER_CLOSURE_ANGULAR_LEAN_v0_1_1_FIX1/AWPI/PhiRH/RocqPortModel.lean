import AWPI.PhiRH.LiteralModel

namespace AWPI.PhiRH.RocqPortModel

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.LiteralModel

/-- Rocq v0.17 jet state. -/
abbrev JetState := ℝ × ℝ

/-- Rocq transverse-jet state, with the two coordinate functions left as the
    next lower-level semantic leaves. -/
def phiKQState (jetPlus jetMinus : ℂ → ℝ) (s : ℂ) : JetState :=
  (jetPlus s, jetMinus s)

/-- Rocq v0.17 plus energy. -/
def energyPlus (st : JetState) : ℝ := st.1 ^ 2

/-- Rocq v0.17 minus energy. -/
def energyMinus (st : JetState) : ℝ := st.2 ^ 2

/-- Rocq concrete scale: `Rpower 2 a`. -/
noncomputable def scale2 (a : ℝ) : ℝ := Real.rpow 2 a

/-- The easy scale leaf is discharged from Mathlib. -/
theorem scale2_at_zero : scale2 0 = 1 := by
  simp [scale2]

/-- The remaining scale-order leaf after fixing the scale function itself. -/
def Scale2StrictMono : Prop := StrictMono scale2

/-- Rocq's real-pair representation of a complex channel. -/
abbrev C2 := ℝ × ℝ

/-- Rocq v0.23 complex multiplication in real-pair coordinates. -/
def c2Mul (z w : C2) : C2 :=
  (z.1 * w.1 - z.2 * w.2,
   z.1 * w.2 + z.2 * w.1)

/-- Rocq v0.22 dyadic phase `tau * ln 2`. -/
noncomputable def dyadicPhase (tau : ℝ) : ℝ := tau * Real.log 2

/-- Rocq v0.23 normalized dyadic multiplier. -/
noncomputable def normalizedDyadicMultiplier (_sigma tau : ℝ) : C2 :=
  (Real.cos (dyadicPhase tau), -Real.sin (dyadicPhase tau))

/-- Rocq v0.21 actual KQ source pair. -/
def actualKQSourcePair
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (N : ℕ) (sigma tau : ℝ) : C2 :=
  (actualKQPlusSource N sigma tau,
   actualKQMinusSource N sigma tau)

/-- Rocq v0.21 actual Phi residual pair. -/
def actualPhiResidualPair
    (actualResidualRe actualResidualIm : ℕ → ℝ → ℝ → ℝ)
    (N : ℕ) (sigma tau : ℝ) : C2 :=
  (actualResidualRe N sigma tau,
   actualResidualIm N sigma tau)

/-- Literal Rocq v0.23 normalized dyadic source formula.  Unlike v0.1.7's
    arbitrary `sourceFormula : Prop`, this is now the exact pointwise equality
    used by the Rocq chain. -/
def ActualNormalizedDyadicMultiplierSourceFormula
    (actualKQPlusSource actualKQMinusSource
      actualResidualRe actualResidualIm : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (N : ℕ) (sigma tau : ℝ),
    actualKQSourcePair actualKQPlusSource actualKQMinusSource N sigma tau =
      c2Mul (normalizedDyadicMultiplier sigma tau)
        (actualPhiResidualPair actualResidualRe actualResidualIm N sigma tau)

/-- KQ plus source evaluated at an actual complex spectral point. -/
def actualKQPlusSourceOnComplex
    (actualKQPlusSource : ℕ → ℝ → ℝ → ℝ)
    (N : ℕ) (s : ℂ) : ℝ :=
  actualKQPlusSource N s.re s.im

/-- KQ minus source evaluated at an actual complex spectral point. -/
def actualKQMinusSourceOnComplex
    (actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (N : ℕ) (s : ℂ) : ℝ :=
  actualKQMinusSource N s.re s.im

/--
The v0.1.8 model.  Every field of `Model` is now definitionally assigned:

* zero predicate: Mathlib nontrivial zeta zero;
* real part: `Complex.re`;
* state: Rocq two-coordinate jet state;
* energies: literal coordinate squares;
* scale: `Real.rpow 2`;
* tail sources: actual KQ source coordinates on `(re,im)`;
* source formula: the literal Rocq v0.23 normalized dyadic equality.

The six function arguments are lower-level analytic data, not abstract Model
fields, and are the next disassembly frontier.
-/
noncomputable def rocqPortModel
    (jetPlus jetMinus : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource
      actualResidualRe actualResidualIm : ℕ → ℝ → ℝ → ℝ) :
    Model ℂ JetState :=
  literalZetaModel JetState
    (phiKQState jetPlus jetMinus)
    energyPlus energyMinus
    scale2
    (actualKQPlusSourceOnComplex actualKQPlusSource)
    (actualKQMinusSourceOnComplex actualKQMinusSource)
    (ActualNormalizedDyadicMultiplierSourceFormula
      actualKQPlusSource actualKQMinusSource actualResidualRe actualResidualIm)

section DefinitionalAudit

variable
    (jetPlus jetMinus : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource
      actualResidualRe actualResidualIm : ℕ → ℝ → ℝ → ℝ)

local notation "RM" =>
  rocqPortModel jetPlus jetMinus actualKQPlusSource actualKQMinusSource
    actualResidualRe actualResidualIm

@[simp] theorem rocqPortModel_state (s : ℂ) :
    Model.state RM s = (jetPlus s, jetMinus s) := by
  rfl

@[simp] theorem rocqPortModel_energyPlus (st : JetState) :
    Model.energyPlus RM st = st.1 ^ 2 := by
  rfl

@[simp] theorem rocqPortModel_energyMinus (st : JetState) :
    Model.energyMinus RM st = st.2 ^ 2 := by
  rfl

@[simp] theorem rocqPortModel_scale2 (a : ℝ) :
    Model.scale2 RM a = Real.rpow 2 a := by
  rfl

@[simp] theorem rocqPortModel_plusTailSource (N : ℕ) (s : ℂ) :
    Model.plusTailSource RM N s = actualKQPlusSource N s.re s.im := by
  rfl

@[simp] theorem rocqPortModel_minusTailSource (N : ℕ) (s : ℂ) :
    Model.minusTailSource RM N s = actualKQMinusSource N s.re s.im := by
  rfl

@[simp] theorem rocqPortModel_sourceFormula :
    Model.sourceFormula RM ↔
      ActualNormalizedDyadicMultiplierSourceFormula
        actualKQPlusSource actualKQMinusSource actualResidualRe actualResidualIm := by
  rfl

/-- Once the explicit remaining monotonicity leaf is supplied, the old bundled
    two-field scale package is reconstructed mechanically. -/
theorem scale2Facts_of_strictMono (hmono : Scale2StrictMono) : Scale2Facts RM := by
  constructor
  · exact scale2_at_zero
  · exact hmono

/-- The semantic RH endpoint remains exactly Mathlib's native proposition. -/
theorem rocqPortModel_RH_iff_mathlibRiemannHypothesis :
    Model.RH RM ↔ RiemannHypothesis := by
  exact literalModel_RH_iff_mathlibRiemannHypothesis
    (phiKQState jetPlus jetMinus)
    energyPlus energyMinus scale2
    (actualKQPlusSourceOnComplex actualKQPlusSource)
    (actualKQMinusSourceOnComplex actualKQMinusSource)
    (ActualNormalizedDyadicMultiplierSourceFormula
      actualKQPlusSource actualKQMinusSource actualResidualRe actualResidualIm)

/-- Forward terminal theorem with no abstract `Model`, no semantic bridge, no
    arbitrary energy functions, no arbitrary scale function, and no arbitrary
    source proposition. -/
theorem PHIRH286_ROCQ_PORT_MODEL_C_IMPLIES_MATHLIB_RH
    (v23 : NormalizedDyadicMultiplierFacts RM)
    (scaleStrictMono : Scale2StrictMono)
    (hC : Constructor RM) :
    RiemannHypothesis := by
  exact (rocqPortModel_RH_iff_mathlibRiemannHypothesis
    jetPlus jetMinus actualKQPlusSource actualKQMinusSource
    actualResidualRe actualResidualIm).1
      (Forward.PHIRH286_C_IMPLIES_RH v23
        (scale2Facts_of_strictMono jetPlus jetMinus actualKQPlusSource
          actualKQMinusSource actualResidualRe actualResidualIm scaleStrictMono)
        hC)

/-- Reverse endpoint at the same lower-level model surface. -/
theorem PHIRH287_ROCQ_PORT_MODEL_BACKGROUND_AND_MATHLIB_RH_IMPLIES_C
    (hB : Background RM)
    (hRH : RiemannHypothesis) :
    Constructor RM := by
  exact Reverse.PHIRH287_BACKGROUND_AND_RH_IMPLIES_C hB
    ((rocqPortModel_RH_iff_mathlibRiemannHypothesis
      jetPlus jetMinus actualKQPlusSource actualKQMinusSource
      actualResidualRe actualResidualIm).2 hRH)

/-- Constructor/RH equivalence under background, now on the explicit Rocq-port
    model and with only strict scale monotonicity exposed from `Scale2Facts`. -/
theorem rocqPortModel_constructorIffMathlibRHUnderBackground
    (v23 : NormalizedDyadicMultiplierFacts RM)
    (scaleStrictMono : Scale2StrictMono)
    (hB : Background RM) :
    Constructor RM ↔ RiemannHypothesis := by
  exact (constructorIffRHUnderBackground v23
    (scale2Facts_of_strictMono jetPlus jetMinus actualKQPlusSource
      actualKQMinusSource actualResidualRe actualResidualIm scaleStrictMono)
    hB).trans
    (rocqPortModel_RH_iff_mathlibRiemannHypothesis
      jetPlus jetMinus actualKQPlusSource actualKQMinusSource
      actualResidualRe actualResidualIm)

end DefinitionalAudit

end AWPI.PhiRH.RocqPortModel

namespace AWPI.PhiRH.RocqPortModel

/-- Mathlib discharges the final scale-order leaf for the concrete base 2
    real-power scale. -/
theorem scale2_strictMono_proved : StrictMono scale2 := by
  intro a b hab
  simpa [scale2] using
    (Real.rpow_lt_rpow_of_exponent_lt
      (x := (2 : ℝ)) (y := a) (z := b) (by norm_num) hab)

end AWPI.PhiRH.RocqPortModel
