import Mathlib

namespace AWPI.PhiRH

universe u v

/-- Shared model.  Compared with v0.1.2, the geometry and KQ tails are now
    definitions rather than opaque fields, matching Rocq v0.20/v0.24. -/
structure Model (Point : Type u) (Jet : Type v) where
  isZero : Point → Prop
  rePart : Point → ℝ
  state : Point → Jet
  energyPlus : Jet → ℝ
  energyMinus : Jet → ℝ
  scale2 : ℝ → ℝ
  plusTailSource : ℕ → Point → ℝ
  minusTailSource : ℕ → Point → ℝ
  sourceFormula : Prop

namespace Model

variable {Point : Type u} {Jet : Type v} (M : Model Point Jet)

noncomputable def centered (rho : Point) : ℝ := M.rePart rho - (1 / 2 : ℝ)

def criticalLine (rho : Point) : Prop := M.rePart rho = (1 / 2 : ℝ)

def positiveStrip (rho : Point) : Prop := 0 < M.rePart rho

/-- Rocq v0.24: forward_gain rho = scale2 (2 * centered rho). -/
noncomputable def gainPlus (rho : Point) : ℝ := M.scale2 (2 * M.centered rho)

/-- Rocq v0.24: backward_gain rho = scale2 (-2 * centered rho). -/
noncomputable def gainMinus (rho : Point) : ℝ := M.scale2 (-2 * M.centered rho)

/-- Rocq v0.20 actual_kq_plus_tail: a literal square. -/
def plusTail (n : ℕ) (rho : Point) : ℝ :=
  M.plusTailSource n rho * M.plusTailSource n rho

/-- Rocq v0.20 actual_kq_minus_tail: a literal square. -/
def minusTail (n : ℕ) (rho : Point) : ℝ :=
  M.minusTailSource n rho * M.minusTailSource n rho

def exactPlusEnergy (rho : Point) : ℝ := M.energyPlus (M.state rho)

def exactMinusEnergy (rho : Point) : ℝ := M.energyMinus (M.state rho)

noncomputable def exactPlusDefect (rho : Point) : ℝ :=
  M.gainPlus rho * M.exactPlusEnergy rho - M.exactPlusEnergy rho

noncomputable def exactMinusDefect (rho : Point) : ℝ :=
  M.gainMinus rho * M.exactMinusEnergy rho - M.exactMinusEnergy rho

def RH : Prop := ∀ rho : Point, M.isZero rho → M.criticalLine rho

end Model

/-- Only the two scale facts used by the Rocq v0.24 closure are left abstract.
    They correspond exactly to PHIRH242 and PHIRH243. -/
structure Scale2Facts {Point : Type u} {Jet : Type v} (M : Model Point Jet) : Prop where
  PHIRH242_SCALE2_AT_ZERO : M.scale2 0 = 1
  PHIRH243_SCALE2_STRICTLY_INCREASING : StrictMono M.scale2

/-- Imported v0.23 boundary.  This is the one genuinely upstream analytic fact
    still abstract in this slice: PHIRH233. -/
structure NormalizedDyadicMultiplierFacts
    {Point : Type u} {Jet : Type v} (M : Model Point Jet) : Prop where
  PHIRH233_NORMALIZED_DYADIC_MULTIPLIER_SOURCE_GIVES_TAIL_DECAY :
    M.sourceFormula →
    (∀ rho : Point, M.isZero rho → M.positiveStrip rho) →
    ∀ (rho : Point) (eps : ℝ),
      M.isZero rho → 0 < eps →
      ∃ n : ℕ, M.plusTail n rho ≤ eps ∧ M.minusTail n rho ≤ eps

/-- Rocq v0.28 background package B. -/
structure Background {Point : Type u} {Jet : Type v} (M : Model Point Jet) : Prop where
  normalizedSourceFormula : M.sourceFormula
  zeroInPositiveStrip : ∀ rho : Point, M.isZero rho → M.positiveStrip rho
  exactPlusActive : ∀ rho : Point, M.isZero rho → 0 < M.exactPlusEnergy rho
  exactMinusActive : ∀ rho : Point, M.isZero rho → 0 < M.exactMinusEnergy rho
  criticalLineForwardGainOne :
    ∀ rho : Point, M.criticalLine rho → M.gainPlus rho = 1
  criticalLineBackwardGainOne :
    ∀ rho : Point, M.criticalLine rho → M.gainMinus rho = 1

/-- Lean counterpart of v0.26 ActualPointwiseSourceConstructor. -/
structure SourceConstructor
    {Point : Type u} {Jet : Type v} (M : Model Point Jet)
    (finitePlusDefect finiteMinusDefect
      finitePlusSquare finiteMinusSquare : ℕ → Point → ℝ) : Prop where
  normalizedSourceFormula : M.sourceFormula
  zeroInPositiveStrip : ∀ rho : Point, M.isZero rho → M.positiveStrip rho
  exactPlusActive : ∀ rho : Point, M.isZero rho → 0 < M.exactPlusEnergy rho
  exactMinusActive : ∀ rho : Point, M.isZero rho → 0 < M.exactMinusEnergy rho
  finitePlusNegativeSquare :
    ∀ (n : ℕ) (rho : Point), M.isZero rho →
      finitePlusDefect n rho = -(finitePlusSquare n rho) ^ 2
  finiteMinusNegativeSquare :
    ∀ (n : ℕ) (rho : Point), M.isZero rho →
      finiteMinusDefect n rho = -(finiteMinusSquare n rho) ^ 2
  plusToLimitTailUpper :
    ∀ (n : ℕ) (rho : Point), M.isZero rho →
      M.exactPlusDefect rho ≤ finitePlusDefect n rho + M.plusTail n rho
  minusToLimitTailUpper :
    ∀ (n : ℕ) (rho : Point), M.isZero rho →
      M.exactMinusDefect rho ≤ finiteMinusDefect n rho + M.minusTail n rho

/-- Lean counterpart of v0.25 ActualPointwiseKQTailCertificate. -/
structure ActualTailCertificate
    {Point : Type u} {Jet : Type v} (M : Model Point Jet)
    (finitePlusDefect finiteMinusDefect : ℕ → Point → ℝ) : Prop where
  exactPlusActive : ∀ rho : Point, M.isZero rho → 0 < M.exactPlusEnergy rho
  exactMinusActive : ∀ rho : Point, M.isZero rho → 0 < M.exactMinusEnergy rho
  finitePlusPassive :
    ∀ (n : ℕ) (rho : Point), M.isZero rho → finitePlusDefect n rho ≤ 0
  finiteMinusPassive :
    ∀ (n : ℕ) (rho : Point), M.isZero rho → finiteMinusDefect n rho ≤ 0
  plusTailNonnegative : ∀ (n : ℕ) (rho : Point), 0 ≤ M.plusTail n rho
  minusTailNonnegative : ∀ (n : ℕ) (rho : Point), 0 ≤ M.minusTail n rho
  plusToLimitTailUpper :
    ∀ (n : ℕ) (rho : Point), M.isZero rho →
      M.exactPlusDefect rho ≤ finitePlusDefect n rho + M.plusTail n rho
  minusToLimitTailUpper :
    ∀ (n : ℕ) (rho : Point), M.isZero rho →
      M.exactMinusDefect rho ≤ finiteMinusDefect n rho + M.minusTail n rho
  jointTailDecay :
    ∀ (rho : Point) (eps : ℝ), M.isZero rho → 0 < eps →
      ∃ n : ℕ, M.plusTail n rho ≤ eps ∧ M.minusTail n rho ≤ eps

/-- v0.28/v0.29 existential constructor statement C. -/
def Constructor {Point : Type u} {Jet : Type v} (M : Model Point Jet) : Prop :=
  ∃ finitePlusDefect finiteMinusDefect
      finitePlusSquare finiteMinusSquare : ℕ → Point → ℝ,
    SourceConstructor M
      finitePlusDefect finiteMinusDefect
      finitePlusSquare finiteMinusSquare

/-- Exact two-sided passivity used by Rocq v0.29. -/
def ExactTwoSidedPassivity
    {Point : Type u} {Jet : Type v} (M : Model Point Jet) : Prop :=
  ∀ rho : Point, M.isZero rho →
    M.exactPlusDefect rho ≤ 0 ∧ M.exactMinusDefect rho ≤ 0

end AWPI.PhiRH
