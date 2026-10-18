import AWPI.PhiRH.RocqPortModel

namespace AWPI.PhiRH.RocqSourceLayer

open AWPI.PhiRH

/-- Rocq v0.17: plus jet is the plus scale times the transverse jet. -/
def jetPlus
    (phiTransverseJet plusJetScale : ℂ → ℝ) (s : ℂ) : ℝ :=
  plusJetScale s * phiTransverseJet s

/-- Rocq v0.17: minus jet is the minus scale times the transverse jet. -/
def jetMinus
    (phiTransverseJet minusJetScale : ℂ → ℝ) (s : ℂ) : ℝ :=
  minusJetScale s * phiTransverseJet s

/-- Rocq v0.17 state after disassembling `jetPlus` and `jetMinus`. -/
def phiKQState
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ) (s : ℂ) : AWPI.PhiRH.RocqPortModel.JetState :=
  (jetPlus phiTransverseJet plusJetScale s,
   jetMinus phiTransverseJet minusJetScale s)

/-- Rocq v0.17 alternating sign. -/
def altSign : ℕ → ℝ
  | 0 => 1
  | Nat.succ n => - altSign n

/-- Rocq v0.17 terminal-cell base `2*n + u + 1`. -/
noncomputable def phiBase (n : ℕ) (u : ℝ) : ℝ :=
  2 * (n : ℝ) + u + 1

/-- Rocq v0.17 real Phi kernel. -/
noncomputable def phiKernelRe (sigma tau x : ℝ) : ℝ :=
  Real.rpow x (-sigma) * Real.cos (tau * Real.log x)

/-- Rocq v0.17 imaginary Phi kernel. -/
noncomputable def phiKernelIm (sigma tau x : ℝ) : ℝ :=
  - (Real.rpow x (-sigma) * Real.sin (tau * Real.log x))

/-- Rocq v0.17 real terminal cell. -/
noncomputable def phiCellRe (n : ℕ) (u sigma tau : ℝ) : ℝ :=
  4 * altSign n * phiKernelRe sigma tau (phiBase n u)

/-- Rocq v0.17 imaginary terminal cell. -/
noncomputable def phiCellIm (n : ℕ) (u sigma tau : ℝ) : ℝ :=
  4 * altSign n * phiKernelIm sigma tau (phiBase n u)

/-- Lean rendering of the Rocq recursive real prefix. -/
noncomputable def phiPrefixRe : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _u, _sigma, _tau => 0
  | Nat.succ n, u, sigma, tau =>
      phiPrefixRe n u sigma tau + phiCellRe n u sigma tau

/-- Lean rendering of the Rocq recursive imaginary prefix. -/
noncomputable def phiPrefixIm : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _u, _sigma, _tau => 0
  | Nat.succ n, u, sigma, tau =>
      phiPrefixIm n u sigma tau + phiCellIm n u sigma tau

/-- Rocq v0.17 finite shifted real residual. -/
noncomputable def finitePhiShiftResidualRe
    (N : ℕ) (u sigma tau : ℝ) : ℝ :=
  phiPrefixRe N u sigma tau + phiPrefixRe N (u + 2) sigma tau -
    4 * phiKernelRe sigma tau (u + 1)

/-- Rocq v0.17 finite shifted imaginary residual. -/
noncomputable def finitePhiShiftResidualIm
    (N : ℕ) (u sigma tau : ℝ) : ℝ :=
  phiPrefixIm N u sigma tau + phiPrefixIm N (u + 2) sigma tau -
    4 * phiKernelIm sigma tau (u + 1)

/-- Rocq v0.19 actual residual real channel: canonical shifted slice `u=1`. -/
noncomputable def actualResidualRe (N : ℕ) (sigma tau : ℝ) : ℝ :=
  finitePhiShiftResidualRe N 1 sigma tau

/-- Rocq v0.19 actual residual imaginary channel: canonical shifted slice `u=1`. -/
noncomputable def actualResidualIm (N : ℕ) (sigma tau : ℝ) : ℝ :=
  finitePhiShiftResidualIm N 1 sigma tau

/-- Rocq v0.19 plus rotation. -/
def rotPlus (c s x y : ℝ) : ℝ := c * x + s * y

/-- Rocq v0.19 minus rotation. -/
def rotMinus (c s x y : ℝ) : ℝ := -s * x + c * y

/-- Rocq v0.22 dyadic cosine coordinate. -/
noncomputable def dyadicRotC (_sigma tau : ℝ) : ℝ :=
  Real.cos (AWPI.PhiRH.RocqPortModel.dyadicPhase tau)

/-- Rocq v0.22 dyadic sine coordinate. -/
noncomputable def dyadicRotS (_sigma tau : ℝ) : ℝ :=
  Real.sin (AWPI.PhiRH.RocqPortModel.dyadicPhase tau)

/-- Canonical plus source induced by the concrete Phi residual and dyadic rotation. -/
noncomputable def canonicalKQPlusSource (N : ℕ) (sigma tau : ℝ) : ℝ :=
  rotPlus (dyadicRotC sigma tau) (dyadicRotS sigma tau)
    (actualResidualRe N sigma tau) (actualResidualIm N sigma tau)

/-- Canonical minus source induced by the concrete Phi residual and dyadic rotation. -/
noncomputable def canonicalKQMinusSource (N : ℕ) (sigma tau : ℝ) : ℝ :=
  rotMinus (dyadicRotC sigma tau) (dyadicRotS sigma tau)
    (actualResidualRe N sigma tau) (actualResidualIm N sigma tau)

/-- Rocq v0.20 plus-coordinate semantic leaf.  The Rocq source leaves the
    actual KQ channel as a variable and requires this equality. -/
def KQPlusCoordinateBinding
    (actualKQPlusSource : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ N sigma tau,
    actualKQPlusSource N sigma tau = canonicalKQPlusSource N sigma tau

/-- Rocq v0.20 minus-coordinate semantic leaf. -/
def KQMinusCoordinateBinding
    (actualKQMinusSource : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ N sigma tau,
    actualKQMinusSource N sigma tau = canonicalKQMinusSource N sigma tau

/-- The two scalar Rocq v0.20 coordinate bindings imply the v0.23 normalized
    complex source formula.  Thus the former source-formula obligation has
    been pushed down to two explicit coordinate equalities. -/
theorem normalizedSourceFormula_of_coordinate_bindings
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (hPlus : KQPlusCoordinateBinding actualKQPlusSource)
    (hMinus : KQMinusCoordinateBinding actualKQMinusSource) :
    AWPI.PhiRH.RocqPortModel.ActualNormalizedDyadicMultiplierSourceFormula
      actualKQPlusSource actualKQMinusSource actualResidualRe actualResidualIm := by
  intro N sigma tau
  change
    (actualKQPlusSource N sigma tau, actualKQMinusSource N sigma tau) =
      AWPI.PhiRH.RocqPortModel.c2Mul (AWPI.PhiRH.RocqPortModel.normalizedDyadicMultiplier sigma tau)
        (actualResidualRe N sigma tau, actualResidualIm N sigma tau)
  rw [hPlus N sigma tau, hMinus N sigma tau]
  apply Prod.ext
  · simp [canonicalKQPlusSource, rotPlus, dyadicRotC, dyadicRotS,
      AWPI.PhiRH.RocqPortModel.c2Mul, AWPI.PhiRH.RocqPortModel.normalizedDyadicMultiplier]
  · simp [canonicalKQMinusSource, rotMinus, dyadicRotC, dyadicRotS,
      AWPI.PhiRH.RocqPortModel.c2Mul, AWPI.PhiRH.RocqPortModel.normalizedDyadicMultiplier]
    ring_nf

/-- v0.1.9 model: the residual channels and the jet-channel formulas are now
    concrete Rocq definitions.  The remaining primitive function inputs are
    the transverse jet, the two jet scales, and the two actual KQ channels. -/
noncomputable def rocqSourceModel
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ) :
    Model ℂ AWPI.PhiRH.RocqPortModel.JetState :=
  AWPI.PhiRH.RocqPortModel.rocqPortModel
    (jetPlus phiTransverseJet plusJetScale)
    (jetMinus phiTransverseJet minusJetScale)
    actualKQPlusSource actualKQMinusSource
    actualResidualRe actualResidualIm

section Audit

variable
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)

local notation "SM" =>
  rocqSourceModel phiTransverseJet plusJetScale minusJetScale
    actualKQPlusSource actualKQMinusSource

@[simp] theorem sourceModel_state (s : ℂ) :
    Model.state SM s =
      (plusJetScale s * phiTransverseJet s,
       minusJetScale s * phiTransverseJet s) := by
  rfl

@[simp] theorem sourceModel_plusTailSource (N : ℕ) (s : ℂ) :
    Model.plusTailSource SM N s = actualKQPlusSource N s.re s.im := by
  rfl

@[simp] theorem sourceModel_minusTailSource (N : ℕ) (s : ℂ) :
    Model.minusTailSource SM N s = actualKQMinusSource N s.re s.im := by
  rfl

@[simp] theorem actualResidualRe_is_u1_shift (N : ℕ) (sigma tau : ℝ) :
    actualResidualRe N sigma tau = finitePhiShiftResidualRe N 1 sigma tau := by
  rfl

@[simp] theorem actualResidualIm_is_u1_shift (N : ℕ) (sigma tau : ℝ) :
    actualResidualIm N sigma tau = finitePhiShiftResidualIm N 1 sigma tau := by
  rfl

/-- The model's normalized-source proposition is discharged from the two
    explicit KQ coordinate leaves. -/
theorem sourceModel_sourceFormula_of_coordinate_bindings
    (hPlus : KQPlusCoordinateBinding actualKQPlusSource)
    (hMinus : KQMinusCoordinateBinding actualKQMinusSource) :
    Model.sourceFormula SM := by
  exact normalizedSourceFormula_of_coordinate_bindings
    actualKQPlusSource actualKQMinusSource hPlus hMinus

/-- The literal RH semantic endpoint remains unchanged after this further
    source-layer disassembly. -/
theorem sourceModel_RH_iff_mathlibRiemannHypothesis :
    Model.RH SM ↔ RiemannHypothesis := by
  exact AWPI.PhiRH.RocqPortModel.rocqPortModel_RH_iff_mathlibRiemannHypothesis
    (jetPlus phiTransverseJet plusJetScale)
    (jetMinus phiTransverseJet minusJetScale)
    actualKQPlusSource actualKQMinusSource actualResidualRe actualResidualIm

end Audit

end AWPI.PhiRH.RocqSourceLayer
