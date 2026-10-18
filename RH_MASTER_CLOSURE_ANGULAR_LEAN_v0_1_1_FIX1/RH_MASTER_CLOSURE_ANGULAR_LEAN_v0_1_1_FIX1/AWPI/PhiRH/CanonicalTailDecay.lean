import AWPI.PhiRH.CanonicalBindingScales
import AWPI.PhiRH.RocqSourceLayer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace AWPI.PhiRH.CanonicalTailDecay

open Filter
open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.CanonicalBindingScales
open AWPI.PhiRH.CanonicalTransverseJet

/-- Squared norm of the concrete finite shifted Phi residual. -/
noncomputable def finitePhiShiftResidualNormSq
    (N : ℕ) (u sigma tau : ℝ) : ℝ :=
  AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualRe N u sigma tau *
      AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualRe N u sigma tau +
    AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualIm N u sigma tau *
      AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualIm N u sigma tau

/-- Squared norm of the terminal Phi cell. -/
noncomputable def phiTerminalNormSq
    (N : ℕ) (u sigma tau : ℝ) : ℝ :=
  AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau * AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau +
    AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau * AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau

@[simp] theorem altSign_succ (n : ℕ) :
    AWPI.PhiRH.RocqSourceLayer.altSign (Nat.succ n) = - AWPI.PhiRH.RocqSourceLayer.altSign n := by
  rfl

@[simp] theorem altSign_mul_self (n : ℕ) :
    AWPI.PhiRH.RocqSourceLayer.altSign n * AWPI.PhiRH.RocqSourceLayer.altSign n = 1 := by
  induction n with
  | zero => simp [AWPI.PhiRH.RocqSourceLayer.altSign]
  | succ n ih => simp [AWPI.PhiRH.RocqSourceLayer.altSign, ih]

@[simp] theorem phiBase_shift (n : ℕ) (u : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiBase n (u + 2) = AWPI.PhiRH.RocqSourceLayer.phiBase (Nat.succ n) u := by
  simp [AWPI.PhiRH.RocqSourceLayer.phiBase]
  ring

@[simp] theorem phiCellRe_shift (n : ℕ) (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiCellRe n (u + 2) sigma tau =
      - AWPI.PhiRH.RocqSourceLayer.phiCellRe (Nat.succ n) u sigma tau := by
  unfold AWPI.PhiRH.RocqSourceLayer.phiCellRe
  rw [phiBase_shift]
  change
    4 * AWPI.PhiRH.RocqSourceLayer.altSign n * AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase (Nat.succ n) u) =
      -(4 * (-AWPI.PhiRH.RocqSourceLayer.altSign n) * AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase (Nat.succ n) u))
  ring

@[simp] theorem phiCellIm_shift (n : ℕ) (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiCellIm n (u + 2) sigma tau =
      - AWPI.PhiRH.RocqSourceLayer.phiCellIm (Nat.succ n) u sigma tau := by
  unfold AWPI.PhiRH.RocqSourceLayer.phiCellIm
  rw [phiBase_shift]
  change
    4 * AWPI.PhiRH.RocqSourceLayer.altSign n * AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase (Nat.succ n) u) =
      -(4 * (-AWPI.PhiRH.RocqSourceLayer.altSign n) * AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase (Nat.succ n) u))
  ring

/-- Rocq PHIRH144. -/
theorem phiPrefixRe_shift_telescopes
    (N : ℕ) (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiPrefixRe N u sigma tau + AWPI.PhiRH.RocqSourceLayer.phiPrefixRe N (u + 2) sigma tau =
      AWPI.PhiRH.RocqSourceLayer.phiCellRe 0 u sigma tau - AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau := by
  induction N with
  | zero => simp [AWPI.PhiRH.RocqSourceLayer.phiPrefixRe]
  | succ N ih =>
      simp only [AWPI.PhiRH.RocqSourceLayer.phiPrefixRe]
      calc
        AWPI.PhiRH.RocqSourceLayer.phiPrefixRe N u sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau +
            (AWPI.PhiRH.RocqSourceLayer.phiPrefixRe N (u + 2) sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiCellRe N (u + 2) sigma tau) =
            (AWPI.PhiRH.RocqSourceLayer.phiPrefixRe N u sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiPrefixRe N (u + 2) sigma tau) +
            (AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiCellRe N (u + 2) sigma tau) := by ring
        _ = (AWPI.PhiRH.RocqSourceLayer.phiCellRe 0 u sigma tau -
              AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau) +
            (AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau -
              AWPI.PhiRH.RocqSourceLayer.phiCellRe (Nat.succ N) u sigma tau) := by
              rw [ih, phiCellRe_shift]
              simp only [sub_eq_add_neg]
        _ = AWPI.PhiRH.RocqSourceLayer.phiCellRe 0 u sigma tau -
              AWPI.PhiRH.RocqSourceLayer.phiCellRe (Nat.succ N) u sigma tau := by ring

/-- Rocq PHIRH145. -/
theorem phiPrefixIm_shift_telescopes
    (N : ℕ) (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiPrefixIm N u sigma tau + AWPI.PhiRH.RocqSourceLayer.phiPrefixIm N (u + 2) sigma tau =
      AWPI.PhiRH.RocqSourceLayer.phiCellIm 0 u sigma tau - AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau := by
  induction N with
  | zero => simp [AWPI.PhiRH.RocqSourceLayer.phiPrefixIm]
  | succ N ih =>
      simp only [AWPI.PhiRH.RocqSourceLayer.phiPrefixIm]
      calc
        AWPI.PhiRH.RocqSourceLayer.phiPrefixIm N u sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau +
            (AWPI.PhiRH.RocqSourceLayer.phiPrefixIm N (u + 2) sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiCellIm N (u + 2) sigma tau) =
            (AWPI.PhiRH.RocqSourceLayer.phiPrefixIm N u sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiPrefixIm N (u + 2) sigma tau) +
            (AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau +
              AWPI.PhiRH.RocqSourceLayer.phiCellIm N (u + 2) sigma tau) := by ring
        _ = (AWPI.PhiRH.RocqSourceLayer.phiCellIm 0 u sigma tau -
              AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau) +
            (AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau -
              AWPI.PhiRH.RocqSourceLayer.phiCellIm (Nat.succ N) u sigma tau) := by
              rw [ih, phiCellIm_shift]
              simp only [sub_eq_add_neg]
        _ = AWPI.PhiRH.RocqSourceLayer.phiCellIm 0 u sigma tau -
              AWPI.PhiRH.RocqSourceLayer.phiCellIm (Nat.succ N) u sigma tau := by ring

@[simp] theorem phiCellRe_zero (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiCellRe 0 u sigma tau = 4 * AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau (u + 1) := by
  simp [AWPI.PhiRH.RocqSourceLayer.phiCellRe, AWPI.PhiRH.RocqSourceLayer.phiBase, AWPI.PhiRH.RocqSourceLayer.altSign]

@[simp] theorem phiCellIm_zero (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiCellIm 0 u sigma tau = 4 * AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau (u + 1) := by
  simp [AWPI.PhiRH.RocqSourceLayer.phiCellIm, AWPI.PhiRH.RocqSourceLayer.phiBase, AWPI.PhiRH.RocqSourceLayer.altSign]

/-- Rocq PHIRH150. -/
theorem finiteResidualRe_eq_neg_terminal
    (N : ℕ) (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualRe N u sigma tau =
      - AWPI.PhiRH.RocqSourceLayer.phiCellRe N u sigma tau := by
  unfold AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualRe
  rw [phiPrefixRe_shift_telescopes, phiCellRe_zero]
  ring

/-- Rocq PHIRH151. -/
theorem finiteResidualIm_eq_neg_terminal
    (N : ℕ) (u sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualIm N u sigma tau =
      - AWPI.PhiRH.RocqSourceLayer.phiCellIm N u sigma tau := by
  unfold AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualIm
  rw [phiPrefixIm_shift_telescopes, phiCellIm_zero]
  ring

/-- Rocq PHIRH161. -/
theorem phiKernel_norm_sq
    (sigma tau x : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau x * AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau x +
        AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau x * AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau x =
      Real.rpow x (-sigma) * Real.rpow x (-sigma) := by
  unfold AWPI.PhiRH.RocqSourceLayer.phiKernelRe AWPI.PhiRH.RocqSourceLayer.phiKernelIm
  calc
    Real.rpow x (-sigma) * Real.cos (tau * Real.log x) *
          (Real.rpow x (-sigma) * Real.cos (tau * Real.log x)) +
        (-(Real.rpow x (-sigma) * Real.sin (tau * Real.log x))) *
          (-(Real.rpow x (-sigma) * Real.sin (tau * Real.log x))) =
        (Real.rpow x (-sigma) * Real.rpow x (-sigma)) *
          (Real.cos (tau * Real.log x) ^ 2 + Real.sin (tau * Real.log x) ^ 2) := by
            ring
    _ = Real.rpow x (-sigma) * Real.rpow x (-sigma) := by
      rw [Real.cos_sq_add_sin_sq]
      ring

/-- Rocq PHIRH162. -/
theorem phiTerminalNormSq_exact
    (N : ℕ) (u sigma tau : ℝ) :
    phiTerminalNormSq N u sigma tau =
      16 * (Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma) *
        Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma)) := by
  unfold phiTerminalNormSq AWPI.PhiRH.RocqSourceLayer.phiCellRe AWPI.PhiRH.RocqSourceLayer.phiCellIm
  calc
    (4 * AWPI.PhiRH.RocqSourceLayer.altSign N * AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u)) *
          (4 * AWPI.PhiRH.RocqSourceLayer.altSign N * AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u)) +
        (4 * AWPI.PhiRH.RocqSourceLayer.altSign N * AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u)) *
          (4 * AWPI.PhiRH.RocqSourceLayer.altSign N * AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u)) =
        16 * (AWPI.PhiRH.RocqSourceLayer.altSign N * AWPI.PhiRH.RocqSourceLayer.altSign N) *
          (AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u) *
              AWPI.PhiRH.RocqSourceLayer.phiKernelRe sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u) +
            AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u) *
              AWPI.PhiRH.RocqSourceLayer.phiKernelIm sigma tau (AWPI.PhiRH.RocqSourceLayer.phiBase N u)) := by ring
    _ = 16 * (Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma) *
        Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma)) := by
      rw [altSign_mul_self, phiKernel_norm_sq]
      ring

/-- Rocq PHIRH164. -/
theorem finiteResidualNormSq_eq_terminalNormSq
    (N : ℕ) (u sigma tau : ℝ) :
    finitePhiShiftResidualNormSq N u sigma tau =
      phiTerminalNormSq N u sigma tau := by
  unfold finitePhiShiftResidualNormSq phiTerminalNormSq
  rw [finiteResidualRe_eq_neg_terminal, finiteResidualIm_eq_neg_terminal]
  ring

lemma phiBase_pos (N : ℕ) (u : ℝ) (hu : 0 < u + 1) :
    0 < AWPI.PhiRH.RocqSourceLayer.phiBase N u := by
  unfold AWPI.PhiRH.RocqSourceLayer.phiBase
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

lemma phiBase_tendsto_atTop (u : ℝ) :
    Tendsto (fun N : ℕ => AWPI.PhiRH.RocqSourceLayer.phiBase N u) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - u - 1) / 2)
  refine ⟨N, ?_⟩
  intro n hNn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hbN : b < 2 * (N : ℝ) + u + 1 := by nlinarith
  unfold AWPI.PhiRH.RocqSourceLayer.phiBase
  linarith

/-- Rocq PHIRH168, via Mathlib's `tendsto_rpow_neg_atTop`. -/
theorem phiTerminalNormSq_decay
    (u sigma tau : ℝ) (hu : 0 < u + 1) (hsigma : 0 < sigma) :
    ∀ eps : ℝ, 0 < eps →
      ∃ N : ℕ, phiTerminalNormSq N u sigma tau ≤ eps := by
  have hrpow :
      Tendsto (fun N : ℕ => Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hsigma).comp (phiBase_tendsto_atTop u)
  have hprod :
      Tendsto
        (fun N : ℕ =>
          Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma) *
            Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma))
        atTop (nhds 0) := by
    simpa using hrpow.mul hrpow
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          16 * (Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma) *
            Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma)))
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hprod :
      Tendsto
        (fun N : ℕ =>
          (16 : ℝ) *
            (Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma) *
              Real.rpow (AWPI.PhiRH.RocqSourceLayer.phiBase N u) (-sigma)))
        atTop (nhds (16 * 0)))
  have hterm :
      Tendsto (fun N : ℕ => phiTerminalNormSq N u sigma tau)
        atTop (nhds 0) := by
    simpa only [phiTerminalNormSq_exact] using hscaled
  intro eps heps
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hterm) eps heps
  refine ⟨N, ?_⟩
  have h := hN N le_rfl
  have hnonneg : 0 ≤ phiTerminalNormSq N u sigma tau := by
    unfold phiTerminalNormSq
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hlt : phiTerminalNormSq N u sigma tau < eps := by
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using h
  exact le_of_lt hlt

/-- Rocq PHIRH171: canonical `u=1` shifted Phi residual decays. -/
theorem canonicalResidualNormSq_decay
    (sigma tau eps : ℝ) (hsigma : 0 < sigma) (heps : 0 < eps) :
    ∃ N : ℕ, finitePhiShiftResidualNormSq N 1 sigma tau ≤ eps := by
  obtain ⟨N, hN⟩ := phiTerminalNormSq_decay 1 sigma tau (by norm_num) hsigma eps heps
  refine ⟨N, ?_⟩
  rw [finiteResidualNormSq_eq_terminalNormSq]
  exact hN

/-- The concrete dyadic rotation preserves squared Euclidean norm. -/
theorem canonicalKQ_tail_sum_eq_residualNormSq
    (N : ℕ) (sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau * AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau +
        AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau * AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau =
      finitePhiShiftResidualNormSq N 1 sigma tau := by
  unfold AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource
    AWPI.PhiRH.RocqSourceLayer.rotPlus AWPI.PhiRH.RocqSourceLayer.rotMinus AWPI.PhiRH.RocqSourceLayer.dyadicRotC AWPI.PhiRH.RocqSourceLayer.dyadicRotS
  unfold AWPI.PhiRH.RocqSourceLayer.actualResidualRe AWPI.PhiRH.RocqSourceLayer.actualResidualIm
  unfold finitePhiShiftResidualNormSq
  let c := Real.cos (dyadicPhase tau)
  let s := Real.sin (dyadicPhase tau)
  let x := AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualRe N 1 sigma tau
  let y := AWPI.PhiRH.RocqSourceLayer.finitePhiShiftResidualIm N 1 sigma tau
  change (c * x + s * y) * (c * x + s * y) +
      (-s * x + c * y) * (-s * x + c * y) = x * x + y * y
  have hunit : c * c + s * s = 1 := by
    dsimp [c, s]
    simpa [pow_two] using Real.cos_sq_add_sin_sq (dyadicPhase tau)
  calc
    (c * x + s * y) * (c * x + s * y) +
        (-s * x + c * y) * (-s * x + c * y) =
      (c * c + s * s) * (x * x + y * y) := by ring
    _ = x * x + y * y := by rw [hunit]; ring

theorem canonicalKQPlusTail_le_residualNormSq
    (N : ℕ) (sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau * AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau ≤
      finitePhiShiftResidualNormSq N 1 sigma tau := by
  have hsum := canonicalKQ_tail_sum_eq_residualNormSq N sigma tau
  have hm : 0 ≤ AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau *
      AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau := mul_self_nonneg _
  nlinarith

theorem canonicalKQMinusTail_le_residualNormSq
    (N : ℕ) (sigma tau : ℝ) :
    AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau * AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau ≤
      finitePhiShiftResidualNormSq N 1 sigma tau := by
  have hsum := canonicalKQ_tail_sum_eq_residualNormSq N sigma tau
  have hp : 0 ≤ AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau *
      AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau := mul_self_nonneg _
  nlinarith

/-- Concrete PHIRH233 for the canonical KQ source channels. -/
theorem canonicalKQ_jointTailDecay
    (sigma tau eps : ℝ) (hsigma : 0 < sigma) (heps : 0 < eps) :
    ∃ N : ℕ,
      AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau * AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource N sigma tau ≤ eps ∧
      AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau * AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource N sigma tau ≤ eps := by
  obtain ⟨N, hres⟩ := canonicalResidualNormSq_decay sigma tau eps hsigma heps
  refine ⟨N, ?_, ?_⟩
  · exact (canonicalKQPlusTail_le_residualNormSq N sigma tau).trans hres
  · exact (canonicalKQMinusTail_le_residualNormSq N sigma tau).trans hres

/-- Native RH now depends only on the two exact-to-tail upper bounds. -/
theorem MATHLIB_RH_OF_TWO_EXACT_TAIL_FRONTIER_LEAVES
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (plusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) *
              (ActivityFrontier.boundJetPlus canonicalPlusJetScale canonicalTransverseJet rho) ^ 2 -
            (ActivityFrontier.boundJetPlus canonicalPlusJetScale canonicalTransverseJet rho) ^ 2 ≤
          -(finitePlusSquare n rho) ^ 2 +
            AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource n rho.re rho.im *
              AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource n rho.re rho.im)
    (minusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) *
              (ActivityFrontier.boundJetMinus canonicalMinusJetScale canonicalTransverseJet rho) ^ 2 -
            (ActivityFrontier.boundJetMinus canonicalMinusJetScale canonicalTransverseJet rho) ^ 2 ≤
          -(finiteMinusSquare n rho) ^ 2 +
            AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource n rho.re rho.im *
              AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource n rho.re rho.im) :
    RiemannHypothesis := by
  apply CanonicalBindingScales.MATHLIB_RH_OF_THREE_CANONICAL_SCALE_FRONTIER_LEAVES
    AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource AWPI.PhiRH.RocqSourceLayer.canonicalKQMinusSource
    finitePlusSquare finiteMinusSquare
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · intro rho eps hz heps
    exact canonicalKQ_jointTailDecay rho.re rho.im eps
      (NativeZetaSupport.nontrivialZetaZero_re_pos rho hz) heps

end AWPI.PhiRH.CanonicalTailDecay
