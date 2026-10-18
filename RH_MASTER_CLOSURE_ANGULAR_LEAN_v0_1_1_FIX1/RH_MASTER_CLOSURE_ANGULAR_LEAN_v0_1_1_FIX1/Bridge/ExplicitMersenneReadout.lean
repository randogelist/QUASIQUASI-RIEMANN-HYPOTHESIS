import Bridge.MersenneCentralCriterion
import Mathlib

namespace NativeSoloboloNegativity

open Filter
open scoped Topology BigOperators

noncomputable section

/-- A single finite Cayley-defect spectral system, shared across all Mersenne depths.
The finite readout at depth `k` is not a free scalar: it is the trace power of these
explicit nonnegative contraction eigenvalues. -/
structure FiniteCayleyDefectSystem where
  dim : ℕ → ℕ
  eigenvalue : (M : ℕ) → ℝ → Fin (dim M) → ℝ
  nonnegative : ∀ (M : ℕ) (a : ℝ) (i : Fin (dim M)), 0 ≤ eigenvalue M a i
  contractive : ∀ (M : ℕ) (a : ℝ) (i : Fin (dim M)), eigenvalue M a i ≤ 1

/-- The finite `2^k` trace-power readout of the Cayley-defect system. -/
def cayleyTracePower
    (S : FiniteCayleyDefectSystem) (k M : ℕ) (a : ℝ) : ℝ :=
  ∑ i : Fin (S.dim M), (S.eigenvalue M a i) ^ (2^k)

/-- !!! Every finite Cayley trace-power readout is nonnegative by construction. -/
theorem CAYLEY_TRACE_POWER_NONNEG
    (S : FiniteCayleyDefectSystem) (k M : ℕ) (a : ℝ) :
    0 ≤ cayleyTracePower S k M a := by
  unfold cayleyTracePower
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (S.nonnegative M a i) _)

/-- Honest finite central-cell frontier: one depth-independent finite Cayley spectrum
whose `2^k` trace powers converge, on a cofinal Mersenne subsequence, to the actual
near-central Hausdorff/Widder cells. No sign of the target cell is a field. -/
def CofinalMersenneCentralCayleyTraceConvergence
    (S : FiniteCayleyDefectSystem) : Prop :=
  ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
    ∀ a : ℝ, 0 < a →
      Tendsto (fun M : ℕ => cayleyTracePower S k M a) atTop
        (𝓝 (centralWidderMoment xiR (mersenneDepth k) a))

/-- Structural nonnegativity of the finite trace powers passes to the central-cell
limit; the target sign itself is never assumed. -/
theorem MERSENNE_CAYLEY_TRACE_CONVERGENCE_GIVES_CENTRAL_POSITIVITY
    (S : FiniteCayleyDefectSystem)
    (hconv : CofinalMersenneCentralCayleyTraceConvergence S) :
    CofinalMersenneCentralPositive := by
  intro K
  rcases hconv K with ⟨k, hk, hka⟩
  refine ⟨k, hk, ?_⟩
  intro a ha
  exact ge_of_tendsto' (hka a ha)
    (fun M => CAYLEY_TRACE_POWER_NONNEG S k M a)

/-- !!! Explicit finite Cayley-defect trace powers on cofinally many Mersenne cells,
plus the separately printed analytic bindings, imply native Mathlib RH. -/
theorem MERSENNE_CAYLEY_TRACE_AND_CHANNEL_ANALYSIS_IMPLY_RH
    (S : FiniteCayleyDefectSystem)
    (hchannel : ActualOffLineChannelAnalysis)
    (hreg : AllPositiveXiRegular)
    (hconv : CofinalMersenneCentralCayleyTraceConvergence S) :
    _root_.RiemannHypothesis :=
  MERSENNE_CENTRAL_POSITIVITY_AND_CHANNEL_ANALYSIS_IMPLY_RH
    hchannel hreg
      (MERSENNE_CAYLEY_TRACE_CONVERGENCE_GIVES_CENTRAL_POSITIVITY S hconv)

/-- Direct actual-xi version of the finite frontier. This avoids the regular-anchor
transport completely: the independently defined finite trace powers converge directly
to the recursive actual xi Widder moments. -/
def CofinalMersenneXiCayleyTraceConvergence
    (S : FiniteCayleyDefectSystem) : Prop :=
  ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
    ∀ a : ℝ, 0 < a →
      Tendsto (fun M : ℕ => cayleyTracePower S k M a) atTop
        (𝓝 (xiWidderMoment a (mersenneDepth k)))

/-- !!! Direct finite Cayley-trace convergence already produces the existing
cofinal uniform-depth positivity, with no positive-axis regularity hypothesis. -/
theorem MERSENNE_XI_CAYLEY_TRACE_CONVERGENCE_GIVES_COFINAL_WIDDER
    (S : FiniteCayleyDefectSystem)
    (hconv : CofinalMersenneXiCayleyTraceConvergence S) :
    CofinalUniformDepthPositive := by
  intro K
  rcases hconv (K + 1) with ⟨k, hk, hka⟩
  have hkpos : 0 < k := by omega
  have hkpow : k < 2^k := (Nat.lt_two_pow_self : k < 2^k)
  have hKpow : K < 2^k := lt_of_lt_of_le (by omega) (Nat.le_of_lt hkpow)
  have hdepth : K ≤ mersenneDepth k := by
    unfold mersenneDepth
    omega
  refine ⟨mersenneDepth k, hdepth, ?_⟩
  intro a ha
  exact ge_of_tendsto' (hka a ha)
    (fun M => CAYLEY_TRACE_POWER_NONNEG S k M a)

/-- !!! Strong hreg-free finite-readout criterion: actual-xi Mersenne trace convergence
and actual off-line channel analysis imply RH. -/
theorem MERSENNE_XI_CAYLEY_TRACE_AND_CHANNEL_ANALYSIS_IMPLY_RH
    (S : FiniteCayleyDefectSystem)
    (hchannel : ActualOffLineChannelAnalysis)
    (hconv : CofinalMersenneXiCayleyTraceConvergence S) :
    _root_.RiemannHypothesis :=
  COFINAL_POSITIVITY_AND_CHANNEL_ANALYSIS_IMPLY_RH hchannel
    (MERSENNE_XI_CAYLEY_TRACE_CONVERGENCE_GIVES_COFINAL_WIDDER S hconv)

/-- The central-cell frontier canonically transports to the direct actual-xi frontier
once positive anchors are known to lie in the regular domain. -/
theorem CENTRAL_CAYLEY_TRACE_CONVERGENCE_GIVES_XI_CONVERGENCE
    (S : FiniteCayleyDefectSystem)
    (hreg : AllPositiveXiRegular)
    (hconv : CofinalMersenneCentralCayleyTraceConvergence S) :
    CofinalMersenneXiCayleyTraceConvergence S := by
  intro K
  rcases hconv K with ⟨k, hk, hka⟩
  refine ⟨k, hk, ?_⟩
  intro a ha
  have hregular := hreg a ha
  have heq := XI_RECURSIVE_EQ_CENTRAL_HAUSDORFF_ON_REGULAR_ANCHORS
    a hregular (mersenneDepth k)
  simpa only [heq] using hka a ha

end
end NativeSoloboloNegativity
