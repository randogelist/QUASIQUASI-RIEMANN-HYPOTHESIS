import AngularMaster.QQRHUnconditional
import RiemannHypothesis.Xi.RiemannHypothesisBridge
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Concrete multiplicity-bearing critical-line cutoffs and a native RH closure.
The trace identity is an explicit input to the helper below; the public
small-o theorem must instantiate it with its separately proved actual identity.
-/

noncomputable section
open Filter Set
open scoped Classical Topology BigOperators

namespace RHSmallO

open AngularMaster OverflowResidueRH

/-- One exact opposite-pair occurrence of the actual xi divisor. -/
abbrev SpectralIndex := ActualPairIndex

/-- The real reciprocal squared-zero contribution. -/
def spectralWeight (i : SpectralIndex) : ℝ :=
  ((actualComplexScale i)⁻¹).re

theorem spectralWeight_pos (i : SpectralIndex) : 0 < spectralWeight i := by
  have hn : 0 < ‖actualComplexScale i‖ :=
    norm_pos_iff.mpr (actualComplexScale_ne_zero i)
  have hs := actualComplexScale_sector_two i
  have hs' := (div_le_iff₀ hn).mp hs
  have hre : 0 < (actualComplexScale i).re := by nlinarith
  unfold spectralWeight
  rw [Complex.inv_re]
  exact div_pos hre (Complex.normSq_pos.mpr (actualComplexScale_ne_zero i))

theorem spectralWeight_summable : Summable spectralWeight := by
  refine Summable.of_nonneg_of_le (fun i => (spectralWeight_pos i).le) ?_
    actualComplexScale_norm_inv_summable
  intro i
  exact (Complex.abs_re_le_norm ((actualComplexScale i)⁻¹)).trans'
    (le_abs_self _)

/-- A critical-line occurrence has exactly the classical inverse-height-square
weight. Each opposite pair is counted once by `SpectralIndex`. -/
theorem spectralWeight_eq_inverse_height_sq
    (i : SpectralIndex) (him : (actualPairZero i).im = 0) :
    spectralWeight i = 1 / ‖actualPairZero i‖ ^ 2 := by
  have hre : (actualComplexScale i).re = ‖actualPairZero i‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [actualComplexScale, pow_two, Complex.mul_re, Complex.normSq_apply, him]
  have hnorm : Complex.normSq (actualComplexScale i) =
      (‖actualPairZero i‖ ^ 2) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_actualComplexScale, actualZeroScale]
  have hn : ‖actualPairZero i‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (actualPairZero_ne_zero i))
  unfold spectralWeight
  rw [Complex.inv_re, hre, hnorm]
  field_simp [hn]

/-- The actual finite height cutoff; the occurrence index retains multiplicity.
For real representatives the norm is the positive critical-line ordinate. -/
def criticalLineCutoffTerm (r : ℝ) (i : SpectralIndex) : ℝ := by
  classical
  exact if (actualPairZero i).im = 0 ∧ ‖actualPairZero i‖ ≤ 1 / r
    then spectralWeight i else 0

def criticalLineCutoff (r : ℝ) : ℝ :=
  ∑' i : SpectralIndex, criticalLineCutoffTerm r i

/-- Each cutoff is a finite sum, despite its convenient `tsum` notation. -/
theorem criticalLineCutoff_finite_support (r : ℝ) :
    (Function.support (criticalLineCutoffTerm r)).Finite := by
  classical
  have hfinite :
      {i : SpectralIndex | ‖actualPairZero i‖ ≤ 1 / r}.Finite :=
    (entireXiPullbackZeroOccurrenceNegationPairingData.repLoc_normProper
      entireXiPullbackZeroOccurrenceNormProper).finite_norm_le (1 / r)
  apply hfinite.subset
  intro i hi
  change criticalLineCutoffTerm r i ≠ 0 at hi
  by_cases hcond : (actualPairZero i).im = 0 ∧ ‖actualPairZero i‖ ≤ 1 / r
  · exact hcond.2
  · have hzero : criticalLineCutoffTerm r i = 0 := by
      unfold criticalLineCutoffTerm
      exact if_neg hcond
    exact (hi hzero).elim

theorem criticalLineCutoffTerm_nonneg (r : ℝ) (i : SpectralIndex) :
    0 ≤ criticalLineCutoffTerm r i := by
  classical
  unfold criticalLineCutoffTerm
  split_ifs
  · exact (spectralWeight_pos i).le
  · exact le_rfl

theorem criticalLineCutoffTerm_le (r : ℝ) (i : SpectralIndex) :
    criticalLineCutoffTerm r i ≤ spectralWeight i := by
  classical
  unfold criticalLineCutoffTerm
  split_ifs
  · exact le_rfl
  · exact (spectralWeight_pos i).le

theorem criticalLineCutoffTerm_summable (r : ℝ) :
    Summable (criticalLineCutoffTerm r) :=
  Summable.of_nonneg_of_le (criticalLineCutoffTerm_nonneg r)
    (criticalLineCutoffTerm_le r) spectralWeight_summable

/-- Literal inverse-square height presentation of the same cutoff. -/
theorem criticalLineCutoff_eq_inverse_height_sum (r : ℝ) :
    criticalLineCutoff r =
      ∑' i : SpectralIndex,
        if (actualPairZero i).im = 0 ∧ ‖actualPairZero i‖ ≤ 1 / r
        then 1 / ‖actualPairZero i‖ ^ 2 else 0 := by
  classical
  apply tsum_congr
  intro i
  unfold criticalLineCutoffTerm
  split_ifs with hi
  · exact spectralWeight_eq_inverse_height_sq i hi.1
  · rfl

/-- Any individual off-line contribution is bounded by the omitted mass,
at every cutoff. No passage to a critical-line cutoff limit is necessary. -/
theorem offLineWeight_le_trace_sub_cutoff
    (q1 : ℝ) (htrace : q1 = ∑' i : SpectralIndex, spectralWeight i)
    (r : ℝ) (i0 : SpectralIndex) (hoff : (actualPairZero i0).im ≠ 0) :
    spectralWeight i0 ≤ q1 - criticalLineCutoff r := by
  classical
  let residual : SpectralIndex → ℝ :=
    fun i => spectralWeight i - criticalLineCutoffTerm r i
  have hnonneg : ∀ i, 0 ≤ residual i := by
    intro i
    exact sub_nonneg.mpr (criticalLineCutoffTerm_le r i)
  have hsum : Summable residual :=
    spectralWeight_summable.sub (criticalLineCutoffTerm_summable r)
  have hsingle := hsum.sum_le_tsum ({i0} : Finset SpectralIndex)
    (fun i _ => hnonneg i)
  simp only [Finset.sum_singleton] at hsingle
  calc
    spectralWeight i0 = residual i0 := by
      simp [residual, criticalLineCutoffTerm, hoff]
    _ ≤ ∑' i : SpectralIndex, residual i := hsingle
    _ = q1 - criticalLineCutoff r := by
      change (∑' i : SpectralIndex,
        (spectralWeight i - criticalLineCutoffTerm r i)) = q1 - criticalLineCutoff r
      rw [spectralWeight_summable.tsum_sub (criticalLineCutoffTerm_summable r)]
      rw [← htrace]
      rfl

/-- Real opposite-pair representatives imply the literal Mathlib RH. -/
theorem native_RH_of_all_representatives_real
    (hreal : ∀ i : SpectralIndex, (actualPairZero i).im = 0) :
    _root_.RiemannHypothesis := by
  classical
  apply riemannHypothesis_iff_entireXiPullback_zeros_real.mpr
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  obtain ⟨i, hi⟩ := entireXiPullbackZeroOccurrenceLoc_exhaustive hz hz0
  let P := entireXiPullbackZeroOccurrenceNegationPairingData
  obtain ⟨⟨j, b⟩, hpair⟩ := P.pairEquiv.surjective i
  cases b with
  | false =>
      have heq : actualPairZero j = z := by
        change entireXiPullbackZeroOccurrenceLoc (P.pairEquiv (j, false)) = z
        rw [hpair, hi]
      simpa [heq] using hreal j
  | true =>
      have heq : -actualPairZero j = z := by
        change -entireXiPullbackZeroOccurrenceLoc (P.pairEquiv (j, false)) = z
        rw [← P.loc_true j, hpair, hi]
      have him : (-actualPairZero j).im = 0 := by simp [hreal j]
      rwa [heq] at him

/-- A vanishing omitted spectral response forces all actual divisor
representatives onto the critical line, hence native Mathlib RH. -/
theorem scalar_response_limit_implies_RH
    (q1 : ℝ) (htrace : q1 = ∑' i : SpectralIndex, spectralWeight i)
    (hlim : Tendsto (fun r : ℝ => q1 - criticalLineCutoff r)
      (𝓝[>] 0) (𝓝 0)) :
    _root_.RiemannHypothesis := by
  classical
  apply native_RH_of_all_representatives_real
  intro i
  by_contra hoff
  have hle : spectralWeight i ≤ (0 : ℝ) :=
    ge_of_tendsto' hlim (fun r => offLineWeight_le_trace_sub_cutoff q1 htrace r i hoff)
  exact (not_le_of_gt (spectralWeight_pos i)) hle

end RHSmallO
