/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import RiemannHypothesis.HadamardProduct.LogDerivative

/-!
# Sign of genus-one zero sums over an arbitrary index type

This module generalizes the finite-sum and regularized-series sign layer from
natural-number-indexed zero sequences to an arbitrary index type.  Strictness
requires only that the index type be nonempty: one fixed residue is retained
as a uniform strictly negative upper bound while the finite sums converge over
the `Finset`-directed filter.
-/

namespace OverflowResidueRH

open Filter Topology

/-- A finite regularized sum over real zero locations has nonpositive
imaginary part in the open upper half-plane. -/
theorem finiteHadamardRegularizedSum_real_im_nonpos_indexed
    {ι : Type*} (zeroLoc : ι → ℝ) (F : Finset ι)
    {s : ℂ} (hs : 0 < s.im) :
    (finiteHadamardRegularizedSum
      (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) F s).im ≤ 0 := by
  classical
  unfold finiteHadamardRegularizedSum
  rw [Complex.im_sum]
  apply Finset.sum_nonpos
  intro i _hi
  rw [Complex.add_im]
  have hregularizer : (1 / (((zeroLoc i : ℝ) : ℂ))).im = 0 := by
    simp
  rw [hregularizer, add_zero]
  exact complex_real_root_residue_imag_nonpos s (zeroLoc i) hs

/-- A finite regularized sum containing `i` is bounded above by the strictly
negative imaginary contribution of that residue. -/
theorem finiteHadamardRegularizedSum_real_im_le_residue_indexed
    {ι : Type*} (zeroLoc : ι → ℝ) (F : Finset ι)
    {i : ι} (hi : i ∈ F) {s : ℂ} (hs : 0 < s.im) :
    (finiteHadamardRegularizedSum
      (fun j : ι => ((zeroLoc j : ℝ) : ℂ)) F s).im ≤
        ((1 : ℂ) / (s - ((zeroLoc i : ℝ) : ℂ))).im := by
  classical
  have hsplit :
      finiteHadamardRegularizedSum
          (fun j : ι => ((zeroLoc j : ℝ) : ℂ)) F s =
        finiteHadamardRegularizedSum
            (fun j : ι => ((zeroLoc j : ℝ) : ℂ)) (F.erase i) s +
          (1 / (s - ((zeroLoc i : ℝ) : ℂ)) +
            1 / ((zeroLoc i : ℝ) : ℂ)) := by
    unfold finiteHadamardRegularizedSum
    exact (F.sum_erase_add _ hi).symm
  have hrest := finiteHadamardRegularizedSum_real_im_nonpos_indexed
    zeroLoc (F.erase i) hs
  have hregularizer : (1 / ((zeroLoc i : ℝ) : ℂ)).im = 0 := by
    simp
  rw [hsplit, Complex.add_im, Complex.add_im, hregularizer, add_zero]
  linarith

/-- The regularized genus-one series over arbitrary real zero locations has
nonpositive imaginary part in the open upper half-plane. -/
theorem hadamardRegularizedLogDerivSeries_real_im_nonpos_indexed
    {ι : Type*} (zeroLoc : ι → ℝ)
    (H : HadamardZeroInvSqSummability
      (fun i : ι => ((zeroLoc i : ℝ) : ℂ)))
    {s : ℂ} (hs : 0 < s.im) :
    (hadamardRegularizedLogDerivSeries
      (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) s).im ≤ 0 := by
  have hsum_tendsto := H.finiteRegularizedSum_tendsto_totalized s
  have him_tendsto :
      Tendsto
        (fun F : Finset ι =>
          (finiteHadamardRegularizedSum
            (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) F s).im)
        Filter.atTop
        (𝓝 (hadamardRegularizedLogDerivSeries
          (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) s).im) :=
    (Complex.continuous_im.tendsto _).comp hsum_tendsto
  exact le_of_tendsto him_tendsto
    (Filter.Eventually.of_forall fun F =>
      finiteHadamardRegularizedSum_real_im_nonpos_indexed zeroLoc F hs)

/-- If the arbitrary index type is nonempty, its regularized genus-one series
has strictly negative imaginary part in the open upper half-plane. -/
theorem hadamardRegularizedLogDerivSeries_real_im_neg_indexed
    {ι : Type*} [Nonempty ι] (zeroLoc : ι → ℝ)
    (H : HadamardZeroInvSqSummability
      (fun i : ι => ((zeroLoc i : ℝ) : ℂ)))
    {s : ℂ} (hs : 0 < s.im) :
    (hadamardRegularizedLogDerivSeries
      (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) s).im < 0 := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  have hsum_tendsto := H.finiteRegularizedSum_tendsto_totalized s
  have him_tendsto :
      Tendsto
        (fun F : Finset ι =>
          (finiteHadamardRegularizedSum
            (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) F s).im)
        Filter.atTop
        (𝓝 (hadamardRegularizedLogDerivSeries
          (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) s).im) :=
    (Complex.continuous_im.tendsto _).comp hsum_tendsto
  have hbound :
      ∀ᶠ F : Finset ι in Filter.atTop,
        (finiteHadamardRegularizedSum
          (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) F s).im ≤
            ((1 : ℂ) / (s - ((zeroLoc i₀ : ℝ) : ℂ))).im := by
    filter_upwards [Filter.eventually_ge_atTop ({i₀} : Finset ι)] with F hF
    exact finiteHadamardRegularizedSum_real_im_le_residue_indexed
      zeroLoc F (hF (by simp)) hs
  have hlimit_le :
      (hadamardRegularizedLogDerivSeries
        (fun i : ι => ((zeroLoc i : ℝ) : ℂ)) s).im ≤
          ((1 : ℂ) / (s - ((zeroLoc i₀ : ℝ) : ℂ))).im :=
    le_of_tendsto him_tendsto hbound
  exact lt_of_le_of_lt hlimit_le
    (complex_real_root_residue_imag_neg s (zeroLoc i₀) hs)

/-- Complex-valued finite-sum wrapper: if every indexed location has zero
imaginary part, the finite regularized sum has nonpositive imaginary part. -/
theorem finiteHadamardRegularizedSum_im_nonpos_of_real_indexed
    {ι : Type*} (zeroLoc : ι → ℂ)
    (hreal : ∀ i : ι, (zeroLoc i).im = 0)
    (F : Finset ι) {s : ℂ} (hs : 0 < s.im) :
    (finiteHadamardRegularizedSum zeroLoc F s).im ≤ 0 := by
  let realLoc : ι → ℝ := fun i => (zeroLoc i).re
  have hloc : (fun i : ι => ((realLoc i : ℝ) : ℂ)) = zeroLoc := by
    funext i
    apply Complex.ext
    · rfl
    · simpa [realLoc] using (hreal i).symm
  simpa only [hloc] using
    finiteHadamardRegularizedSum_real_im_nonpos_indexed realLoc F hs

/-- Complex-valued series wrapper for nonpositive imaginary part. -/
theorem hadamardRegularizedLogDerivSeries_im_nonpos_of_real_indexed
    {ι : Type*} (zeroLoc : ι → ℂ)
    (H : HadamardZeroInvSqSummability zeroLoc)
    (hreal : ∀ i : ι, (zeroLoc i).im = 0)
    {s : ℂ} (hs : 0 < s.im) :
    (hadamardRegularizedLogDerivSeries zeroLoc s).im ≤ 0 := by
  let realLoc : ι → ℝ := fun i => (zeroLoc i).re
  have hloc : (fun i : ι => ((realLoc i : ℝ) : ℂ)) = zeroLoc := by
    funext i
    apply Complex.ext
    · rfl
    · simpa [realLoc] using (hreal i).symm
  have Hreal : HadamardZeroInvSqSummability
      (fun i : ι => ((realLoc i : ℝ) : ℂ)) := by
    rw [hloc]
    exact H
  simpa only [hloc] using
    hadamardRegularizedLogDerivSeries_real_im_nonpos_indexed
      realLoc Hreal hs

/-- Complex-valued series wrapper for strict negativity over a nonempty index
type. -/
theorem hadamardRegularizedLogDerivSeries_im_neg_of_real_indexed
    {ι : Type*} [Nonempty ι] (zeroLoc : ι → ℂ)
    (H : HadamardZeroInvSqSummability zeroLoc)
    (hreal : ∀ i : ι, (zeroLoc i).im = 0)
    {s : ℂ} (hs : 0 < s.im) :
    (hadamardRegularizedLogDerivSeries zeroLoc s).im < 0 := by
  let realLoc : ι → ℝ := fun i => (zeroLoc i).re
  have hloc : (fun i : ι => ((realLoc i : ℝ) : ℂ)) = zeroLoc := by
    funext i
    apply Complex.ext
    · rfl
    · simpa [realLoc] using (hreal i).symm
  have Hreal : HadamardZeroInvSqSummability
      (fun i : ι => ((realLoc i : ℝ) : ℂ)) := by
    rw [hloc]
    exact H
  simpa only [hloc] using
    hadamardRegularizedLogDerivSeries_real_im_neg_indexed
      realLoc Hreal hs

end OverflowResidueRH
