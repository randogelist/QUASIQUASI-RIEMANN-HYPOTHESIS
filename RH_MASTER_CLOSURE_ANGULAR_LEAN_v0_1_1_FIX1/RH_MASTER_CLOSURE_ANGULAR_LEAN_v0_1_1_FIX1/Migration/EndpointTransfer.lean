import Migration.LocalComparison

namespace Merger04.Migration

open Filter Merger04.Regularization
open scoped Topology

/-- Complex entire differentiability gives an analytic real centered slice. -/
theorem ENTIRE_REAL_SLICE_CONTDIFF :
    ContDiff ℝ ⊤ (realSlice entireXi) := by
  have h : ContDiff ℝ ⊤ (fun x : ℝ => (entireXi (x : ℂ)).re) :=
    (ENTIRE_XI_DIFFERENTIABLE.contDiff : ContDiff ℂ ⊤ entireXi).real_of_complex
  have hc : ContDiff ℝ ⊤ (fun x : ℝ => x + (1 / 2 : ℝ)) := by
    fun_prop
  exact h.comp hc

theorem SQRT_QUARTER : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have hp := Real.sqrt_nonneg (1 / 4 : ℝ)
  nlinarith

theorem ENTIRE_REAL_SLICE_AT_SQRT_QUARTER :
    realSlice entireXi (Real.sqrt (1 / 4 : ℝ)) = 1 := by
  rw [SQRT_QUARTER]
  norm_num [realSlice, entireXi]

/-- The regularized log derivative is analytic near the exceptional anchor:
    its denominator is nonzero there because entireXi 1 = 1. -/
theorem ENTIRE_CENTERED_R_CONTDIFF_AT_QUARTER :
    ContDiffAt ℝ ⊤ (centeredR entireXi) (1 / 4 : ℝ) := by
  have hs : ContDiffAt ℝ ⊤ Real.sqrt (1 / 4 : ℝ) :=
    Real.contDiffAt_sqrt (by norm_num)
  have hf : ContDiffAt ℝ ⊤ (realSlice entireXi) (Real.sqrt (1 / 4 : ℝ)) :=
    ENTIRE_REAL_SLICE_CONTDIFF.contDiffAt
  have hdf : ContDiffAt ℝ ⊤ (deriv (realSlice entireXi))
      (Real.sqrt (1 / 4 : ℝ)) :=
    hf.derivWithin (by simp)
  have hnum : ContDiffAt ℝ ⊤
      (fun a : ℝ => deriv (realSlice entireXi) (Real.sqrt a)) (1 / 4 : ℝ) :=
    hdf.comp (1 / 4 : ℝ) hs
  have hval : ContDiffAt ℝ ⊤
      (fun a : ℝ => realSlice entireXi (Real.sqrt a)) (1 / 4 : ℝ) :=
    hf.comp (1 / 4 : ℝ) hs
  have hden : ContDiffAt ℝ ⊤
      (fun a : ℝ => 2 * Real.sqrt a * realSlice entireXi (Real.sqrt a))
      (1 / 4 : ℝ) :=
    (contDiffAt_const.mul hs).mul hval
  have hden0 :
      2 * Real.sqrt (1 / 4 : ℝ) *
        realSlice entireXi (Real.sqrt (1 / 4 : ℝ)) ≠ 0 := by
    rw [ENTIRE_REAL_SLICE_AT_SQRT_QUARTER, SQRT_QUARTER]
    norm_num
  exact hnum.div hden hden0

theorem SCALE_D_CONTDIFF_AT
    {f : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ ⊤ f a) :
    ContDiffAt ℝ ⊤ (scaleD f) a := by
  have hd : ContDiffAt ℝ ⊤ (deriv f) a := hf.derivWithin (by simp)
  exact contDiffAt_id.mul hd

theorem SCALE_D2_CONTDIFF_AT
    {f : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ ⊤ f a) :
    ContDiffAt ℝ ⊤ (scaleD2 f) a := by
  exact SCALE_D_CONTDIFF_AT (SCALE_D_CONTDIFF_AT hf)

theorem STEP_CONTDIFF_AT
    (n : ℕ) {f : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ ⊤ f a) :
    ContDiffAt ℝ ⊤ (step n f) a := by
  have hd := SCALE_D2_CONTDIFF_AT hf
  unfold step
  exact contDiffAt_const.mul ((contDiffAt_const.mul hf).sub hd)

theorem TOWER_CONTDIFF_AT
    {f : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ ⊤ f a) (n : ℕ) :
    ContDiffAt ℝ ⊤ (tower f n) a := by
  induction n with
  | zero => exact hf
  | succ n ih => exact STEP_CONTDIFF_AT n ih

theorem ENTIRE_BASE_MOMENT_CONTDIFF_AT_QUARTER :
    ContDiffAt ℝ ⊤ (baseMoment entireXi) (1 / 4 : ℝ) := by
  have hp : ContDiffAt ℝ ⊤
      (fun a : ℝ => a * centeredR entireXi a) (1 / 4 : ℝ) :=
    contDiffAt_id.mul ENTIRE_CENTERED_R_CONTDIFF_AT_QUARTER
  have hd : ContDiffAt ℝ ⊤
      (deriv (fun a : ℝ => a * centeredR entireXi a)) (1 / 4 : ℝ) :=
    hp.derivWithin (by simp)
  exact (contDiffAt_const.mul contDiffAt_id).mul hd

/-- The exceptional value is a genuine continuous extension at every depth. -/
theorem ENTIRE_MOMENT_CONTINUOUS_AT_QUARTER (n : ℕ) :
    ContinuousAt (fun a : ℝ => moment entireXi a n) (1 / 4 : ℝ) := by
  exact (TOWER_CONTDIFF_AT ENTIRE_BASE_MOMENT_CONTDIFF_AT_QUARTER n).continuousAt

/-- A continuity argument fills a missing positive anchor without changing
    the values or derivatives of the old function at that anchor. -/
theorem NONNEGATIVE_AT_PUNCTURE
    {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hf : ContinuousAt f p)
    (h : ∀ a : ℝ, 0 < a → a ≠ p → 0 ≤ f a) :
    0 ≤ f p := by
  by_contra hnot
  have hneg : f p < 0 := lt_of_not_ge hnot
  have he : ∀ᶠ a in 𝓝 p, f a < 0 :=
    hf (isOpen_Iio.mem_nhds hneg)
  have her : ∀ᶠ a in 𝓝[>] p, f a < 0 :=
    he.filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ a in 𝓝[>] p, p < a := self_mem_nhdsWithin
  obtain ⟨a, ha, hfa⟩ := (hgt.and her).exists
  exact (not_lt_of_ge (h a (lt_trans hp ha) (ne_of_gt ha))) hfa

/-- Fixed-depth forward migration, with no analytic premise supplied by caller. -/
theorem RAW_UNIFORM_POSITIVITY_IMPLIES_REGULARIZED
    (n : ℕ) (hraw : UniformPositive rawXi n) :
    UniformPositive entireXi n := by
  have hoff : ∀ a : ℝ, 0 < a → a ≠ (1 / 4 : ℝ) →
      0 ≤ moment entireXi a n := by
    intro a ha haq
    rw [← MOMENT_EQ_AWAY_FROM_QUARTER a ha haq n]
    exact hraw a ha
  intro a ha
  by_cases haq : a = (1 / 4 : ℝ)
  · subst a
    exact NONNEGATIVE_AT_PUNCTURE (by norm_num)
      (ENTIRE_MOMENT_CONTINUOUS_AT_QUARTER n) hoff
  · exact hoff a ha haq

/-- Cofinality is preserved with exactly the same witness depths. -/
theorem RAW_PROFILE_US_IMPLIES_REGULARIZED_US
    (hUS : RawProfileUS) : RegularizedUS := by
  intro K
  obtain ⟨n, hnK, hn⟩ := hUS K
  exact ⟨n, hnK, RAW_UNIFORM_POSITIVITY_IMPLIES_REGULARIZED n hn⟩

end Merger04.Migration
