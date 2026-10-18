/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import RiemannHypothesis.ComplexAnalysis.AntiHerglotz

/-!
# Logarithmic derivative response

The logarithmic derivative `Λ[f](z) := f'(z) / f(z)` (the *overflow field*),
together with the totalization-at-zeros analysis that shows the `a / 0 = 0`
convention is harmless: the pole-witness engine only ever queries the
response at probe points `ρ − ε·I` with `ε > 0`, never at a zero.

## Main definitions

* `logDerivativeResponse f` — the logarithmic derivative `f'/f`.

## Main results

* `logDerivativeResponse_eq_zero_at_zero` — totalized response is `0` at a zero.
* `antiHerglotz_at_zero_is_vacuous` — the sign law is `0 ≤ 0` at a zero.
* `lowerProbe_ne_pole` — a probe `ρ − ε·I` (`ε > 0`) is never `ρ`.
* `antiHerglotz_iff_antiHerglotz_away_from_zeros` — the sign law reduces to its
  content on the zero-free set.
-/

namespace OverflowResidueRH

open Complex Filter Topology

-- =====================================================================
-- §3. The logarithmic derivative response
-- =====================================================================

/-- The **overflow field** / logarithmic derivative
  Λ[f](z) := f'(z) / f(z).
A signed residue cloud for any factored object. -/
noncomputable def logDerivativeResponse (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv f z / f z

-- =====================================================================
-- §6-bis. Totalization-at-zeros analysis (engine soundness)
-- =====================================================================
-- A reviewer-flagged concern: `logDerivativeResponse f z = f'(z) / f(z)`
-- evaluates to `0` at any zero of `f` because Lean uses the totalized
-- division convention `a / 0 = 0`. So the anti-Herglotz inequality
-- `Im (R z) ≤ 0` reads as `0 ≤ 0` at every zero, trivially true.
--
-- The lemmas below make precise *why this is harmless*: the
-- pole-witness engine never queries `R` at a zero — it queries `R` at a
-- probe `ρ − ε·I` with `ε > 0`, which is provably distinct from `ρ`
-- (`lowerProbe_ne_pole`). The totalization is bookkeeping, not
-- load-bearing.

/-- **PROVED — totalized log-derivative is `0` at any zero.**
Pure consequence of Lean's `a / 0 = 0` convention; recorded as a named
lemma so the totalization behaviour is explicit. -/
theorem logDerivativeResponse_eq_zero_at_zero
    {f : ℂ → ℂ} {ρ : ℂ} (hzero : f ρ = 0) :
    logDerivativeResponse f ρ = 0 := by
  unfold logDerivativeResponse
  rw [hzero, div_zero]

/-- **PROVED — anti-Herglotz inequality is vacuous at any zero.**
At a zero, both sides of `(R z).im ≤ 0` are `0`. The substantive
content of `AntiHerglotzUHP R` therefore lies entirely on the
zero-free set. -/
theorem antiHerglotz_at_zero_is_vacuous
    {f : ℂ → ℂ} {ρ : ℂ} (hzero : f ρ = 0) :
    (logDerivativeResponse f ρ).im = 0 := by
  rw [logDerivativeResponse_eq_zero_at_zero hzero]
  exact Complex.zero_im

/-- **PROVED — engine probe is never a zero.** The escape constructed by
the pole-decomposition engine lives at probe `ρ − ε·I` with `ε > 0`, and
the imaginary parts differ by exactly `ε`, so the probe is distinct from
the pole `ρ` itself. The totalization at `ρ` therefore never enters the
engine's contradiction. (The companion `probe_ne_pole` in `PoleProbe`
proves the same fact in the same form.) -/
theorem lowerProbe_ne_pole
    (ρ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ρ - (ε : ℂ) * Complex.I ≠ ρ := by
  intro h
  have him_diff : (ρ - (ε : ℂ) * Complex.I).im = ρ.im := by rw [h]
  have him_calc : (ρ - (ε : ℂ) * Complex.I).im = ρ.im - ε := by
    simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re,
          Complex.ofReal_re, Complex.ofReal_im]
  rw [him_calc] at him_diff
  linarith

/-- ⭐ **PROVED — sharper anti-Herglotz form, restricted to nonzero
points.** `AntiHerglotzUHP R` with totalized `R = Λ[f]` is *equivalent*
on its substantive content to the same inequality demanded only at points
where `f ≠ 0`. The forward direction is trivial; the backward direction
patches in the vacuous `0 ≤ 0` at zeros. This formalises the claim that
the totalization adds no proof obligations. -/
theorem antiHerglotz_iff_antiHerglotz_away_from_zeros
    (f : ℂ → ℂ) :
    AntiHerglotzUHP (logDerivativeResponse f)
      ↔ ∀ z : ℂ, 0 < z.im → f z ≠ 0 →
          (logDerivativeResponse f z).im ≤ 0 := by
  constructor
  · intro h z hz _; exact h z hz
  · intro h z hz
    by_cases hfz : f z = 0
    · rw [antiHerglotz_at_zero_is_vacuous hfz]
    · exact h z hz hfz

-- =====================================================================
-- Wave-0 analytic helpers (clean-room copies from the monolith spine).
-- These are foundational complex-analysis / real-analysis facts used by
-- the Cauchy-kernel and zero-counting layers built above this module.
-- =====================================================================

/-- ⭐ **PROVED — secant lower bound for `Real.log`** on `[α, β] ⊆ (0, ∞)`. -/
theorem Real.secant_le_log
    {α β T : ℝ} (hα : 0 < α) (hαβ : α < β) (hαT : α ≤ T) (hTβ : T ≤ β) :
    ((β - T) / (β - α)) * Real.log α + ((T - α) / (β - α)) * Real.log β
      ≤ Real.log T := by
  have hβ : 0 < β := lt_trans hα hαβ
  have hβα : 0 < β - α := by linarith
  set a := (β - T) / (β - α) with ha_def
  set b := (T - α) / (β - α) with hb_def
  have ha_nn : 0 ≤ a := div_nonneg (by linarith) (le_of_lt hβα)
  have hb_nn : 0 ≤ b := div_nonneg (by linarith) (le_of_lt hβα)
  have hab : a + b = 1 := by
    unfold a b
    rw [← add_div, show β - T + (T - α) = β - α from by ring, div_self hβα.ne']
  have h_avg : a * α + b * β = T := by
    unfold a b
    field_simp
    ring
  have hα_mem : α ∈ Set.Ioi (0 : ℝ) := hα
  have hβ_mem : β ∈ Set.Ioi (0 : ℝ) := hβ
  have h_concave := strictConcaveOn_log_Ioi.concaveOn.2 hα_mem hβ_mem ha_nn hb_nn hab
  simp only [smul_eq_mul] at h_concave
  rw [h_avg] at h_concave
  exact h_concave

/-- ⭐ **PROVED — Im of `1/(a + I·b)²`** when `a² + b² ≠ 0`:
  `Im(1/(a + I·b)²) = -2·a·b / (a² + b²)²`.
Direct algebra via `Complex.inv_im` + `Complex.normSq`. -/
lemma im_inv_sq_complex (a b : ℝ) (_h : a ^ 2 + b ^ 2 ≠ 0) :
    (((a : ℂ) + Complex.I * (b : ℂ)) ^ 2)⁻¹.im
      = -2 * a * b / (a ^ 2 + b ^ 2) ^ 2 := by
  have hsq_re : (((a : ℂ) + Complex.I * (b : ℂ)) ^ 2).re = a ^ 2 - b ^ 2 := by
    rw [pow_two]
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq_im : (((a : ℂ) + Complex.I * (b : ℂ)) ^ 2).im = 2 * a * b := by
    rw [pow_two]
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.inv_im, hsq_im, Complex.normSq_apply, hsq_re, hsq_im]
  have h_denom :
      (a ^ 2 - b ^ 2) * (a ^ 2 - b ^ 2) + 2 * a * b * (2 * a * b)
        = (a ^ 2 + b ^ 2) ^ 2 := by
    ring
  rw [h_denom]
  ring

/-- ⭐ **PROVED — `IntervalIntegrable.ofReal` for ℝ → ℂ.** Lifts real
interval integrability to ℂ via the pointwise coercion. Built from
Mathlib's `MeasureTheory.Integrable.ofReal` on each of the two
`IntegrableOn` halves of `IntervalIntegrable`. -/
lemma intervalIntegrable_ofReal
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun u => ((f u : ℝ) : ℂ))
      MeasureTheory.volume a b :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

/-- 🌟🌟🌟 **PROVED — complex improper convergence from a real
norm-majorant.** Mirrors §CCV's real-side comparison theorem. Proof:
Cauchy criterion via `Metric.cauchy_iff`, with the key step
`‖∫_{Y1}^{Y2} f‖ ≤ ∫_{Y1}^{Y2} ‖f u‖ du ≤ ∫_{Y1}^{Y2} M u du`
(combining `MeasureTheory.norm_integral_le_integral_norm` and
`intervalIntegral.integral_mono_on`) plus the M-tail smallness from
the M-partial Cauchy structure. -/
theorem improperComplexIntegralConverges_of_normMajorant
    {f : ℝ → ℂ} {M : ℝ → ℝ} {T LM : ℝ}
    (hf_int : ∀ X, T ≤ X → IntervalIntegrable f MeasureTheory.volume T X)
    (hM_int : ∀ X, T ≤ X → IntervalIntegrable M MeasureTheory.volume T X)
    (hM_tendsto : Filter.Tendsto (fun X => ∫ u in T..X, M u)
                    Filter.atTop (𝓝 LM))
    (hbound : ∀ᶠ u in Filter.atTop, ‖f u‖ ≤ M u) :
    ∃ L : ℂ, Filter.Tendsto (fun X => ∫ u in T..X, f u) Filter.atTop (𝓝 L) := by
  have h_cauchy :
      Cauchy (Filter.map (fun X => ∫ u in T..X, f u) Filter.atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, ?_⟩
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have h_M_close : ∀ᶠ A in Filter.atTop,
        |(∫ u in T..A, M u) - LM| < ε / 2 := by
      have h := (Metric.tendsto_nhds.mp hM_tendsto) (ε / 2) hε2
      filter_upwards [h] with A hdist
      rwa [Real.dist_eq] at hdist
    obtain ⟨N_M, hN_M⟩ := Filter.eventually_atTop.mp h_M_close
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbound
    let N : ℝ := max T (max N0 N_M)
    refine ⟨(fun X => ∫ u in T..X, f u) '' {X | N ≤ X}, ?_, ?_⟩
    · exact Filter.image_mem_map (Filter.eventually_ge_atTop N)
    suffices key :
        ∀ Y1 Y2 : ℝ, N ≤ Y1 → N ≤ Y2 → Y1 ≤ Y2 →
          ‖(∫ u in T..Y2, f u) - (∫ u in T..Y1, f u)‖ < ε by
      rintro _ ⟨X1, hX1, rfl⟩ _ ⟨X2, hX2, rfl⟩
      rw [dist_eq_norm]
      rcases le_total X1 X2 with hX12 | hX21
      · rw [norm_sub_rev]; exact key X1 X2 hX1 hX2 hX12
      · exact key X2 X1 hX2 hX1 hX21
    intro Y1 Y2 hY1 hY2 hY12
    have hT_Y1 : T ≤ Y1 := le_trans (le_max_left T _) hY1
    have hT_Y2 : T ≤ Y2 := le_trans (le_max_left T _) hY2
    have hN0_Y1 : N0 ≤ Y1 :=
      le_trans (le_trans (le_max_left N0 N_M) (le_max_right T _)) hY1
    have hN_M_Y1 : N_M ≤ Y1 :=
      le_trans (le_trans (le_max_right N0 N_M) (le_max_right T _)) hY1
    have hN_M_Y2 : N_M ≤ Y2 :=
      le_trans (le_trans (le_max_right N0 N_M) (le_max_right T _)) hY2
    have hf_int_TY2 := hf_int Y2 hT_Y2
    have hf_int_TY1 : IntervalIntegrable f MeasureTheory.volume T Y1 :=
      hf_int_TY2.mono_set (by
        rw [Set.uIcc_of_le hT_Y1, Set.uIcc_of_le hT_Y2]
        exact Set.Icc_subset_Icc_right hY12)
    have hf_int_Y1Y2 : IntervalIntegrable f MeasureTheory.volume Y1 Y2 :=
      hf_int_TY2.mono_set (by
        rw [Set.uIcc_of_le hY12, Set.uIcc_of_le hT_Y2]
        exact Set.Icc_subset_Icc_left hT_Y1)
    have hM_int_TY2 := hM_int Y2 hT_Y2
    have hM_int_TY1 : IntervalIntegrable M MeasureTheory.volume T Y1 :=
      hM_int_TY2.mono_set (by
        rw [Set.uIcc_of_le hT_Y1, Set.uIcc_of_le hT_Y2]
        exact Set.Icc_subset_Icc_right hY12)
    have hM_int_Y1Y2 : IntervalIntegrable M MeasureTheory.volume Y1 Y2 :=
      hM_int_TY2.mono_set (by
        rw [Set.uIcc_of_le hY12, Set.uIcc_of_le hT_Y2]
        exact Set.Icc_subset_Icc_left hT_Y1)
    have h_split_f : (∫ u in T..Y2, f u) =
        (∫ u in T..Y1, f u) + ∫ u in Y1..Y2, f u :=
      (intervalIntegral.integral_add_adjacent_intervals
        hf_int_TY1 hf_int_Y1Y2).symm
    have h_tail_f :
        (∫ u in T..Y2, f u) - (∫ u in T..Y1, f u) = ∫ u in Y1..Y2, f u := by
      rw [h_split_f]; ring
    rw [h_tail_f]
    have hbound_Y1Y2 : ∀ u ∈ Set.Icc Y1 Y2, ‖f u‖ ≤ M u := by
      intro u hu
      exact hN0 u (le_trans hN0_Y1 hu.1)
    have h_norm_int : ‖∫ u in Y1..Y2, f u‖ ≤ ∫ u in Y1..Y2, ‖f u‖ := by
      rw [intervalIntegral.integral_of_le hY12,
          intervalIntegral.integral_of_le hY12]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have h_mono : ∫ u in Y1..Y2, ‖f u‖ ≤ ∫ u in Y1..Y2, M u :=
      intervalIntegral.integral_mono_on hY12 hf_int_Y1Y2.norm hM_int_Y1Y2
        hbound_Y1Y2
    have h_comp : ‖∫ u in Y1..Y2, f u‖ ≤ ∫ u in Y1..Y2, M u :=
      le_trans h_norm_int h_mono
    have h_split_M : (∫ u in T..Y2, M u) =
        (∫ u in T..Y1, M u) + ∫ u in Y1..Y2, M u :=
      (intervalIntegral.integral_add_adjacent_intervals
        hM_int_TY1 hM_int_Y1Y2).symm
    have h_M_tail_eq : ∫ u in Y1..Y2, M u =
        (∫ u in T..Y2, M u) - (∫ u in T..Y1, M u) := by linarith
    have h_M_close_Y1 := hN_M Y1 hN_M_Y1
    have h_M_close_Y2 := hN_M Y2 hN_M_Y2
    have h_M_diff_lt :
        |(∫ u in T..Y2, M u) - (∫ u in T..Y1, M u)| < ε := by
      calc |(∫ u in T..Y2, M u) - (∫ u in T..Y1, M u)|
          ≤ |(∫ u in T..Y2, M u) - LM| + |LM - (∫ u in T..Y1, M u)| :=
              abs_sub_le _ _ _
        _ = |(∫ u in T..Y2, M u) - LM| + |(∫ u in T..Y1, M u) - LM| := by
              rw [abs_sub_comm LM]
        _ < ε / 2 + ε / 2 := add_lt_add h_M_close_Y2 h_M_close_Y1
        _ = ε := by ring
    rw [h_M_tail_eq] at h_comp
    have h_le_abs :
        (∫ u in T..Y2, M u) - (∫ u in T..Y1, M u)
          ≤ |(∫ u in T..Y2, M u) - (∫ u in T..Y1, M u)| := le_abs_self _
    linarith
  obtain ⟨L, hL⟩ := CompleteSpace.complete h_cauchy
  exact ⟨L, hL⟩

/-- ⭐ **PROVED — reciprocal-square norm bound.** If `‖w‖ ≥ u/2 > 0`,
then `‖1/w²‖ ≤ 4/u²`. -/
lemma norm_inv_sq_le_four_div_sq_of_norm_ge_half
    {w : ℂ} {u : ℝ} (hu : 0 < u) (hw : u / 2 ≤ ‖w‖) :
    ‖(1 : ℂ) / w^2‖ ≤ 4 / u^2 := by
  have hu_half_pos : 0 < u / 2 := by linarith
  have hw_pos : 0 < ‖w‖ := lt_of_lt_of_le hu_half_pos hw
  have h_sq : (u / 2)^2 ≤ ‖w‖^2 :=
    sq_le_sq' (by linarith [norm_nonneg w]) hw
  have hw_sq_pos : 0 < ‖w‖^2 := by positivity
  have hu_sq_pos : 0 < u^2 := by positivity
  rw [norm_div, norm_one, norm_pow, div_le_div_iff₀ hw_sq_pos hu_sq_pos]
  nlinarith [h_sq]

/-- ⭐ **PROVED — `log X / X → 0`** as `X → ∞`. Via Mathlib's
`Real.tendsto_pow_log_div_mul_add_atTop` specialized to `n = 1, a = 1,
b = 0`. -/
lemma log_div_id_atTop_tendsto_zero :
    Filter.Tendsto (fun X : ℝ => Real.log X / X) Filter.atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1
    (by norm_num : (1 : ℝ) ≠ 0)
  simpa using this

/-- ⭐ **PROVED — `z - (u : ℂ) ≠ 0` when `0 < z.im`.** -/
lemma complex_sub_real_ne_zero_of_im_pos
    {z : ℂ} (hz : 0 < z.im) (u : ℝ) :
    z - (u : ℂ) ≠ 0 := by
  intro h
  have him : (z - (u : ℂ)).im = 0 := by rw [h]; rfl
  have him' : (z - (u : ℂ)).im = z.im := by simp
  rw [him'] at him
  linarith

/-- ⭐ **PROVED — `z + (u : ℂ) ≠ 0` when `0 < z.im`.** -/
lemma complex_add_real_ne_zero_of_im_pos
    {z : ℂ} (hz : 0 < z.im) (u : ℝ) :
    z + (u : ℂ) ≠ 0 := by
  intro h
  have him : (z + (u : ℂ)).im = 0 := by rw [h]; rfl
  have him' : (z + (u : ℂ)).im = z.im := by simp
  rw [him'] at him
  linarith

/-- ⭐ **PROVED — algebra cleanup for arctan-shift derivative.** Isolates
the field manipulation `(1/y) / (1 + ((u - a)/y)²) = y/((u - a)² + y²)`. -/
lemma arctan_shift_deriv_algebra
    {a y u : ℝ} (hy : y ≠ 0) :
    (1 / (1 + ((u - a) / y) ^ 2)) * (1 / y)
      = y / ((u - a) ^ 2 + y ^ 2) := by
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  field_simp
  ring

/-- 🌟 **PROVED — `arctan ((X - a)/y) → π/2` as `X → ∞` for `y > 0`.**
The inner shift `(X - a)/y → ∞` (since `y > 0`); compose with
`Real.tendsto_arctan_atTop`. -/
lemma tendsto_arctan_shift_atTop
    (a : ℝ) {y : ℝ} (hy : 0 < y) :
    Filter.Tendsto
      (fun X : ℝ => Real.arctan ((X - a) / y))
      Filter.atTop
      (𝓝 (Real.pi / 2)) := by
  have h_shift : Filter.Tendsto (fun X : ℝ => (X - a) / y)
      Filter.atTop Filter.atTop := by
    have h_sub : Filter.Tendsto (fun X : ℝ => X - a) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right Filter.atTop (-a) Filter.tendsto_id
    exact h_sub.atTop_div_const hy
  have h_arctan_at_top :
      Filter.Tendsto Real.arctan Filter.atTop (𝓝 (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  exact h_arctan_at_top.comp h_shift

/-- ⭐ **PROVED — interval integrability of the one-sided Cauchy kernel.**
The integrand is continuous (denominator strictly positive for
`y ≠ 0`), hence interval-integrable on any `[T, X]`. -/
lemma cauchy_one_side_intervalIntegrable
    (a T X : ℝ) {y : ℝ} (hy : y ≠ 0) :
    IntervalIntegrable
      (fun u => y / ((u - a) ^ 2 + y ^ 2))
      MeasureTheory.volume T X := by
  have h_cont : Continuous (fun u : ℝ => y / ((u - a) ^ 2 + y ^ 2)) := by
    refine continuous_const.div ?_ ?_
    · exact ((continuous_id.sub continuous_const).pow 2).add continuous_const
    · intro u
      have h1 : (0 : ℝ) ≤ (u - a) ^ 2 := sq_nonneg _
      have h2 : (0 : ℝ) < y ^ 2 := by positivity
      linarith
  exact h_cont.intervalIntegrable T X

/-- 🌟 **PROVED — derivative of `arctan t − t/(1+t²)` is `2t²/(1+t²)²`.**
Chain through `Real.hasDerivAt_arctan` + quotient rule. -/
lemma hasDerivAt_arctan_minus_div_one_add_sq (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => Real.arctan x - x / (1 + x ^ 2))
      (2 * t ^ 2 / (1 + t ^ 2) ^ 2)
      t := by
  have h_arctan : HasDerivAt Real.arctan (1 / (1 + t ^ 2)) t :=
    Real.hasDerivAt_arctan t
  have h_id : HasDerivAt (fun x : ℝ => x) (1 : ℝ) t := hasDerivAt_id t
  have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    have h : HasDerivAt (fun x : ℝ => x ^ 2)
        (((2 : ℕ) : ℝ) * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
    norm_num at h
    exact h
  have h_den : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).add h_sq
    rwa [zero_add] at h
  have h_ne : (1 : ℝ) + t ^ 2 ≠ 0 := by
    have h1 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    linarith
  have h_div :
      HasDerivAt (fun x : ℝ => x / (1 + x ^ 2))
        ((1 * (1 + t ^ 2) - t * (2 * t)) / (1 + t ^ 2) ^ 2) t :=
    h_id.div h_den h_ne
  have h_sub := h_arctan.sub h_div
  convert h_sub using 1
  all_goals first
    | rfl
    | (field_simp [h_ne]; ring)

/-- ⭐ **PROVED — `π/2 − arctan s = arctan (1/s)` for `s > 0`.**
Direct from Mathlib's `Real.arctan_inv_of_pos`. -/
lemma pi_div_two_sub_arctan_eq_arctan_inv
    {s : ℝ} (hs : 0 < s) :
    Real.pi / 2 - Real.arctan s = Real.arctan (1 / s) := by
  rw [one_div]
  exact (Real.arctan_inv_of_pos hs).symm

/-- ⭐ **PROVED — generic pointwise list sum bound.** -/
lemma list_sum_le_sum_of_pointwise
    {α : Type*} {L : List α} {f g : α → ℝ}
    (h : ∀ a ∈ L, f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h_a : f a ≤ g a := h a (by simp)
    have h_rest : ∀ b ∈ rest, f b ≤ g b :=
      fun b hb => h b (List.mem_cons_of_mem a hb)
    have h_rest_le := ih h_rest
    linarith

/-- ⭐ **PROVED — kernel-factor polynomial bound**
`((10−a)²+y²)·((10+a)²+y²) ≤ 116·(100−a²+y²)` on `a²+y² ≤ 16`. -/
lemma kernel_factor_den_le_aux
    {a y : ℝ} (_ha_nn : 0 ≤ a) (hbox : a ^ 2 + y ^ 2 ≤ 16) :
    ((10 - a) ^ 2 + y ^ 2) * ((10 + a) ^ 2 + y ^ 2)
      ≤ 116 * (100 - a ^ 2 + y ^ 2) := by
  have hu : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  have hv : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hnn : (0 : ℝ) ≤ a ^ 2 + y ^ 2 := by linarith
  have hv_le_16 : y ^ 2 ≤ 16 := by linarith
  have h_w_sq_le_256 :
      (a ^ 2 + y ^ 2) * (a ^ 2 + y ^ 2) ≤ 256 := by
    have h_mul : (a ^ 2 + y ^ 2) * (a ^ 2 + y ^ 2)
                ≤ (a ^ 2 + y ^ 2) * 16 :=
      mul_le_mul_of_nonneg_left hbox hnn
    linarith
  have h_lhs_expand :
      ((10 - a) ^ 2 + y ^ 2) * ((10 + a) ^ 2 + y ^ 2)
        = (a ^ 2 + y ^ 2) * (a ^ 2 + y ^ 2)
          + 200 * (a ^ 2 + y ^ 2) - 400 * a ^ 2 + 10000 := by
    ring
  rw [h_lhs_expand]
  linarith [h_w_sq_le_256, hu, hv, hv_le_16]

/-- 🌟🌟🌟 **PROVED — finite-fiber regrouping criterion for nonnegative
real series.**

This is the summability engine needed for the Riemann-von Mangoldt side:
partition a nonnegative family into finite fibers, dominate the `tsum` of
each fiber by a summable sequence, and the original family is summable. -/
theorem summable_of_nonneg_fiber_tsum_le
    {ι : Type*}
    (bin : ι → ℕ)
    {f : ι → ℝ} {majorant : ℕ → ℝ}
    (hf_nonneg : ∀ i, 0 ≤ f i)
    (hfiber : ∀ n : ℕ, {i : ι | bin i = n}.Finite)
    (hmajorant : Summable majorant)
    (hfiber_le :
      ∀ n : ℕ,
        (∑' i : {i : ι // bin i = n}, f i) ≤ majorant n) :
    Summable f := by
  classical
  let F : (Σ n : ℕ, {i : ι // bin i = n}) → ℝ :=
    fun p => f p.2.1
  have hF_nonneg : ∀ p, 0 ≤ F p := by
    intro p
    exact hf_nonneg p.2.1
  have hfiber_summable :
      ∀ n : ℕ, Summable fun i : {i : ι // bin i = n} => F ⟨n, i⟩ := by
    intro n
    haveI : Fintype {i : ι // bin i = n} := (hfiber n).fintype
    exact (hasSum_fintype (fun i : {i : ι // bin i = n} => F ⟨n, i⟩)).summable
  have hfiber_tsum_nonneg :
      ∀ n : ℕ, 0 ≤ ∑' i : {i : ι // bin i = n}, F ⟨n, i⟩ := by
    intro n
    exact tsum_nonneg (fun i => hf_nonneg i.1)
  have hfiber_tsum_summable :
      Summable fun n : ℕ =>
        ∑' i : {i : ι // bin i = n}, F ⟨n, i⟩ :=
    Summable.of_nonneg_of_le
      hfiber_tsum_nonneg
      (fun n => by simpa [F] using hfiber_le n)
      hmajorant
  have hF_summable : Summable F := by
    exact (summable_sigma_of_nonneg hF_nonneg).mpr
      ⟨hfiber_summable, hfiber_tsum_summable⟩
  exact (Equiv.sigmaFiberEquiv bin).summable_iff.mp (by
    exact hF_summable)

/-- 🌟🌟🌟 **PROVED — `log n / (n-1)^2` is summable.**

This is the classical convergence input behind the Riemann–von Mangoldt shell
route: an annular zero count of size `O(log n)` produces an inverse-square mass
of size `O(log n / n^2)`, which is summable.  The proof compares with the
convergent `p`-series `∑ 1 / n^(3/2)` using `log n = o(n^(1/2))`. -/
theorem summable_log_natCast_mul_pred_sq_inv :
    Summable (fun n : ℕ => Real.log n * (((n - 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  have hsummable_rpow : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  refine summable_of_isBigO_nat hsummable_rpow ?_
  have hlog :
      (fun n : ℕ => Real.log n) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).isBigO
    exact h.comp_tendsto tendsto_natCast_atTop_atTop
  have hinv :
      (fun n : ℕ => (((n - 1 : ℕ) : ℝ) ^ 2)⁻¹) =O[Filter.atTop]
        (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    refine Asymptotics.IsBigO.of_bound 4 ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hx : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      hcast, inv_eq_one_div, inv_eq_one_div, mul_one_div,
      div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith [hx]
  have hmul := hlog.mul hinv
  refine hmul.trans ?_
  refine Filter.EventuallyEq.isBigO ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have e2 : ((n : ℝ) ^ 2) = (n : ℝ) ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have key :
      (n : ℝ) ^ (1 / 2 : ℝ) * ((n : ℝ) ^ 2)⁻¹ = (n : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [e2, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
    congr 1
    norm_num
  rw [key, Real.rpow_neg hn0.le, one_div]

-- =====================================================================
-- Wave-next analytic helpers: arctan rational bounds + `log(T/2π)`
-- endpoint estimates feeding the zero-counting / Backlund-Turing layers.
-- Clean-room copies from the monolith spine.
-- =====================================================================

/-- 🌟 **PROVED — chain rule: derivative of `arctan ((u - a) / y)` in `u`.** -/
lemma hasDerivAt_arctan_shift_div
    (a : ℝ) {y : ℝ} (hy : y ≠ 0) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ => Real.arctan ((v - a) / y))
      (y / ((u - a) ^ 2 + y ^ 2))
      u := by
  have h_inner :
      HasDerivAt (fun v : ℝ => (v - a) / y) (1 / y) u := by
    have h_sub : HasDerivAt (fun v : ℝ => v - a) (1 : ℝ) u :=
      (hasDerivAt_id u).sub_const a
    simpa [one_div] using h_sub.div_const y
  have h_arctan :=
    (Real.hasDerivAt_arctan ((u - a) / y)).comp u h_inner
  have h_eq := arctan_shift_deriv_algebra (a := a) (y := y) (u := u) hy
  rw [h_eq] at h_arctan
  exact h_arctan

/-- 🌟🌟 **PROVED — `s/(1+s²) ≤ arctan s` for `s ≥ 0`.** Routes through
the FTC for `f(t) := arctan t − t/(1+t²)`, noting `f(0) = 0` and
`f' ≥ 0`. -/
lemma div_one_add_sq_le_arctan {s : ℝ} (hs : 0 ≤ s) :
    s / (1 + s ^ 2) ≤ Real.arctan s := by
  have h_zero : Real.arctan 0 - 0 / (1 + (0 : ℝ) ^ 2) = 0 := by
    rw [Real.arctan_zero]; simp
  have h_cont :
      Continuous (fun t : ℝ => 2 * t ^ 2 / (1 + t ^ 2) ^ 2) := by
    refine (continuous_const.mul (continuous_pow 2)).div ?_ ?_
    · exact ((continuous_const.add (continuous_pow 2)).pow 2)
    · intro t
      have h1 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
      have h_pos : (0 : ℝ) < 1 + t ^ 2 := by linarith
      have : (0 : ℝ) < (1 + t ^ 2) ^ 2 := by positivity
      linarith
  have hFTC :
      (Real.arctan s - s / (1 + s ^ 2))
          - (Real.arctan 0 - 0 / (1 + (0 : ℝ) ^ 2))
        = ∫ t in (0 : ℝ)..s, 2 * t ^ 2 / (1 + t ^ 2) ^ 2 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_arctan_minus_div_one_add_sq t)
      (h_cont.intervalIntegrable 0 s)
    exact h.symm
  rw [h_zero, sub_zero] at hFTC
  have h_int_nn :
      0 ≤ ∫ t in (0 : ℝ)..s, 2 * t ^ 2 / (1 + t ^ 2) ^ 2 := by
    apply intervalIntegral.integral_nonneg hs
    intro u _
    have h_t_sq : (0 : ℝ) ≤ 2 * u ^ 2 := by nlinarith [sq_nonneg u]
    have h_den : (0 : ℝ) < (1 + u ^ 2) ^ 2 := by positivity
    exact div_nonneg h_t_sq (le_of_lt h_den)
  linarith

/-- ⭐ **PROVED — `π/2 − arctan(A/y) = arctan(y/A)` for `A, y > 0`.**
CLV-shaped specialization of the complement identity. -/
lemma pi_div_two_sub_arctan_shift_eq_arctan_div
    {A y : ℝ} (hA : 0 < A) (hy : 0 < y) :
    Real.pi / 2 - Real.arctan (A / y) = Real.arctan (y / A) := by
  have hs : 0 < A / y := div_pos hA hy
  rw [pi_div_two_sub_arctan_eq_arctan_inv hs]
  congr 1
  field_simp

/-- ⭐ **PROVED — Endpoint bound: `log(10/(2π)) ≥ 9/25`.**
Chain: `exp(-9/25) ≥ 16/25` (from `add_one_le_exp`) ⟹ `exp(9/25) ≤ 25/16`
⟹ `25/16 ≤ 10/(2π)` (since `π < 3.15 < 3.2 = 16/5`). -/
lemma log_10_div_2pi_ge_9_25 :
    (9 / 25 : ℝ) ≤ Real.log (10 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_pos : 0 < Real.exp (9/25) := Real.exp_pos _
  have h_one_sub : (-(9/25 : ℝ)) + 1 ≤ Real.exp (-(9/25)) := Real.add_one_le_exp _
  have h_1625 : (16/25 : ℝ) ≤ Real.exp (-(9/25)) := by linarith
  rw [Real.exp_neg] at h_1625
  have h_exp_le : Real.exp (9/25) ≤ 25/16 := by
    have := mul_le_mul_of_nonneg_right h_1625 (le_of_lt h_exp_pos)
    rw [inv_mul_cancel₀ (ne_of_gt h_exp_pos)] at this
    linarith
  have h_10_2pi_ge : (25/16 : ℝ) ≤ 10 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]; nlinarith
  have h_T_ge_exp : Real.exp (9/25) ≤ 10 / (2 * Real.pi) :=
    le_trans h_exp_le h_10_2pi_ge
  have h := Real.log_le_log h_exp_pos h_T_ge_exp
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — Helper 3a: `log(12/(2π)) ≥ 2/5`.**
Via `Real.add_one_le_exp(-2/5)` ⟹ `exp(2/5) ≤ 5/3 ≤ 12/(2π)`. -/
lemma log_12_div_2pi_ge_2_5 :
    (2 / 5 : ℝ) ≤ Real.log (12 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_pos : 0 < Real.exp (2/5) := Real.exp_pos _
  have h_one_sub : (-(2/5 : ℝ)) + 1 ≤ Real.exp (-(2/5)) := Real.add_one_le_exp _
  have h_35 : (3/5 : ℝ) ≤ Real.exp (-(2/5)) := by linarith
  rw [Real.exp_neg] at h_35
  have h_exp_le : Real.exp (2/5) ≤ 5/3 := by
    have := mul_le_mul_of_nonneg_right h_35 (le_of_lt h_exp_pos)
    rw [inv_mul_cancel₀ (ne_of_gt h_exp_pos)] at this
    linarith
  have h_12_2pi_ge : (5/3 : ℝ) ≤ 12 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]; nlinarith
  have h_T_ge_exp : Real.exp (2/5) ≤ 12 / (2 * Real.pi) :=
    le_trans h_exp_le h_12_2pi_ge
  have h := Real.log_le_log h_exp_pos h_T_ge_exp
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — Helper 3b: `log(13/(2π)) ≥ 1/2`.**
Via `Real.add_one_le_exp(-1/2)` ⟹ `exp(1/2) ≤ 2 ≤ 13/(2π)`. -/
lemma log_13_div_2pi_ge_1_2 :
    (1 / 2 : ℝ) ≤ Real.log (13 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_pos : 0 < Real.exp (1/2) := Real.exp_pos _
  have h_one_sub : (-(1/2 : ℝ)) + 1 ≤ Real.exp (-(1/2)) := Real.add_one_le_exp _
  have h_half : (1/2 : ℝ) ≤ Real.exp (-(1/2)) := by linarith
  rw [Real.exp_neg] at h_half
  have h_exp_le : Real.exp (1/2) ≤ 2 := by
    have := mul_le_mul_of_nonneg_right h_half (le_of_lt h_exp_pos)
    rw [inv_mul_cancel₀ (ne_of_gt h_exp_pos)] at this
    linarith
  have h_13_2pi_ge : (2 : ℝ) ≤ 13 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]; nlinarith
  have h_T_ge_exp : Real.exp (1/2) ≤ 13 / (2 * Real.pi) :=
    le_trans h_exp_le h_13_2pi_ge
  have h := Real.log_le_log h_exp_pos h_T_ge_exp
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — `log(14/(2π)) ≥ 3/4`.**
Cubing: `(exp 1)^3 < 2.7182818286^3 ≤ (17/8)^4` (norm_num).
∴ `exp 3 ≤ (17/8)^4`. Hence `exp(3/4)^4 ≤ (17/8)^4`, so
`exp(3/4) ≤ 17/8`. Finally `17/8 ≤ 14/(2π)` since `(17/8)·(2π) ≤ 14`
via `π < 3.1416`. -/
lemma log_14_div_2pi_ge_3_4 :
    (3 / 4 : ℝ) ≤ Real.log (14 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_1_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_2718_pos : (0 : ℝ) < 2.7182818286 := by norm_num
  have h_exp_1_cubed_lt : (Real.exp 1)^3 < (2.7182818286 : ℝ)^3 := by
    have := pow_lt_pow_left₀ h_exp_1_lt (le_of_lt h_exp_1_pos) (n := 3) (by norm_num)
    exact this
  have h_27_cube_le : (2.7182818286 : ℝ)^3 ≤ (17/8 : ℝ)^4 := by norm_num
  have h_exp_1_cubed_le : (Real.exp 1)^3 ≤ (17/8 : ℝ)^4 := by linarith
  have h_exp_3_eq : Real.exp 3 = (Real.exp 1)^3 := by
    have := Real.exp_one_pow 3
    have h_cast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    rw [← h_cast]
    exact this.symm
  have h_exp_3_4_pow : (Real.exp (3/4 : ℝ))^4 = Real.exp 3 := by
    have := Real.exp_nat_mul (3/4 : ℝ) 4
    have h_eq : ((4 : ℕ) : ℝ) * (3/4 : ℝ) = 3 := by norm_num
    rw [h_eq] at this
    exact this.symm
  have h_exp_3_le : Real.exp 3 ≤ (17/8 : ℝ)^4 := h_exp_3_eq ▸ h_exp_1_cubed_le
  have h_exp_3_4_le : Real.exp (3/4 : ℝ) ≤ 17/8 := by
    have h_pow_4_le : (Real.exp (3/4 : ℝ))^4 ≤ (17/8 : ℝ)^4 := h_exp_3_4_pow ▸ h_exp_3_le
    have h_exp_pos : 0 ≤ Real.exp (3/4 : ℝ) := le_of_lt (Real.exp_pos _)
    have h_178_pos : (0 : ℝ) ≤ 17/8 := by norm_num
    exact (pow_le_pow_iff_left₀ h_exp_pos h_178_pos (by norm_num : (4 : ℕ) ≠ 0)).mp h_pow_4_le
  have h_178_le_142pi : (17/8 : ℝ) ≤ 14 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]
    nlinarith
  have h_exp_le_ratio : Real.exp (3/4 : ℝ) ≤ 14 / (2 * Real.pi) :=
    le_trans h_exp_3_4_le h_178_le_142pi
  have h_exp_pos : 0 < Real.exp (3/4 : ℝ) := Real.exp_pos _
  have h := Real.log_le_log h_exp_pos h_exp_le_ratio
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — Endpoint bound: `log(19/(2π)) ≥ 11/10`.**
Chain: `exp 1 < 2.7182818286` → `(exp 1)^11 < 2.7182818286^11 ≤ (301/100)^10`
→ `exp(11/10)^10 ≤ (301/100)^10` → `exp(11/10) ≤ 301/100`
→ `301/100 ≤ 19/(2π)` via `π < 3.1416`. -/
lemma log_19_div_2pi_ge_11_10 :
    (11 / 10 : ℝ) ≤ Real.log (19 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_1_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_exp_1_nn : 0 ≤ Real.exp 1 := le_of_lt h_exp_1_pos
  have h_exp_1_11_lt : (Real.exp 1)^11 < (2.7182818286 : ℝ)^11 :=
    pow_lt_pow_left₀ h_exp_1_lt h_exp_1_nn (by norm_num)
  have h_27_le_301 : (2.7182818286 : ℝ)^11 ≤ (301/100 : ℝ)^10 := by norm_num
  have h_exp_1_11_le : (Real.exp 1)^11 ≤ (301/100 : ℝ)^10 := by linarith
  have h_exp_11_eq : Real.exp 11 = (Real.exp 1)^11 := by
    have h := Real.exp_one_pow 11
    have h_cast : ((11 : ℕ) : ℝ) = (11 : ℝ) := by norm_num
    rw [← h_cast]; exact h.symm
  have h_exp_11_10_pow : (Real.exp (11/10 : ℝ))^10 = Real.exp 11 := by
    have h := Real.exp_nat_mul (11/10 : ℝ) 10
    have h_eq : ((10 : ℕ) : ℝ) * (11/10 : ℝ) = 11 := by norm_num
    rw [h_eq] at h
    exact h.symm
  have h_exp_11_le : Real.exp 11 ≤ (301/100 : ℝ)^10 := h_exp_11_eq ▸ h_exp_1_11_le
  have h_exp_11_10_le : Real.exp (11/10 : ℝ) ≤ 301/100 := by
    have h_pow_10_le : (Real.exp (11/10 : ℝ))^10 ≤ (301/100 : ℝ)^10 :=
      h_exp_11_10_pow ▸ h_exp_11_le
    have h_exp_pos : 0 ≤ Real.exp (11/10 : ℝ) := le_of_lt (Real.exp_pos _)
    have h_301_pos : (0 : ℝ) ≤ 301/100 := by norm_num
    exact (pow_le_pow_iff_left₀ h_exp_pos h_301_pos
              (by norm_num : (10 : ℕ) ≠ 0)).mp h_pow_10_le
  have h_301_le_192pi : (301/100 : ℝ) ≤ 19 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]
    nlinarith
  have h_exp_11_10_le_192pi : Real.exp (11/10 : ℝ) ≤ 19 / (2 * Real.pi) :=
    le_trans h_exp_11_10_le h_301_le_192pi
  have h_exp_pos : 0 < Real.exp (11/10 : ℝ) := Real.exp_pos _
  have h := Real.log_le_log h_exp_pos h_exp_11_10_le_192pi
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — Endpoint bound: `log(32/(2π)) ≥ 8/5`.**
Chain: `(exp 1)^8 < 2.7182818286^8 ≤ 5^5` → `exp(8/5) ≤ 5`
→ `5 ≤ 32/(2π)` via `π < 3.15`. -/
lemma log_32_div_2pi_ge_8_5 :
    (8 / 5 : ℝ) ≤ Real.log (32 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_1_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_exp_1_nn : 0 ≤ Real.exp 1 := le_of_lt h_exp_1_pos
  have h_exp_1_8_lt : (Real.exp 1)^8 < (2.7182818286 : ℝ)^8 :=
    pow_lt_pow_left₀ h_exp_1_lt h_exp_1_nn (by norm_num)
  have h_27_le_5 : (2.7182818286 : ℝ)^8 ≤ (5 : ℝ)^5 := by norm_num
  have h_exp_1_8_le : (Real.exp 1)^8 ≤ (5 : ℝ)^5 := by linarith
  have h_exp_8_eq : Real.exp 8 = (Real.exp 1)^8 := by
    have h := Real.exp_one_pow 8
    have h_cast : ((8 : ℕ) : ℝ) = (8 : ℝ) := by norm_num
    rw [← h_cast]; exact h.symm
  have h_exp_8_5_pow : (Real.exp (8/5 : ℝ))^5 = Real.exp 8 := by
    have h := Real.exp_nat_mul (8/5 : ℝ) 5
    have h_eq : ((5 : ℕ) : ℝ) * (8/5 : ℝ) = 8 := by norm_num
    rw [h_eq] at h
    exact h.symm
  have h_exp_8_le : Real.exp 8 ≤ (5 : ℝ)^5 := h_exp_8_eq ▸ h_exp_1_8_le
  have h_exp_8_5_le : Real.exp (8/5 : ℝ) ≤ 5 := by
    have h_pow_5_le : (Real.exp (8/5 : ℝ))^5 ≤ (5 : ℝ)^5 := h_exp_8_5_pow ▸ h_exp_8_le
    have h_exp_pos : 0 ≤ Real.exp (8/5 : ℝ) := le_of_lt (Real.exp_pos _)
    have h_5_pos : (0 : ℝ) ≤ 5 := by norm_num
    exact (pow_le_pow_iff_left₀ h_exp_pos h_5_pos (by norm_num : (5 : ℕ) ≠ 0)).mp h_pow_5_le
  have h_5_le_322pi : (5 : ℝ) ≤ 32 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]
    nlinarith
  have h_exp_le_ratio : Real.exp (8/5 : ℝ) ≤ 32 / (2 * Real.pi) :=
    le_trans h_exp_8_5_le h_5_le_322pi
  have h_exp_pos : 0 < Real.exp (8/5 : ℝ) := Real.exp_pos _
  have h := Real.log_le_log h_exp_pos h_exp_le_ratio
  rwa [Real.log_exp] at h

/-- `log(36/(2π)) ≥ 5/3`. Route: `exp(5/3)^3 = exp 5 = (exp 1)^5 ≤ (11/2)^3`. -/
lemma log_36_div_2pi_ge_5_3 :
    (5 / 3 : ℝ) ≤ Real.log (36 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_1_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_exp_1_pow_lt :
      (Real.exp 1)^5 < (2.7182818286 : ℝ)^5 :=
    pow_lt_pow_left₀ h_exp_1_lt (le_of_lt h_exp_1_pos)
      (n := 5) (by norm_num)
  have h_num_pow_le : (2.7182818286 : ℝ)^5 ≤ (11 / 2 : ℝ)^3 := by norm_num
  have h_exp_1_pow_le : (Real.exp 1)^5 ≤ (11 / 2 : ℝ)^3 := by linarith
  have h_exp_5_eq : Real.exp 5 = (Real.exp 1)^5 := by
    have h := Real.exp_one_pow 5
    have h_cast : ((5 : ℕ) : ℝ) = (5 : ℝ) := by norm_num
    rw [← h_cast]; exact h.symm
  have h_exp_5_le : Real.exp 5 ≤ (11 / 2 : ℝ)^3 := by
    rw [h_exp_5_eq]; exact h_exp_1_pow_le
  have h_exp_5_3_pow : (Real.exp (5 / 3 : ℝ))^3 = Real.exp 5 := by
    have h := Real.exp_nat_mul (5 / 3 : ℝ) 3
    have h_eq : ((3 : ℕ) : ℝ) * (5 / 3 : ℝ) = 5 := by norm_num
    rw [h_eq] at h; exact h.symm
  have h_exp_5_3_le : Real.exp (5 / 3 : ℝ) ≤ 11 / 2 := by
    have h_pow : (Real.exp (5 / 3 : ℝ))^3 ≤ (11 / 2 : ℝ)^3 := by
      rw [h_exp_5_3_pow]; exact h_exp_5_le
    have h_exp_nn : 0 ≤ Real.exp (5 / 3 : ℝ) := le_of_lt (Real.exp_pos _)
    have h_112_nn : 0 ≤ (11 / 2 : ℝ) := by norm_num
    exact (pow_le_pow_iff_left₀ h_exp_nn h_112_nn
      (by norm_num : (3 : ℕ) ≠ 0)).mp h_pow
  have h_112_le_36_2pi : (11 / 2 : ℝ) ≤ 36 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]; nlinarith
  have h_exp_le_ratio :
      Real.exp (5 / 3 : ℝ) ≤ 36 / (2 * Real.pi) :=
    le_trans h_exp_5_3_le h_112_le_36_2pi
  have h_exp_pos : 0 < Real.exp (5 / 3 : ℝ) := Real.exp_pos _
  have h := Real.log_le_log h_exp_pos h_exp_le_ratio
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — Endpoint bound: `log(48/(2π)) ≥ 2`.**
Chain: `(exp 1)² ≤ 7.4` (from `exp_one_lt_d9`) and `7.4·(2π) ≤ 48` via
`π < 3.1416`. Tighter than the [80,140] chain because `8·(2π) > 48`. -/
lemma log_48_div_2pi_ge_2 :
    (2 : ℝ) ≤ Real.log (48 / (2 * Real.pi)) := by
  have h_pi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_1_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_exp_1_sq_lt : (Real.exp 1)^2 < (2.7182818286 : ℝ)^2 :=
    pow_lt_pow_left₀ h_exp_1_lt (le_of_lt h_exp_1_pos) (n := 2) (by norm_num)
  have h_27_sq_le : (2.7182818286 : ℝ)^2 ≤ 7.4 := by norm_num
  have h_exp_1_sq_le : (Real.exp 1)^2 ≤ 7.4 := by linarith
  have h_exp_2_eq : Real.exp 2 = (Real.exp 1)^2 := by
    have := Real.exp_one_pow 2
    have h_cast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [← h_cast]; exact this.symm
  have h_exp_2_le : Real.exp 2 ≤ 7.4 := h_exp_2_eq ▸ h_exp_1_sq_le
  have h_74_le : (7.4 : ℝ) ≤ 48 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]
    nlinarith
  have h_exp_2_le_ratio : Real.exp 2 ≤ 48 / (2 * Real.pi) :=
    le_trans h_exp_2_le h_74_le
  have h_exp_pos : 0 < Real.exp 2 := Real.exp_pos _
  have h := Real.log_le_log h_exp_pos h_exp_2_le_ratio
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — `log(80/(2π)) ≥ 2`.**
Squaring: `(exp 1)² < 2.7182818286² ≤ 8` (norm_num).
∴ `exp 2 ≤ 8`. Finally `8 ≤ 80/(2π)` since `8·(2π) ≤ 80`
via `π < 4`. -/
lemma log_80_div_2pi_ge_2 :
    (2 : ℝ) ≤ Real.log (80 / (2 * Real.pi)) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt_4 : Real.pi < 4 := Real.pi_lt_four
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_exp_1_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h_exp_1_pos : 0 < Real.exp 1 := Real.exp_pos _
  have h_exp_1_sq_lt : (Real.exp 1)^2 < (2.7182818286 : ℝ)^2 :=
    pow_lt_pow_left₀ h_exp_1_lt (le_of_lt h_exp_1_pos) (n := 2) (by norm_num)
  have h_27_sq_le : (2.7182818286 : ℝ)^2 ≤ 8 := by norm_num
  have h_exp_1_sq_le : (Real.exp 1)^2 ≤ 8 := by linarith
  have h_exp_2_eq : Real.exp 2 = (Real.exp 1)^2 := by
    have := Real.exp_one_pow 2
    have h_cast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [← h_cast]; exact this.symm
  have h_exp_2_le : Real.exp 2 ≤ 8 := h_exp_2_eq ▸ h_exp_1_sq_le
  have h_8_le : (8 : ℝ) ≤ 80 / (2 * Real.pi) := by
    rw [le_div_iff₀ h_2pi_pos]
    nlinarith
  have h_exp_2_le_ratio : Real.exp 2 ≤ 80 / (2 * Real.pi) :=
    le_trans h_exp_2_le h_8_le
  have h_exp_pos : 0 < Real.exp 2 := Real.exp_pos _
  have h := Real.log_le_log h_exp_pos h_exp_2_le_ratio
  rwa [Real.log_exp] at h

/-- ⭐ **PROVED — Sharper π reciprocal: `1/(2π) ≥ 7/44`.**
Via `Real.pi_lt_d4 : π < 3.1416`, hence `2π < 6.2832 < 44/7`,
hence `(7/44)·(2π) ≤ 1`. -/
lemma one_div_two_pi_ge_seven_fortyfour :
    (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  rw [le_div_iff₀ h2pi_pos]
  nlinarith

/-- ⭐ **PROVED — `1/(2π) ≥ 3/19`.**
Since `2π ≤ 6.3 ≤ 19/3`. -/
lemma one_div_two_pi_ge_three_nineteenths :
    (3 / 19 : ℝ) ≤ 1 / (2 * Real.pi) := by
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  rw [le_div_iff₀ h_2pi_pos]
  nlinarith

/-- ⭐ **PROVED — Padé bound** `2(5−π)/(5+π) ≤ log(5/π)`. -/
lemma pade_log_5_div_pi :
    2 * (5 - Real.pi) / (5 + Real.pi) ≤ Real.log (5 / Real.pi) := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_5_lt_pi : Real.pi < 5 := by linarith
  have hπ_ne : Real.pi ≠ 0 := ne_of_gt h_pi_pos
  have h_5_plus_pi_pos : (0 : ℝ) < 5 + Real.pi := by linarith
  have h_x_nn : (0 : ℝ) ≤ (5 - Real.pi) / Real.pi := by
    apply div_nonneg
    · linarith
    · exact le_of_lt h_pi_pos
  have h_one_add : 1 + (5 - Real.pi) / Real.pi = 5 / Real.pi := by
    field_simp
    ring
  have h_pade := Real.le_log_one_add_of_nonneg h_x_nn
  rw [h_one_add] at h_pade
  have h_inner_pos : (0 : ℝ) < (5 - Real.pi) / Real.pi + 2 := by positivity
  have h_inner_ne : ((5 - Real.pi) / Real.pi + 2) ≠ 0 := ne_of_gt h_inner_pos
  have h_step1 :
      2 * ((5 - Real.pi) / Real.pi)
        ≤ ((5 - Real.pi) / Real.pi + 2) * Real.log (5 / Real.pi) := by
    have h := mul_le_mul_of_nonneg_right h_pade (le_of_lt h_inner_pos)
    rw [div_mul_cancel₀ _ h_inner_ne] at h
    linarith
  have h_step2 :
      2 * (5 - Real.pi) ≤ (5 + Real.pi) * Real.log (5 / Real.pi) := by
    have h := mul_le_mul_of_nonneg_left h_step1 (le_of_lt h_pi_pos)
    have hl : Real.pi * (2 * ((5 - Real.pi) / Real.pi)) = 2 * (5 - Real.pi) := by
      field_simp
    have h_factor :
        Real.pi * ((5 - Real.pi) / Real.pi + 2) = 5 + Real.pi := by
      field_simp; ring
    have hr :
        Real.pi * (((5 - Real.pi) / Real.pi + 2) * Real.log (5 / Real.pi))
          = (5 + Real.pi) * Real.log (5 / Real.pi) := by
      rw [show Real.pi *
            (((5 - Real.pi) / Real.pi + 2) * Real.log (5 / Real.pi))
            = (Real.pi * ((5 - Real.pi) / Real.pi + 2))
                * Real.log (5 / Real.pi) from by ring,
          h_factor]
    linarith [h, hl.le, hl.symm.le, hr.le, hr.symm.le]
  have h5pπ_ne : (5 + Real.pi : ℝ) ≠ 0 := ne_of_gt h_5_plus_pi_pos
  rw [div_le_iff₀ h_5_plus_pi_pos]
  linarith [h_step2]

/-- ⭐ **PROVED — rational `74/163 ≤ 2(5−π)/(5+π)`** from `π ≤ 3.15`. -/
lemma pade_rational_lb_at_5_div_pi :
    (74 / 163 : ℝ) ≤ 2 * (5 - Real.pi) / (5 + Real.pi) := by
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_5_plus_pi_pos : (0 : ℝ) < 5 + Real.pi := by linarith
  rw [le_div_iff₀ h_5_plus_pi_pos]
  linarith

/-- ⭐ **PROVED — `log(5/π) ≥ 74/163`.** -/
lemma log_5_div_pi_ge_74_div_163 :
    (74 / 163 : ℝ) ≤ Real.log (5 / Real.pi) :=
  le_trans pade_rational_lb_at_5_div_pi pade_log_5_div_pi

/-- 🌟🌟 **PROVED — FTC for the one-sided Cauchy kernel.**
`∫_T^X y / ((u - a)² + y²) du = arctan((X - a)/y) − arctan((T - a)/y)`. -/
lemma integral_cauchy_one_side_eq_arctan_sub
    (a T X : ℝ) {y : ℝ} (hy : y ≠ 0) :
    (∫ u in T..X, y / ((u - a) ^ 2 + y ^ 2))
      = Real.arctan ((X - a) / y) - Real.arctan ((T - a) / y) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _
    exact hasDerivAt_arctan_shift_div a hy u
  · -- The integrand is continuous, hence interval-integrable
    have h_cont : Continuous (fun u : ℝ => y / ((u - a) ^ 2 + y ^ 2)) := by
      refine continuous_const.div ?_ ?_
      · exact ((continuous_id.sub continuous_const).pow 2).add continuous_const
      · intro u
        have h1 : (0 : ℝ) ≤ (u - a) ^ 2 := sq_nonneg _
        have h2 : (0 : ℝ) < y ^ 2 := by positivity
        linarith
    exact h_cont.intervalIntegrable T X

/-- 🌟🌟🌟 **PROVED — CLV-shaped rational lower bound on `arctan (y/A)`.**
For `A > 0`, `y ≥ 0`:

  `y · A / (A² + y²) ≤ arctan (y / A)`.

Direct application of `div_one_add_sq_le_arctan` at `s := y/A` after
the algebraic identity `(y/A)/(1+(y/A)²) = yA/(A²+y²)`. -/
lemma arctan_div_lower_rational
    {A y : ℝ} (hA : 0 < A) (hy : 0 ≤ y) :
    y * A / (A ^ 2 + y ^ 2) ≤ Real.arctan (y / A) := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  have h_div_nn : 0 ≤ y / A := div_nonneg hy (le_of_lt hA)
  have h_base : (y / A) / (1 + (y / A) ^ 2) ≤ Real.arctan (y / A) :=
    div_one_add_sq_le_arctan h_div_nn
  have h_alg : (y / A) / (1 + (y / A) ^ 2) = y * A / (A ^ 2 + y ^ 2) := by
    have hA_sq_pos : 0 < A ^ 2 := by positivity
    have hAy_sq_pos : 0 < A ^ 2 + y ^ 2 := by positivity
    field_simp
  rw [h_alg] at h_base
  exact h_base

end OverflowResidueRH
