/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import RiemannHypothesis.ComplexAnalysis.AntiHerglotz

/-!
# Pole-probe arithmetic and the local pole-decomposition engine

The "engine room" of the overflow-residue argument. Near an upper-half-plane
pole `ρ`, probing at `ρ − ε·I` rotates the residue `m / (z − ρ)` onto the
positive imaginary axis with magnitude `m/ε`, which diverges as `ε ↓ 0` and
defeats any bounded background. This forces `PositiveUpperImaginaryEscape`,
contradicting the anti-Herglotz sign law.

Knows nothing about polynomials, entire functions, or Xi — only the abstract
probe arithmetic, the `LocalLogDerivPoleDecomposition` data, and reusable
continuity → probe-bound / probe-nonzero helpers.

## Main results

* `positiveEscape_of_localLogDerivPole` — the analytic engine: a
  local pole decomposition forces positive upper-imaginary escape.
* `complex_local_pole_decomposition_{simple,double,triple,general}` — algebraic
  log-derivative identities at a root of given multiplicity.
* `continuousAt_implies_probe_bounded`, `probe_ne_pole`,
  `continuousAt_implies_probe_nonzero` — generic probe-mechanics helpers.
-/

namespace OverflowResidueRH

open Complex

-- =====================================================================
-- §4. Probe arithmetic at an upper pole  (CXXIX)
-- =====================================================================
-- The `m / (−ε·I)` blow-up family. A real residue `m` divided by `−ε·I`
-- rotates onto the positive imaginary axis with magnitude `m/ε`, which
-- diverges as `ε ↓ 0` and defeats any bounded background.

/-- **PROVED — escape value `m/ε` exceeds any bounded `K` once `ε < m/K`.**
This is the analytic clincher: a bounded background cannot kill the
`m/ε` divergence near an upper pole. -/
theorem escape_exceeds_bounded_background
    (m K eps : ℝ) (_hm : m > 0) (hK : K > 0) (hε : 0 < eps)
    (hsmall : eps < m / K) :
    m / eps > K := by
  rw [gt_iff_lt, lt_div_iff₀ hε]
  have hKne : K ≠ 0 := ne_of_gt hK
  have : K * eps < K * (m / K) := by
    apply mul_lt_mul_of_pos_left hsmall hK
  have hKK : K * (m / K) = m := by
    field_simp
  rw [hKK] at this
  linarith

/-- **PROVED — escape strictly positive: `m/ε − K > 0` once `ε < m/K`.** -/
theorem residual_escape_positive
    (m K eps : ℝ) (hm : m > 0) (hK : K > 0) (hε : 0 < eps)
    (hsmall : eps < m / K) :
    m / eps - K > 0 := by
  have h := escape_exceeds_bounded_background m K eps hm hK hε hsmall
  linarith

/-- **PROVED — probe subtraction: `(a + (b−ε)·I) − (a + b·I) = −ε·I`.** -/
theorem complex_probe_subtraction (a b eps : ℝ) :
    ((a : ℂ) + (b - eps) * Complex.I) - ((a : ℂ) + b * Complex.I)
      = -eps * Complex.I := by
  ring

/-- **PROVED — `Im(m / (−ε·I)) = m / ε`** for `ε ≠ 0`.
The central probe identity: at the probe just below an upper pole, the
residue contribution `m / (z_ε − ρ)` has imaginary part `m/ε`. -/
theorem im_principalPart_at_lowerProbe (m eps : ℝ) (hε : eps ≠ 0) :
    ((m : ℂ) / ((-eps : ℂ) * Complex.I)).im = m / eps := by
  have hε2 : eps^2 ≠ 0 := pow_ne_zero 2 hε
  rw [Complex.div_im]
  rw [Complex.normSq_mul, Complex.normSq_I, mul_one]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.normSq_neg, Complex.normSq_ofReal,
    mul_zero, mul_one, sub_zero, add_zero, neg_zero]
  field_simp
  ring

/-- **PROVED — `Im(m / (−ε·I)) > 0` when `m, ε > 0`.** -/
theorem im_principalPart_at_lowerProbe_pos
    (m eps : ℝ) (hm : 0 < m) (hε : 0 < eps) :
    0 < ((m : ℂ) / ((-eps : ℂ) * Complex.I)).im := by
  rw [im_principalPart_at_lowerProbe m eps (ne_of_gt hε)]
  exact div_pos hm hε

/-- **PROVED — escape exceeds bounded background (complex form):**
if `m, ε > 0` and `ε < m/K` and `|Im B| ≤ K` then
`Im(m / (−ε·I) + B) > 0`. -/
theorem upper_pole_escape_with_background_complex
    (m eps K : ℝ) (B : ℂ)
    (hm : 0 < m) (hK : 0 < K) (hε : 0 < eps)
    (hsmall : eps < m / K)
    (hB : |B.im| ≤ K) :
    0 < (((m : ℂ) / ((-eps : ℂ) * Complex.I)) + B).im := by
  rw [Complex.add_im, im_principalPart_at_lowerProbe m eps (ne_of_gt hε)]
  have hescape : m / eps > K :=
    escape_exceeds_bounded_background m K eps hm hK hε hsmall
  have hB_lb : -K ≤ B.im := neg_le_of_abs_le hB
  linarith

/-- **PROVED — escape via probe formula combined: at `z_ε` for upper pole
`ρ`, the residue + background imaginary part is positive.** -/
theorem polynomial_upper_root_forces_escape_complex
    (a b eps m K : ℝ) (B : ℂ)
    (_hb : 0 < b) (hm : 0 < m) (hK : 0 < K)
    (hε : 0 < eps) (_hε_lt_b : eps < b)
    (hsmall : eps < m / K)
    (hB : |B.im| ≤ K) :
    0 < (((m : ℂ) /
      (((a : ℂ) + (b - eps) * Complex.I) - ((a : ℂ) + b * Complex.I))) + B).im := by
  rw [complex_probe_subtraction]
  exact upper_pole_escape_with_background_complex m eps K B hm hK hε hsmall hB

-- =====================================================================
-- §5. Local pole decomposition engine  (CXXXI Layers 1–2)
-- =====================================================================

/-- **Local-decomposition data for a log-derivative response at an upper
pole.** The pole is at `ρ` with multiplicity `m`. The response equals
`m/(z − ρ) + background z` on the probe segment `ρ − ε·I` for
`0 < ε < ε0`. The background's imaginary part is uniformly bounded by `K`
on that segment. -/
structure LocalLogDerivPoleDecomposition (R : ℂ → ℂ) (ρ : ℂ) where
  m : ℕ
  hm_pos : 0 < m
  background : ℂ → ℂ
  ε0 : ℝ
  hε0 : 0 < ε0
  hε0_lt : ε0 < ρ.im
  K : ℝ
  hK_pos : 0 < K
  decomp_at_probe :
    ∀ ε : ℝ, 0 < ε → ε < ε0 →
      R (ρ - (ε : ℂ) * Complex.I) =
        ((m : ℝ) : ℂ) / ((ρ - (ε : ℂ) * Complex.I) - ρ) +
        background (ρ - (ε : ℂ) * Complex.I)
  background_bounded :
    ∀ ε : ℝ, 0 < ε → ε < ε0 →
      |(background (ρ - (ε : ℂ) * Complex.I)).im| ≤ K

/-- **Explicit lower-probe witness.** A local logarithmic-derivative pole
decomposition does more than give an unspecified upper-half-plane escape:
there is a positive vertical displacement `ε`, still inside the certified
decomposition interval, for which the point `ρ - ε I` remains in the upper
half-plane and the response has strictly positive imaginary part.

This strengthened form records the geometry used by the pole argument and is
therefore useful for concrete counterexample/diagnostic constructions. -/
theorem exists_lowerProbe_escape_of_localLogDerivPole
    {R : ℂ → ℂ} {ρ : ℂ}
    (D : LocalLogDerivPoleDecomposition R ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.ε0 ∧
      0 < (ρ - (ε : ℂ) * Complex.I).im ∧
      0 < (R (ρ - (ε : ℂ) * Complex.I)).im := by
  have hm_real_pos : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.hm_pos
  have hmK_pos : 0 < (D.m : ℝ) / D.K := div_pos hm_real_pos D.hK_pos
  let ε : ℝ := min (D.ε0 / 2) ((D.m : ℝ) / D.K / 2)
  have hε_pos : 0 < ε := by
    refine lt_min ?_ ?_
    · linarith [D.hε0]
    · linarith
  have hε_lt_ε0 : ε < D.ε0 := by
    refine lt_of_le_of_lt (min_le_left _ _) ?_
    linarith [D.hε0]
  have hε_lt_mK : ε < (D.m : ℝ) / D.K := by
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    linarith
  refine ⟨ε, hε_pos, hε_lt_ε0, ?_, ?_⟩
  · have h_im : (ρ - (ε : ℂ) * Complex.I).im = ρ.im - ε := by
      simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im]
    rw [h_im]
    linarith [D.hε0_lt]
  · rw [D.decomp_at_probe ε hε_pos hε_lt_ε0]
    have hsub : (ρ - (ε : ℂ) * Complex.I) - ρ = -(ε : ℂ) * Complex.I := by
      ring
    rw [hsub]
    have hB := D.background_bounded ε hε_pos hε_lt_ε0
    exact upper_pole_escape_with_background_complex
      (D.m : ℝ) ε D.K (D.background (ρ - (ε : ℂ) * Complex.I))
      hm_real_pos D.hK_pos hε_pos hε_lt_mK hB

/-- **PROVED — THE TRUE ANALYTIC ENGINE.** A local pole decomposition at
an upper pole forces a positive upper-imaginary escape. Pick
`ε := min(ε₀/2, m/(2K))`, apply `upper_pole_escape_with_background_complex`. -/
theorem positiveEscape_of_localLogDerivPole
    {R : ℂ → ℂ} {ρ : ℂ}
    (D : LocalLogDerivPoleDecomposition R ρ) :
    PositiveUpperImaginaryEscape R := by
  obtain ⟨ε, _hε, _hεD, hupper, hescape⟩ :=
    exists_lowerProbe_escape_of_localLogDerivPole D
  exact ⟨ρ - (ε : ℂ) * Complex.I, hupper, hescape⟩

/-- **PROVED — complex local-pole decomposition for a simple root.**
If `p` factors locally as `p = (X − ρ) · q` at `z` with `q(z) ≠ 0`
and `z ≠ ρ`, then `(p value)' / (p value) = 1/(z−ρ) + q'/q`.
Stated as an algebraic identity on values. -/
theorem complex_local_pole_decomposition_simple_root
    (z ρ q dq : ℂ) (hρ : z ≠ ρ) (hq : q ≠ 0) :
    (q + (z - ρ) * dq) / ((z - ρ) * q)
      = 1 / (z - ρ) + dq / q := by
  have hρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hρ
  field_simp

/-- **PROVED — complex local-pole decomposition for multiplicity 2.**
If `p = (X − ρ)² · q`, then at `z ≠ ρ`, `q(z) ≠ 0`:
`p'(z)/p(z) = 2/(z−ρ) + q'(z)/q(z)`. -/
theorem complex_local_pole_decomposition_double_root
    (z ρ q dq : ℂ) (hρ : z ≠ ρ) (hq : q ≠ 0) :
    (2 * (z - ρ) * q + (z - ρ)^2 * dq) / ((z - ρ)^2 * q)
      = 2 / (z - ρ) + dq / q := by
  have hρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hρ
  have hρ'2 : (z - ρ)^2 ≠ 0 := pow_ne_zero 2 hρ'
  field_simp

/-- **PROVED — complex local-pole decomposition for multiplicity 3.** -/
theorem complex_local_pole_decomposition_triple_root
    (z ρ q dq : ℂ) (hρ : z ≠ ρ) (hq : q ≠ 0) :
    (3 * (z - ρ)^2 * q + (z - ρ)^3 * dq) / ((z - ρ)^3 * q)
      = 3 / (z - ρ) + dq / q := by
  have hρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hρ
  have hρ'3 : (z - ρ)^3 ≠ 0 := pow_ne_zero 3 hρ'
  field_simp

/-- **PROVED — local-pole decomposition for general multiplicity `m = k+1`
in the form `(p value)' / (p value) = m/(z−ρ) + q'/q`** when supplied
with the standard derivative expansion `m·(z−ρ)^(m−1)·q + (z−ρ)^m·q'`. -/
theorem complex_local_pole_decomposition_general
    (z ρ q dq : ℂ) (k : ℕ) (hρ : z ≠ ρ) (hq : q ≠ 0) :
    (((k + 1 : ℕ) : ℂ) * (z - ρ)^k * q + (z - ρ)^(k + 1) * dq)
      / ((z - ρ)^(k + 1) * q)
      = ((k + 1 : ℕ) : ℂ) / (z - ρ) + dq / q := by
  have hρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hρ
  have hρ'k : (z - ρ)^k ≠ 0 := pow_ne_zero k hρ'
  have hρ'sk : (z - ρ)^(k + 1) ≠ 0 := pow_ne_zero (k + 1) hρ'
  rw [pow_succ]
  field_simp

-- =====================================================================
-- §6. Reusable continuity → probe helpers
-- =====================================================================
-- Generic probe-mechanics lemmas, used by both the polynomial and the
-- entire-function discharges. They know nothing about the specific target.

/-- **Continuity ⟹ probe boundedness.** A function continuous
at `ρ` is uniformly bounded (in imaginary part) along the probe segment
`ρ − ε·I` for `0 < ε < ε0`. Reusable for both polynomial and xi targets:
pick metric `δ` for radius 1, take `ε0 = min(δ/2, ρ.im/2)`, `K = ‖B ρ‖ + 1`,
close via triangle inequality. -/
theorem continuousAt_implies_probe_bounded
    {B : ℂ → ℂ} {ρ : ℂ}
    (hB : ContinuousAt B ρ)
    (hupper : 0 < ρ.im) :
    ∃ K : ℝ, 0 < K ∧
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < ρ.im ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 →
        |(B (ρ - (ε : ℂ) * Complex.I)).im| ≤ K := by
  rw [Metric.continuousAt_iff] at hB
  obtain ⟨δ, hδ_pos, hδ⟩ := hB 1 zero_lt_one
  refine ⟨‖B ρ‖ + 1, by positivity,
          min (δ/2) (ρ.im / 2), ?_, ?_, ?_⟩
  · refine lt_min (by linarith) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  intro ε hε_pos hε_lt
  have hε_lt_δ : ε < δ := by
    have : ε < δ / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    linarith
  set z : ℂ := ρ - (ε : ℂ) * Complex.I with hz_def
  have hzρ : z - ρ = -(ε : ℂ) * Complex.I := by
    change ρ - (ε : ℂ) * Complex.I - ρ = -(ε : ℂ) * Complex.I
    ring
  have hnorm : ‖z - ρ‖ = ε := by
    rw [hzρ, norm_mul, norm_neg, Complex.norm_I, mul_one]
    change ‖((ε : ℝ) : ℂ)‖ = ε
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos hε_pos
  have hdist : dist z ρ < δ := by
    rw [dist_eq_norm, hnorm]; exact hε_lt_δ
  have h_dist_B : dist (B z) (B ρ) < 1 := hδ hdist
  rw [dist_eq_norm] at h_dist_B
  have h_im : |(B z).im| ≤ ‖B z‖ := Complex.abs_im_le_norm (B z)
  have h_tri : ‖B z‖ ≤ ‖B z - B ρ‖ + ‖B ρ‖ := by
    have h_eq : B z = (B z - B ρ) + B ρ := by ring
    nth_rewrite 1 [h_eq]
    exact norm_add_le (B z - B ρ) (B ρ)
  linarith

/-- **PROVED — probe never coincides with the pole when `ε > 0`.**
The imaginary parts differ by exactly `ε`. -/
theorem probe_ne_pole (ρ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ρ - (ε : ℂ) * Complex.I ≠ ρ := by
  intro h
  have him_diff : (ρ - (ε : ℂ) * Complex.I).im = ρ.im := by rw [h]
  have him_calc : (ρ - (ε : ℂ) * Complex.I).im = ρ.im - ε := by
    simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re,
          Complex.ofReal_re, Complex.ofReal_im]
  rw [him_calc] at him_diff
  linarith

/-- **PROVED — continuous-at-ρ + nonzero-at-ρ ⟹ nonzero on probe.**
Triangle bound: `‖f(z)‖ > ‖f ρ‖/2` on a small enough probe segment. -/
theorem continuousAt_implies_probe_nonzero
    {f : ℂ → ℂ} {ρ : ℂ}
    (hf : ContinuousAt f ρ)
    (hfρ : f ρ ≠ 0)
    (hupper : 0 < ρ.im) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < ρ.im ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 →
        f (ρ - (ε : ℂ) * Complex.I) ≠ 0 := by
  rw [Metric.continuousAt_iff] at hf
  have h_pos : 0 < ‖f ρ‖ := norm_pos_iff.mpr hfρ
  obtain ⟨δ, hδ_pos, hδ⟩ := hf (‖f ρ‖ / 2) (by linarith)
  refine ⟨min (δ/2) (ρ.im / 2), ?_, ?_, ?_⟩
  · refine lt_min (by linarith) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  intro ε hε_pos hε_lt
  have hε_lt_δ : ε < δ := by
    have : ε < δ / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    linarith
  set z : ℂ := ρ - (ε : ℂ) * Complex.I
  have hzρ : z - ρ = -(ε : ℂ) * Complex.I := by
    change ρ - (ε : ℂ) * Complex.I - ρ = -(ε : ℂ) * Complex.I
    ring
  have hnorm : ‖z - ρ‖ = ε := by
    rw [hzρ, norm_mul, norm_neg, Complex.norm_I, mul_one]
    change ‖((ε : ℝ) : ℂ)‖ = ε
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos hε_pos
  have hdist : dist z ρ < δ := by
    rw [dist_eq_norm, hnorm]; exact hε_lt_δ
  have h_dist : dist (f z) (f ρ) < ‖f ρ‖ / 2 := hδ hdist
  rw [dist_eq_norm] at h_dist
  intro hfz
  rw [hfz] at h_dist
  simp at h_dist
  linarith

end OverflowResidueRH
