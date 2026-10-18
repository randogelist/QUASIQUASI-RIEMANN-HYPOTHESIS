/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Nonvanishing
import RiemannHypothesis.GammaCancellation.TextbookXi
import RiemannHypothesis.Xi.FunctionalEquation
import RiemannHypothesis.Xi.SignTargets

/-!
# The zero set of the entire Riemann xi function

This module proves, without an auxiliary correspondence hypothesis, that the
zeros of `entireRiemannXi` are exactly Mathlib's nontrivial zeros of
`riemannZeta`.  It then identifies Mathlib's `RiemannHypothesis` with the
statement that every zero of `entireRiemannXi` lies on the critical line.

The points at which the raw Gamma-factor formula is totalized require some
care.  At `s = 0` the entire xi function is `1 / 2`.  At a negative even
integer, its functional equation moves the value to the zero-free half-plane
`1 < re s`.  Thus no cancellation fact is smuggled into the zero
correspondence as an assumption.
-/

namespace OverflowResidueRH

open Complex
open Filter Topology

/-- The pointwise predicate used by Mathlib's definition of the Riemann
hypothesis: a zeta zero which is neither a trivial negative-even zero nor the
totalized value at `s = 1`. -/
def IsMathlibNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

/-- At a regular point, the entire xi definition agrees directly with the
completed-zeta formula. -/
theorem entireRiemannXi_eq_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireRiemannXi s =
      (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  unfold entireRiemannXi
  rw [completedRiemannZeta_eq]
  exact (xi_completedZeta_correction_algebra hs0 hs1).symm

/-- Away from the totalized point at zero, completed zeta is the Deligne
Gamma factor times Riemann zeta whenever that Gamma factor is nonzero. -/
theorem completedRiemannZeta_eq_GammaReal_mul_riemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hz := riemannZeta_def_of_ne_zero (s := s) hs0
  rw [hz]
  field_simp [hG]

/-- At regular points, vanishing of the entire xi function is equivalent to
vanishing of Riemann zeta. -/
theorem entireRiemannXi_eq_zero_iff_riemannZeta_eq_zero
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    entireRiemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [entireRiemannXi_eq_completedRiemannZeta hs0 hs1,
      completedRiemannZeta_eq_GammaReal_mul_riemannZeta hs0 hG]
  simp [hs0, sub_ne_zero.mpr hs1, hG]

/-- The entire xi function is nonzero at `s = 0`. -/
theorem entireRiemannXi_zero_ne :
    entireRiemannXi 0 ≠ 0 := by
  norm_num [entireRiemannXi]

/-- The entire xi function is nonzero at `s = 1`. -/
theorem entireRiemannXi_one_ne :
    entireRiemannXi 1 ≠ 0 := by
  norm_num [entireRiemannXi]

/-- A nontrivial zeta zero is not a pullback of a Gamma pole. -/
theorem half_not_mem_gammaPoleSet_of_nontrivial_zeta_zero
    {s : ℂ} (hzeta : riemannZeta s = 0)
    (hnot_trivial : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    s / 2 ∉ gammaPoleSet := by
  rintro ⟨n, hn⟩
  by_cases hn0 : n = 0
  · subst n
    have hs0 : s = 0 := by
      linear_combination 2 * hn
    subst s
    norm_num [riemannZeta_zero] at hzeta
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    apply hnot_trivial
    refine ⟨m, ?_⟩
    have hn' : s / 2 = -((m : ℂ) + 1) := by
      simpa using hn
    linear_combination 2 * hn'

/-- Every Mathlib-nontrivial zeta zero is a zero of the entire xi function. -/
theorem entireRiemannXi_eq_zero_of_nontrivial_zeta_zero
    {s : ℂ} (hzeta : riemannZeta s = 0)
    (hnot_trivial : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (hs1 : s ≠ 1) :
    entireRiemannXi s = 0 := by
  have hsPole : s / 2 ∉ gammaPoleSet :=
    half_not_mem_gammaPoleSet_of_nontrivial_zeta_zero hzeta hnot_trivial
  rw [← completedXiRawEntireXiOffPolePointwiseFormula.pointwise_eq s hs1 hsPole]
  simp [completedXiFunction, hzeta]

/-- The entire xi function has no zeros in the half-plane `1 < re s`. -/
theorem entireRiemannXi_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    entireRiemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hsPole : s / 2 ∉ gammaPoleSet := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    exact hsPole ⟨n, hn⟩
  have hraw : completedXiFunction s ≠ 0 := by
    unfold completedXiFunction
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero (by norm_num) hs0)
            (sub_ne_zero.mpr hs1))
          (Complex.exp_ne_zero _))
        hgamma)
      (riemannZeta_ne_zero_of_one_lt_re hs)
  rw [completedXiRawEntireXiOffPolePointwiseFormula.pointwise_eq s hs1 hsPole] at hraw
  exact hraw

/-- Negative-even trivial zeta zeros are not zeros of the entire xi function.
The functional equation moves them to the zero-free half-plane. -/
theorem entireRiemannXi_neg_two_mul_nat_add_one_ne_zero (n : ℕ) :
    entireRiemannXi (-2 * ((n : ℂ) + 1)) ≠ 0 := by
  rw [← entireRiemannXi_one_sub]
  apply entireRiemannXi_ne_zero_of_one_lt_re
  norm_num [Complex.sub_re, Complex.mul_re, Complex.add_re]
  exact_mod_cast Nat.zero_lt_succ n

/-- A zero of the entire xi function cannot occur at a pullback of a Gamma
pole.  Negative even points are moved by the functional equation to
`re s > 1`; the remaining pole-pullback point is `s = 0`, where xi is
`1 / 2`. -/
theorem half_not_mem_gammaPoleSet_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    s / 2 ∉ gammaPoleSet := by
  rintro ⟨n, hn⟩
  by_cases hn0 : n = 0
  · subst n
    have hs0 : s = 0 := by
      linear_combination 2 * hn
    subst s
    norm_num [entireRiemannXi] at hxi
  · have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hre := congrArg Complex.re hn
    simp at hre
    have hright : 1 < (1 - s).re := by
      rw [Complex.sub_re]
      norm_num
      nlinarith
    apply entireRiemannXi_ne_zero_of_one_lt_re hright
    rw [entireRiemannXi_one_sub]
    exact hxi

/-- A zero of the entire xi function is not the totalized point `s = 1`. -/
theorem ne_one_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    s ≠ 1 := by
  intro hs
  subst s
  norm_num [entireRiemannXi] at hxi

/-- Every zero of the entire xi function is a zero of Mathlib's Riemann zeta
function. -/
theorem riemannZeta_eq_zero_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    riemannZeta s = 0 := by
  have hsPole : s / 2 ∉ gammaPoleSet :=
    half_not_mem_gammaPoleSet_of_entireRiemannXi_zero hxi
  have hs0 : s ≠ 0 := ne_zero_of_half_not_gammaPole hsPole
  have hs1 : s ≠ 1 := ne_one_of_entireRiemannXi_zero hxi
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    exact hsPole ⟨n, hn⟩
  have hraw : completedXiFunction s = 0 := by
    rw [completedXiRawEntireXiOffPolePointwiseFormula.pointwise_eq s hs1 hsPole]
    exact hxi
  rw [completedXiFunction] at hraw
  have hcoefficient :
      (1 / 2 : ℂ) * s * (s - 1)
          * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
          * Complex.Gamma (s / 2) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) hs0)
          (sub_ne_zero.mpr hs1))
        (Complex.exp_ne_zero _))
      hgamma
  exact (mul_eq_zero.mp hraw).resolve_left hcoefficient

/-- A zero of the entire xi function is not a trivial negative-even zeta
zero. -/
theorem not_trivial_of_entireRiemannXi_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
  intro htrivial
  obtain ⟨n, hn⟩ := htrivial
  apply half_not_mem_gammaPoleSet_of_entireRiemannXi_zero hxi
  refine ⟨n + 1, ?_⟩
  rw [hn]
  push_cast
  ring

/-- The zeros of the entire xi function are exactly the nontrivial zeros in
Mathlib's formulation of the Riemann hypothesis. -/
theorem entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero
    {s : ℂ} :
    entireRiemannXi s = 0 ↔ IsMathlibNontrivialZetaZero s := by
  constructor
  · intro hxi
    exact ⟨riemannZeta_eq_zero_of_entireRiemannXi_zero hxi,
      not_trivial_of_entireRiemannXi_zero hxi,
      ne_one_of_entireRiemannXi_zero hxi⟩
  · rintro ⟨hzeta, hnot_trivial, hs1⟩
    exact entireRiemannXi_eq_zero_of_nontrivial_zeta_zero hzeta hnot_trivial hs1

/-- Every zero of the entire xi function lies strictly inside the critical
strip.  The right boundary follows from zeta nonvanishing on `re s ≥ 1`; the
left boundary follows by reflecting with the xi functional equation. -/
theorem entireRiemannXi_zero_re_mem_Ioo
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    s.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hzeta : riemannZeta s = 0 :=
    riemannZeta_eq_zero_of_entireRiemannXi_zero hxi
  have hre_lt_one : s.re < 1 := by
    apply lt_of_not_ge
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta
  have hreflected : entireRiemannXi (1 - s) = 0 := by
    rw [entireRiemannXi_one_sub]
    exact hxi
  have hzeta_reflected : riemannZeta (1 - s) = 0 :=
    riemannZeta_eq_zero_of_entireRiemannXi_zero hreflected
  have hreflected_lt_one : (1 - s).re < 1 := by
    apply lt_of_not_ge
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta_reflected
  have hre_pos : 0 < s.re := by
    rw [Complex.sub_re] at hreflected_lt_one
    norm_num at hreflected_lt_one ⊢
    linarith
  exact ⟨hre_pos, hre_lt_one⟩

/-- Consequently, the imaginary coordinate of every centered-pullback zero
lies strictly between `-1/2` and `1/2`.  This is the geometric input that
compares pullback norm shells with zeta-height slabs. -/
theorem entireXiPullback_zero_im_abs_lt_half
    {z : ℂ} (hz : EntireXiPullback z = 0) :
    |z.im| < (1 / 2 : ℝ) := by
  have hstrip := entireRiemannXi_zero_re_mem_Ioo
    (s := (1 / 2 : ℂ) + Complex.I * z) hz
  rw [critical_shift_re] at hstrip
  rw [abs_lt]
  constructor <;> linarith [hstrip.1, hstrip.2]

/-! ### Exact analytic multiplicity across the xi--zeta bridge -/

/-- The local analytic unit relating `entireRiemannXi` to `riemannZeta`
inside the critical strip. -/
private noncomputable def entireRiemannXiZetaUnit (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s

/-- Deligne's real Gamma factor is analytic wherever its argument has
positive real part.  We obtain this without a separate pole-set calculation:
its reciprocal is entire, and is nonzero on this half-plane. -/
private theorem analyticAt_GammaReal_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  have hinv : AnalyticAt ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hinv_ne : (Complex.Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  have hdouble := hinv.inv hinv_ne
  change AnalyticAt ℂ (fun w : ℂ => ((Complex.Gammaℝ w)⁻¹)⁻¹) s at hdouble
  simpa only [inv_inv] using hdouble

private theorem analyticAt_entireRiemannXiZetaUnit_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ entireRiemannXiZetaUnit s := by
  have hpoly :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * w * (w - 1)) s := by
    fun_prop
  exact hpoly.mul (analyticAt_GammaReal_of_re_pos hs)

/-- At a zero of `entireRiemannXi`, the entire xi function agrees in a full
neighborhood with a nonvanishing analytic unit times `riemannZeta`. -/
private theorem
    entireRiemannXi_eventuallyEq_zetaUnit_mul_riemannZeta_at_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    entireRiemannXi =ᶠ[𝓝 s] entireRiemannXiZetaUnit * riemannZeta := by
  have hstrip := entireRiemannXi_zero_re_mem_Ioo hxi
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hstrip
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hstrip
  have hpos : ∀ᶠ w : ℂ in 𝓝 s, 0 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hstrip.1
  filter_upwards [hpos, eventually_ne_nhds hs0, eventually_ne_nhds hs1]
    with w hwpos hw0 hw1
  change entireRiemannXi w =
    entireRiemannXiZetaUnit w * riemannZeta w
  rw [entireRiemannXi_eq_completedRiemannZeta hw0 hw1,
    completedRiemannZeta_eq_GammaReal_mul_riemannZeta hw0
      (Complex.Gammaℝ_ne_zero_of_re_pos hwpos)]
  unfold entireRiemannXiZetaUnit
  ring

/-- At every zero of `entireRiemannXi`, its analytic order is exactly the
analytic order of `riemannZeta`.  Thus the xi--zeta zero correspondence
preserves multiplicity, rather than merely preserving the zero set. -/
theorem entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    analyticOrderAt entireRiemannXi s =
      analyticOrderAt riemannZeta s := by
  have hstrip := entireRiemannXi_zero_re_mem_Ioo hxi
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hstrip
  have hunit : AnalyticAt ℂ entireRiemannXiZetaUnit s :=
    analyticAt_entireRiemannXiZetaUnit_of_re_pos hstrip.1
  have hunit_ne : entireRiemannXiZetaUnit s ≠ 0 := by
    unfold entireRiemannXiZetaUnit
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      norm_num at hstrip
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) hs0)
        (sub_ne_zero.mpr hs1))
      (Complex.Gammaℝ_ne_zero_of_re_pos hstrip.1)
  have hzeta : AnalyticAt ℂ riemannZeta s := by
    exact analyticOn_riemannZeta s (by simpa using hs1)
  rw [analyticOrderAt_congr
    (entireRiemannXi_eventuallyEq_zetaUnit_mul_riemannZeta_at_zero hxi)]
  rw [analyticOrderAt_mul hunit hzeta,
    hunit.analyticOrderAt_eq_zero.mpr hunit_ne, zero_add]

/-- Natural-number form of exact xi--zeta multiplicity preservation. -/
theorem entireRiemannXi_analyticOrderNatAt_eq_riemannZeta_of_zero
    {s : ℂ} (hxi : entireRiemannXi s = 0) :
    analyticOrderNatAt entireRiemannXi s =
      analyticOrderNatAt riemannZeta s :=
  congrArg ENat.toNat
    (entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero hxi)

/-- Exact analytic multiplicity preservation, stated directly for Mathlib's
predicate of a nontrivial zeta zero. -/
theorem entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_mathlib_nontrivial_zero
    {s : ℂ} (hs : IsMathlibNontrivialZetaZero s) :
    analyticOrderAt entireRiemannXi s =
      analyticOrderAt riemannZeta s :=
  entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero
    (entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr hs)

/-- Natural-number multiplicity preservation, stated directly for Mathlib's
predicate of a nontrivial zeta zero. -/
theorem entireRiemannXi_analyticOrderNatAt_eq_riemannZeta_of_mathlib_nontrivial_zero
    {s : ℂ} (hs : IsMathlibNontrivialZetaZero s) :
    analyticOrderNatAt entireRiemannXi s =
      analyticOrderNatAt riemannZeta s :=
  entireRiemannXi_analyticOrderNatAt_eq_riemannZeta_of_zero
    (entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr hs)

/-- Mathlib's Riemann hypothesis is exactly the assertion that all zeros of
the entire xi function lie on the critical line. -/
theorem riemannHypothesis_iff_entireRiemannXi_zeros_on_critical_line :
    RiemannHypothesis ↔
      ∀ s : ℂ, entireRiemannXi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hRH s hxi
    exact hRH s
      (riemannZeta_eq_zero_of_entireRiemannXi_zero hxi)
      (not_trivial_of_entireRiemannXi_zero hxi)
      (ne_one_of_entireRiemannXi_zero hxi)
  · intro hxi s hzeta hnot_trivial hs1
    exact hxi s
      (entireRiemannXi_eq_zero_of_nontrivial_zeta_zero
        hzeta hnot_trivial hs1)

/-- Pulling the entire xi function back along `s = 1 / 2 + I * z`
turns Mathlib's Riemann hypothesis into the literal real-rootedness of
`EntireXiPullback`. -/
theorem riemannHypothesis_iff_entireXiPullback_zeros_real :
    RiemannHypothesis ↔
      ∀ z : ℂ, EntireXiPullback z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_entireRiemannXi_zeros_on_critical_line]
  constructor
  · intro hcritical z hz
    have hline := hcritical
      ((1 / 2 : ℂ) + Complex.I * z) hz
    rw [critical_shift_re] at hline
    linarith
  · intro hreal s hs
    let z : ℂ := -Complex.I * (s - (1 / 2 : ℂ))
    have hshift : (1 / 2 : ℂ) + Complex.I * z = s := by
      dsimp [z]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hz : EntireXiPullback z = 0 := by
      unfold EntireXiPullback
      rw [hshift]
      exact hs
    have him : z.im = 0 := hreal z hz
    have hre := critical_shift_re z
    rw [hshift, him] at hre
    simpa using hre

/-- The repository's remaining left-half-plane logarithmic-derivative sign
condition implies Mathlib's literal `RiemannHypothesis`.  All regularity,
Schwarz-reflection, nontriviality, exceptional-point, and zero-correspondence
obligations have been discharged; `h_sign` is the only hypothesis. -/
theorem riemannHypothesis_of_entireXi_leftHalfPlaneLogDerivSign
    (h_sign : EntireXi.leftHalfPlaneLogDerivSign) :
    RiemannHypothesis :=
  riemannHypothesis_iff_entireXiPullback_zeros_real.mpr
    (EntireXiPullback.zeros_real_of_sign h_sign)

end OverflowResidueRH
