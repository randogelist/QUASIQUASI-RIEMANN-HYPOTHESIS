/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.Push
import RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import RiemannHypothesis.ComplexAnalysis.LogDerivative
import RiemannHypothesis.ComplexAnalysis.PoleProbe
import RiemannHypothesis.RealZeros.Engine

/-!
# Entire-function logarithmic-derivative criteria

This module derives the local pole decomposition from analytic zero
factorization and proves a natural global theorem: a nontrivial entire
function satisfying the upper-half-plane logarithmic-derivative sign has no
upper-half-plane zeros, and Schwarz reflection then makes every zero real.

## Main results

* `entire_function_no_upper_zeros_of_analytic_nontrivial` — the natural
  one-sided global theorem.
* `entire_function_roots_real_of_analytic_nontrivial` — the Schwarz-symmetric
  real-zero theorem.
* `logDeriv_of_eventual_factorization` — the local logarithmic-derivative
  decomposition derived from analytic factorization.
-/

namespace OverflowResidueRH

open Complex Filter Topology

-- =====================================================================
-- Neighborhood → probe helpers
-- =====================================================================

/-- If `P` holds on a neighborhood of `ρ`, then `P` holds
on the entire probe segment `ρ − ε·I` for all small enough `ε`. Useful
for both polynomial and xi-pullback discharges. -/
theorem eventually_nhds_implies_probe_eventually
    {P : ℂ → Prop} {ρ : ℂ}
    (hP : ∀ᶠ z in 𝓝 ρ, P z)
    (hupper : 0 < ρ.im) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < ρ.im ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 →
        P (ρ - (ε : ℂ) * Complex.I) := by
  rw [Metric.eventually_nhds_iff] at hP
  obtain ⟨δ, hδ_pos, hδ⟩ := hP
  refine ⟨min (δ/2) (ρ.im / 2), ?_, ?_, ?_⟩
  · refine lt_min (by linarith) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  intro ε hε_pos hε_lt
  apply hδ
  rw [dist_eq_norm,
      show ρ - (ε : ℂ) * Complex.I - ρ = -((ε : ℂ) * Complex.I) by ring,
      norm_neg, norm_mul, Complex.norm_I, mul_one]
  change ‖((ε : ℝ) : ℂ)‖ < δ
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
  have hε_lt_half : ε < δ / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  linarith

/-- Strengthening of `eventually_nhds_implies_probe_eventually`: not only does
`P` hold *at* the probe `ρ − ε·I`, it holds on an entire neighbourhood of
it. This is the form needed when feeding the data into Mathlib lemmas of
the shape `Filter.EventuallyEq.deriv_eq`, which require eventual equality
*at* the differentiation point. -/
theorem eventually_nhds_implies_probe_eventually_nhds
    {P : ℂ → Prop} {ρ : ℂ}
    (hP : ∀ᶠ z in 𝓝 ρ, P z)
    (hupper : 0 < ρ.im) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < ρ.im ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ᶠ z in 𝓝 (ρ - (ε : ℂ) * Complex.I), P z := by
  rw [Metric.eventually_nhds_iff] at hP
  obtain ⟨δ, hδ_pos, hδ⟩ := hP
  refine ⟨min (δ / 2) (ρ.im / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  intro ε hε_pos hε_lt
  have hε_lt_half : ε < δ / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ / 4, by linarith, ?_⟩
  intro w hw
  apply hδ
  have hprobe_dist : dist (ρ - (ε : ℂ) * Complex.I) ρ = ε := by
    rw [dist_eq_norm,
        show ρ - (ε : ℂ) * Complex.I - ρ = -((ε : ℂ) * Complex.I) by ring,
        norm_neg, norm_mul, Complex.norm_I, mul_one]
    change ‖((ε : ℝ) : ℂ)‖ = ε
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
  calc dist w ρ
        ≤ dist w (ρ - (ε : ℂ) * Complex.I) +
            dist (ρ - (ε : ℂ) * Complex.I) ρ := dist_triangle _ _ _
    _ < δ / 4 + ε := by linarith
    _ < δ := by linarith

-- =====================================================================
-- Entire-function generalization template
-- =====================================================================

/-- **Entire-function local pole-decomposition hypothesis.** At every
upper-half-plane zero of `F`, the local pole structure is good enough
to supply a `LocalLogDerivPoleDecomposition` for `Λ[F]`. This is the
entire-function analogue of the polynomial `PolynomialPoleWitnessHypothesis`.

Constructively building an inhabitant of this structure from the natural
factorization data `∀ᶠ z in 𝓝 ρ, F z = (z − ρ)^m · g z` (with `g(ρ) ≠ 0`
and `g` analytic) is handled by `LocalAnalyticZeroFactorization` below. -/
structure EntireLocalPoleDecompositionHypothesis (F : ℂ → ℂ) : Prop where
  decomp_at_each_upper_zero :
    ∀ ρ : ℂ, F ρ = 0 → 0 < ρ.im →
      Nonempty (LocalLogDerivPoleDecomposition (logDerivativeResponse F) ρ)

/-- The entire-function pole-decomposition hypothesis implies the abstract
`LogDerivPoleWitnessLaw`. -/
theorem entireLocalPoleDecomposition_gives_poleWitness
    {F : ℂ → ℂ} (H : EntireLocalPoleDecompositionHypothesis F) :
    LogDerivPoleWitnessLaw F (logDerivativeResponse F) where
  upper_zero_forces_escape := by
    intro ρ hzero hupper
    obtain ⟨D⟩ := H.decomp_at_each_upper_zero ρ hzero hupper
    exact positiveEscape_of_localLogDerivPole D

/-- For any function `F`
satisfying the entire-function local pole-decomposition hypothesis,
anti-Herglotz log-derivative plus Schwarz symmetry ⟹ every zero of `F`
is real.

Inhabiting `EntireLocalPoleDecompositionHypothesis F` for any analytic
`F` reduces to the local factorization at each zero plus the bounded
background — both standard complex analysis, handled by the reusable
`continuousAt_implies_probe_bounded`. -/
theorem entire_function_roots_real_of_logDeriv_antiHerglotz_and_conjSymm
    (F : ℂ → ℂ)
    (H : EntireLocalPoleDecompositionHypothesis F)
    (hanti : AntiHerglotzUHP (logDerivativeResponse F))
    (hsym : ∀ z : ℂ, F (star z) = star (F z)) :
    ∀ ρ : ℂ, F ρ = 0 → ρ.im = 0 :=
  realZeros_of_antiHerglotz_logDerivative
    (entireLocalPoleDecomposition_gives_poleWitness H) hanti hsym

-- =====================================================================
-- Local analytic factorization to pole decomposition
-- =====================================================================

/-- **Local analytic factorization data at a zero.** Records the standard
analytic factorization
   F z = (z − ρ)^m · g z   eventually near ρ,
with `m ≥ 1`, `g` nonvanishing at `ρ`, `g` differentiable on a neighbourhood
of `ρ`, and the log-derivative background `g'/g` continuous at `ρ`.

This is the natural complex-analytic input that any function holomorphic
on a neighbourhood of an isolated zero of multiplicity `m` provides. -/
structure LocalAnalyticZeroFactorization (F : ℂ → ℂ) (ρ : ℂ) where
  m : ℕ
  hm_pos : 0 < m
  g : ℂ → ℂ
  hgρ : g ρ ≠ 0
  hg_diff_nhds : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z
  hcont_background : ContinuousAt (fun z => deriv g z / g z) ρ
  hfactor : ∀ᶠ z in 𝓝 ρ, F z = (z - ρ) ^ m * g z

/-- Logarithmic derivative of an eventual factorization.
If `F` agrees on a neighbourhood of `z` with `(· − ρ)^m · g` (with `m ≥ 1`,
`z ≠ ρ`, `g z ≠ 0`, `g` differentiable at `z`), then the algebraic identity
transfers to the actual log-derivative response:

  `Λ[F](z)  =  m / (z − ρ)  +  g'(z) / g(z)`.

Mechanism: `Filter.EventuallyEq.deriv_eq` rewrites `deriv F z` to the
derivative of the factored form; the product/power rules compute the
latter; `complex_local_pole_decomposition_general` reduces the
resulting algebraic ratio. -/
theorem logDeriv_of_eventual_factorization
    {F g : ℂ → ℂ} {ρ z : ℂ} {m : ℕ}
    (hm : 0 < m)
    (hzρ : z ≠ ρ)
    (hgz : g z ≠ 0)
    (hF_eq : F =ᶠ[𝓝 z] fun w => (w - ρ) ^ m * g w)
    (hgdiff : DifferentiableAt ℂ g z) :
    logDerivativeResponse F z =
      ((m : ℕ) : ℂ) / (z - ρ) + deriv g z / g z := by
  -- Rewrite m as k+1 to mesh with the §5 general lemma.
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- Value of F at z.
  have hF_val : F z = (z - ρ) ^ (k + 1) * g z := hF_eq.eq_of_nhds
  -- Derivative of (·−ρ)^(k+1) at z, then product with g.
  have h_sub : HasDerivAt (fun w : ℂ => w - ρ) 1 z :=
    (hasDerivAt_id z).sub_const ρ
  have h_pow : HasDerivAt (fun w : ℂ => (w - ρ) ^ (k + 1))
                (((k + 1 : ℕ) : ℂ) * (z - ρ) ^ k) z := by
    have h := h_sub.pow (k + 1)
    simp only [Nat.add_sub_cancel, mul_one] at h
    convert h using 2
    all_goals rfl
  have hg : HasDerivAt g (deriv g z) z := hgdiff.hasDerivAt
  have h_prod : HasDerivAt (fun w : ℂ => (w - ρ) ^ (k + 1) * g w)
                  (((k + 1 : ℕ) : ℂ) * (z - ρ) ^ k * g z +
                    (z - ρ) ^ (k + 1) * deriv g z) z := h_pow.mul hg
  have h_F_deriv : deriv F z =
      ((k + 1 : ℕ) : ℂ) * (z - ρ) ^ k * g z +
        (z - ρ) ^ (k + 1) * deriv g z := by
    rw [hF_eq.deriv_eq]; exact h_prod.deriv
  unfold logDerivativeResponse
  rw [h_F_deriv, hF_val]
  exact complex_local_pole_decomposition_general z ρ (g z) (deriv g z) k hzρ hgz

/-- **PROVED — building `LocalLogDerivPoleDecomposition` from a
`LocalAnalyticZeroFactorization`.** The entire-function analogue of
§9's `localLogDerivPoleDecomposition_of_polynomial_factor`. Mechanism:

  • probe ≠ pole (`probe_ne_pole`);
  • probe → background bounded (`continuousAt_implies_probe_bounded`
    applied to `H.hcont_background`);
  • probe → `g` nonzero (`continuousAt_implies_probe_nonzero` from the
    continuity of `g` at `ρ` together with `H.hgρ`);
  • probe → differentiable in a *neighbourhood* of the probe
    (`eventually_nhds_implies_probe_eventually` applied to
    `H.hg_diff_nhds`);
  • eventual factorization propagated to a nhd of the probe
    (`eventually_nhds_implies_probe_eventually_nhds`);
  • value-form bridge `logDeriv_of_eventual_factorization`.
-/
noncomputable def localAnalyticZeroFactorization_gives_LocalLogDerivPoleDecomposition
    {F : ℂ → ℂ} {ρ : ℂ}
    (hupper : 0 < ρ.im)
    (H : LocalAnalyticZeroFactorization F ρ) :
    LocalLogDerivPoleDecomposition (logDerivativeResponse F) ρ :=
  let hcontG : ContinuousAt H.g ρ := H.hg_diff_nhds.self_of_nhds.continuousAt
  let hnzG := continuousAt_implies_probe_nonzero hcontG H.hgρ hupper
  let hbg := continuousAt_implies_probe_bounded H.hcont_background hupper
  let hev_fac_nhd :=
    eventually_nhds_implies_probe_eventually_nhds H.hfactor hupper
  let hev_diff :=
    eventually_nhds_implies_probe_eventually H.hg_diff_nhds hupper
  let K := hbg.choose
  let hK := hbg.choose_spec
  let ε0B := hK.2.choose
  let hε0B := hK.2.choose_spec
  let ε0Q := hnzG.choose
  let hε0Q := hnzG.choose_spec
  let ε0F := hev_fac_nhd.choose
  let hε0F := hev_fac_nhd.choose_spec
  let ε0D := hev_diff.choose
  let hε0D := hev_diff.choose_spec
  let ε0 : ℝ := min (min ε0B ε0Q) (min ε0F ε0D)
  { m := H.m
    hm_pos := H.hm_pos
    background := fun z => deriv H.g z / H.g z
    ε0 := ε0
    hε0 :=
      lt_min (lt_min hε0B.1 hε0Q.1) (lt_min hε0F.1 hε0D.1)
    hε0_lt :=
      lt_of_le_of_lt
        (le_trans (min_le_left _ _) (min_le_left _ _)) hε0B.2.1
    K := K
    hK_pos := hK.1
    decomp_at_probe := fun ε hε_pos hε_lt => by
      have hε_lt_B : ε < ε0B :=
        lt_of_lt_of_le hε_lt
          (le_trans (min_le_left _ _) (min_le_left _ _))
      have hε_lt_Q : ε < ε0Q :=
        lt_of_lt_of_le hε_lt
          (le_trans (min_le_left _ _) (min_le_right _ _))
      have hε_lt_F : ε < ε0F :=
        lt_of_lt_of_le hε_lt
          (le_trans (min_le_right _ _) (min_le_left _ _))
      have hε_lt_D : ε < ε0D :=
        lt_of_lt_of_le hε_lt
          (le_trans (min_le_right _ _) (min_le_right _ _))
      have hzρ : ρ - (ε : ℂ) * Complex.I ≠ ρ := probe_ne_pole ρ ε hε_pos
      have hgz : H.g (ρ - (ε : ℂ) * Complex.I) ≠ 0 :=
        hε0Q.2.2 ε hε_pos hε_lt_Q
      have hF_eq_nhds :
          F =ᶠ[𝓝 (ρ - (ε : ℂ) * Complex.I)]
            fun w => (w - ρ) ^ H.m * H.g w :=
        hε0F.2.2 ε hε_pos hε_lt_F
      have hdiff_at_probe :
          DifferentiableAt ℂ H.g (ρ - (ε : ℂ) * Complex.I) :=
        hε0D.2.2 ε hε_pos hε_lt_D
      have h := logDeriv_of_eventual_factorization
                  H.hm_pos hzρ hgz hF_eq_nhds hdiff_at_probe
      -- Reconcile `((m : ℕ) : ℂ)` (from the lemma) with `((m : ℝ) : ℂ)`
      -- (from the structure field).
      rw [h]
      push_cast
      rfl
    background_bounded := fun ε hε_pos hε_lt => by
      have hε_lt_B : ε < ε0B :=
        lt_of_lt_of_le hε_lt
          (le_trans (min_le_left _ _) (min_le_left _ _))
      exact hε0B.2.2 ε hε_pos hε_lt_B }

/-- **Entire-function zero-factorization hypothesis.** Every upper-half-plane
zero of `F` admits a `LocalAnalyticZeroFactorization`. The natural shape of
the data any function holomorphic on the upper half-plane (with isolated
zeros) provides. -/
structure EntireZeroFactorizationHypothesis (F : ℂ → ℂ) : Prop where
  factor_at_each_upper_zero :
    ∀ ρ : ℂ, F ρ = 0 → 0 < ρ.im →
      Nonempty (LocalAnalyticZeroFactorization F ρ)

/-- ⭐ **PROVED — analytic factorization hypothesis ⟹ §10 pole-decomposition
hypothesis.** Direct composition with the bridge above. After this, the
§10 capstone `entire_function_roots_real_of_logDeriv_antiHerglotz_and_conjSymm`
is one step away from being hypothesis-free for any `F` supplying a
`LocalAnalyticZeroFactorization` at each upper-half-plane zero. -/
theorem entireZeroFactorization_gives_EntireLocalPoleDecompositionHypothesis
    {F : ℂ → ℂ}
    (H : EntireZeroFactorizationHypothesis F) :
    EntireLocalPoleDecompositionHypothesis F where
  decomp_at_each_upper_zero ρ hzero hupper := by
    obtain ⟨HF⟩ := H.factor_at_each_upper_zero ρ hzero hupper
    exact ⟨localAnalyticZeroFactorization_gives_LocalLogDerivPoleDecomposition
      hupper HF⟩

/-- ⭐ **PROVED — ENTIRE-FUNCTION TEMPLATE, ANALYTIC-INPUT FORM.**
The §10 capstone, with the abstract pole-decomposition hypothesis replaced
by the natural analytic factorization hypothesis. -/
theorem entire_function_roots_real_of_analytic_factor_antiHerglotz_and_conjSymm
    (F : ℂ → ℂ)
    (H : EntireZeroFactorizationHypothesis F)
    (hanti : AntiHerglotzUHP (logDerivativeResponse F))
    (hsym : ∀ z : ℂ, F (star z) = star (F z)) :
    ∀ ρ : ℂ, F ρ = 0 → ρ.im = 0 :=
  entire_function_roots_real_of_logDeriv_antiHerglotz_and_conjSymm F
    (entireZeroFactorization_gives_EntireLocalPoleDecompositionHypothesis H)
    hanti hsym

-- =====================================================================
-- §16.4. Analytic zeros yield a local factorization (Mathlib discharge)
-- =====================================================================
-- Mathlib's analyticity machinery — `AnalyticAt`, isolated zeros, and
-- `HasFPowerSeriesAt` — discharges the local factorization
-- `F z = (z − ρ)^m · g z` with `g ρ ≠ 0` at any non-degenerate zero of an
-- analytic function. The §10-bis pipeline already carries
-- `LocalAnalyticZeroFactorization → LocalLogDerivPoleDecomposition` and
-- `EntireZeroFactorizationHypothesis → EntireLocalPoleDecompositionHypothesis`.
-- The Prop-field structure below isolates exactly what the Mathlib discharge
-- owes: "every analytic non-degenerate zero admits a
-- `LocalAnalyticZeroFactorization`".

/-- **Analytic-zero non-degeneracy.** `F` is analytic at `ρ` and is
not eventually zero near `ρ`. By Mathlib's isolated-zeros dichotomy this
is exactly the hypothesis under which a positive-order vanishing is
well-defined. -/
structure AnalyticZeroNonDegenerate (F : ℂ → ℂ) (ρ : ℂ) : Prop where
  isAnalytic : AnalyticAt ℂ F ρ
  not_eventually_zero : ¬ (∀ᶠ z in 𝓝 ρ, F z = 0)

/-- **Promise: every analytic non-degenerate zero admits a local
factorization.** For any `F` analytic at `ρ` with `F ρ = 0` and `F` not
locally identically zero, there exist `m > 0` and an analytic `g` with
`g ρ ≠ 0` and `F z = (z − ρ)^m · g z` near `ρ`. Isolated here as a `Prop`
for discharge against `Mathlib.Analysis.Analytic.IsolatedZeros`. -/
def AnalyticZeroAdmitsFactorization (F : ℂ → ℂ) (ρ : ℂ) : Prop :=
  AnalyticZeroNonDegenerate F ρ →
  F ρ = 0 →
  Nonempty (LocalAnalyticZeroFactorization F ρ)

/-- **Global form: every zero of `F` admits the factorization.** -/
def EntireAnalyticZerosAdmitFactorization (F : ℂ → ℂ) : Prop :=
  ∀ ρ : ℂ, AnalyticZeroAdmitsFactorization F ρ

/-- **Upper-half-plane non-degenerate zero data for `F`.** At every
upper-half-plane zero of `F`, the function is analytic and not locally
identically zero. Automatic for any non-identically-zero analytic
function on a connected open set containing the UHP. -/
def EntireZerosNonDegenerate (F : ℂ → ℂ) : Prop :=
  ∀ ρ : ℂ, F ρ = 0 → 0 < ρ.im → AnalyticZeroNonDegenerate F ρ

/-- Analytic factorization plus nondegeneracy gives the entire-function
zero-factorization hypothesis. -/
theorem entireZeroFactorization_of_analytic
    {F : ℂ → ℂ}
    (h_admits : EntireAnalyticZerosAdmitFactorization F)
    (h_nondeg : EntireZerosNonDegenerate F) :
    EntireZeroFactorizationHypothesis F where
  factor_at_each_upper_zero ρ hzero hupper :=
    h_admits ρ (h_nondeg ρ hzero hupper) hzero

/-- Analytic factorization and nondegenerate upper-half-plane zeros give the
entire-function pole-decomposition hypothesis. -/
theorem entireLocalPoleDecomposition_of_analytic
    {F : ℂ → ℂ}
    (h_admits : EntireAnalyticZerosAdmitFactorization F)
    (h_nondeg : EntireZerosNonDegenerate F) :
    EntireLocalPoleDecompositionHypothesis F :=
  entireZeroFactorization_gives_EntireLocalPoleDecompositionHypothesis
    (entireZeroFactorization_of_analytic h_admits h_nondeg)

/-- The sign condition, Schwarz reflection, analyticity, and
upper-half-plane zero nondegeneracy imply that all zeros are real. The
entire-function template has the
pole-decomposition hypothesis discharged from the natural analytic inputs. -/
theorem entire_function_roots_real_of_analytic_inputs
    (F : ℂ → ℂ)
    (h_admits : EntireAnalyticZerosAdmitFactorization F)
    (h_nondeg : EntireZerosNonDegenerate F)
    (hanti : AntiHerglotzUHP (logDerivativeResponse F))
    (hsym : ∀ z : ℂ, F (star z) = star (F z)) :
    ∀ ρ : ℂ, F ρ = 0 → ρ.im = 0 :=
  entire_function_roots_real_of_logDeriv_antiHerglotz_and_conjSymm F
    (entireLocalPoleDecomposition_of_analytic h_admits h_nondeg)
    hanti hsym

-- =====================================================================
-- §16.4-A. Mathlib discharge of the analytic factorization promise
-- =====================================================================
-- `AnalyticZeroAdmitsFactorization F ρ` is the isolated-zero content of
-- complex analysis: every analytic non-degenerate zero admits the local
-- factorization `F z = (z − ρ)^m · g z` with `g ρ ≠ 0`. Mathlib's
-- `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` supplies this
-- directly, reducing `AnalyticZeroAdmitsFactorization` to a theorem.

/-- Mathlib discharge of `AnalyticZeroAdmitsFactorization`.
Given any `F : ℂ → ℂ` analytic and non-degenerate at `ρ` with `F ρ = 0`,
Mathlib's isolated-zeros machinery extracts a positive multiplicity `m`
and an analytic non-vanishing remainder `g`. -/
theorem analytic_zero_admits_factorization
    (F : ℂ → ℂ) (ρ : ℂ) :
    AnalyticZeroAdmitsFactorization F ρ := by
  intro hND hzero
  obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hND.isAnalytic).mpr
      hND.not_eventually_zero
  -- Show `n > 0` from `F ρ = 0` and `g ρ ≠ 0`.
  have hm_pos : 0 < n := by
    by_contra hcon
    push Not at hcon
    have hn0 : n = 0 := Nat.le_zero.mp hcon
    subst hn0
    have heq : F ρ = (ρ - ρ) ^ 0 • g ρ := hg_eq.self_of_nhds
    simp only [pow_zero, one_smul] at heq
    rw [hzero] at heq
    exact hg_ne heq.symm
  -- Convert `•` to `*` (canonical ℂ-action).
  have hfactor : ∀ᶠ z in 𝓝 ρ, F z = (z - ρ) ^ n * g z := by
    filter_upwards [hg_eq] with z hz
    rw [hz, smul_eq_mul]
  -- `g` is differentiable in a neighborhood of `ρ`.
  have hg_diff_nhds : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z := by
    filter_upwards [hg_an.eventually_analyticAt] with z hz
    exact hz.differentiableAt
  -- `deriv g / g` is continuous at `ρ`.
  have hcont_background : ContinuousAt (fun z => deriv g z / g z) ρ :=
    hg_an.deriv.continuousAt.div hg_an.continuousAt hg_ne
  exact ⟨{ m := n
           hm_pos := hm_pos
           g := g
           hgρ := hg_ne
           hg_diff_nhds := hg_diff_nhds
           hcont_background := hcont_background
           hfactor := hfactor }⟩

/-- Every `F : ℂ → ℂ`
automatically inhabits `EntireAnalyticZerosAdmitFactorization`. -/
theorem entireAnalyticZerosAdmitFactorization_holds
    (F : ℂ → ℂ) :
    EntireAnalyticZerosAdmitFactorization F :=
  fun ρ => analytic_zero_admits_factorization F ρ

/-- With the Mathlib factorization theorem in hand, the `h_admits` hypothesis
is automatic; the remaining inputs
are non-degeneracy of the UHP zeros, anti-Herglotz of `Λ[F]`, and Schwarz
reflection. -/
theorem entire_function_roots_real_of_analytic_nondeg
    (F : ℂ → ℂ)
    (h_nondeg : EntireZerosNonDegenerate F)
    (hanti : AntiHerglotzUHP (logDerivativeResponse F))
    (hsym : ∀ z : ℂ, F (star z) = star (F z)) :
    ∀ ρ : ℂ, F ρ = 0 → ρ.im = 0 :=
  entire_function_roots_real_of_analytic_inputs F
    (entireAnalyticZerosAdmitFactorization_holds F) h_nondeg hanti hsym

/-- A globally analytic function that is nonzero somewhere has no locally
identically-zero germ. Consequently, every zero is nondegenerate in the sense
needed by the local factorization argument.

This is the natural global discharge of `EntireZerosNonDegenerate`: the
identity theorem replaces the project-specific nondegeneracy package. -/
theorem entireZerosNonDegenerate_of_analyticOnNhd_univ
    {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (h_nontrivial : ∃ z : ℂ, F z ≠ 0) :
    EntireZerosNonDegenerate F := by
  intro ρ _hzero _hupper
  refine ⟨hF ρ (Set.mem_univ ρ), ?_⟩
  intro hlocal
  obtain ⟨w, hw⟩ := h_nontrivial
  apply hw
  have hpre : IsPreconnected (Set.univ : Set ℂ) := isPreconnected_univ
  have hF_eq_zero : F =ᶠ[𝓝 ρ] 0 := by
    filter_upwards [hlocal] with z hz
    simpa using hz
  have hzero_on : Set.EqOn F 0 Set.univ :=
    hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hpre (Set.mem_univ ρ) hF_eq_zero
  simpa using hzero_on (Set.mem_univ w)

/-- A nontrivial entire function whose logarithmic derivative has
nonpositive imaginary part away from its zeros has no zero in the open upper
half-plane.

The sign assumption is stated only where `F z ≠ 0`; this avoids relying on
Lean's totalized value for division by zero. -/
theorem entire_function_no_upper_zeros_of_analytic_nontrivial
    (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (h_nontrivial : ∃ z : ℂ, F z ≠ 0)
    (h_sign : ∀ z : ℂ, 0 < z.im → F z ≠ 0 →
      (logDerivativeResponse F z).im ≤ 0) :
    ∀ z : ℂ, 0 < z.im → F z ≠ 0 := by
  have h_nondeg : EntireZerosNonDegenerate F :=
    entireZerosNonDegenerate_of_analyticOnNhd_univ hF h_nontrivial
  have h_local : EntireLocalPoleDecompositionHypothesis F :=
    entireLocalPoleDecomposition_of_analytic
      (entireAnalyticZerosAdmitFactorization_holds F) h_nondeg
  exact antiHerglotz_forbids_upper_zeros
    (entireLocalPoleDecomposition_gives_poleWitness h_local)
    ((antiHerglotz_iff_antiHerglotz_away_from_zeros F).2 h_sign)

/-- A nontrivial entire function with Schwarz reflection and a nonpositive
upper-half-plane logarithmic-derivative sign has only real zeros.

This theorem exposes only standard analytic hypotheses. Local zero
factorization and the pole witness are discharged internally. -/
theorem entire_function_roots_real_of_analytic_nontrivial
    (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (h_nontrivial : ∃ z : ℂ, F z ≠ 0)
    (h_sign : ∀ z : ℂ, 0 < z.im → F z ≠ 0 →
      (logDerivativeResponse F z).im ≤ 0)
    (h_schwarz : ∀ z : ℂ, F (star z) = star (F z)) :
    ∀ ρ : ℂ, F ρ = 0 → ρ.im = 0 :=
  entire_function_roots_real_of_analytic_nondeg F
    (entireZerosNonDegenerate_of_analyticOnNhd_univ hF h_nontrivial)
    ((antiHerglotz_iff_antiHerglotz_away_from_zeros F).2 h_sign)
    h_schwarz

end OverflowResidueRH
