/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import RiemannHypothesis.ComplexAnalysis.LogDerivative

/-!
# ZeroCounting.SmoothMainTerm

The Riemann–von Mangoldt smooth main term for the zero-counting function and its
density, together with the abstract density-tail model skeletons that the concrete
analytic objects inhabit.

For the zero count `N(u) := # {γ : ζ-zero with 0 < Im γ ≤ u}`, the leading-order
smooth approximation is

  `N₀(u) = (u/(2π))·log(u/(2π)) − u/(2π) + 7/8`, density `ρ(u) = N₀'(u) = (1/(2π))·log(u/(2π))`.

We prove the two facts needed downstream: nonnegativity of `ρ` on `[2π, ∞)` and the
derivative identity `deriv N₀ = ρ`.

## Main declarations

* `zeroDensityRho`, `smoothZeroCountingN0` — density and smooth main term.
* `zeroDensityRho_nonneg_of_ge_two_pi` — `ρ ≥ 0` on `[2π, ∞)`.
* `deriv_smoothZeroCountingN0` — `deriv N₀ u = ρ u` for `u > 0`.
* `ZeroCountingDensityTailModel`, `SmoothDensityPairedTail` — abstract model skeletons.
-/

namespace OverflowResidueRH

/-- **Zero-counting density-tail model skeleton.** Names the analytic
data for the density model `M_{N,M}(z)` without yet formalizing the
integral. Fields:

* `threshold` — `T` (typically `T = 2π` or larger), beyond which the
  density `ρ` is nonneg;
* `gamma` — known real-axis zero ordinates `γ_n`;
* `rho` — the density function (the natural choice is
  `ρ(u) = (1 / (2π)) · log (u / (2π))`, which is `≥ 0` for `u ≥ 2π`);
* `rho_nonneg_on_tail` — `ρ ≥ 0` on `[threshold, ∞)`;
* `model` — the actual model `M_{N,M}` (cloud + smooth density tail);
* `modelAnti` — the model is anti-Herglotz (follows for the positive
  density tail since `K_u(z)` has nonpositive imaginary part for
  `Im z > 0` and `ρ ≥ 0` on the relevant range).

This is the analytic skeleton the next phase fills in. -/
structure ZeroCountingDensityTailModel where
  threshold : ℝ
  gamma : ℕ → ℝ
  rho : ℝ → ℝ
  rho_nonneg_on_tail : ∀ u : ℝ, threshold ≤ u → 0 ≤ rho u
  model : ℂ → ℂ
  modelAnti : AntiHerglotzUHP model

-- ---------------------------------------------------------------------
-- Concrete zero-counting density model
-- ---------------------------------------------------------------------
-- The Riemann–von Mangoldt smooth main term for the zero-counting
-- function `N(u) := # {γ : ζ-zero with 0 < Im γ ≤ u}` is
--   `N_0(u) = (u/(2π)) · log(u/(2π)) − u/(2π) + 7/8`,
-- with density `ρ(u) = N_0'(u) = (1/(2π)) · log(u/(2π))`.
-- This section makes those concrete and proves the two facts needed
-- to inhabit the `rho` / `rho_nonneg_on_tail` / model fields of
-- `ZeroCountingDensityTailModel`: nonnegativity of `ρ` on `[2π, ∞)`,
-- and the derivative identity `deriv N_0 = ρ`.

/-- **Riemann–von Mangoldt zero density** `ρ(u) := (1/(2π)) · log(u/(2π))`.
This is the natural smooth density for the zero count `N(u)` of nontrivial
ζ-zeros in the critical strip up to height `u`. -/
noncomputable def zeroDensityRho (u : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))

/-- **Smooth zero count** `N_0(u) := (u/(2π))·log(u/(2π)) − u/(2π) + 7/8`,
the leading-order Riemann–von Mangoldt approximation to the zero-counting
function. Its derivative is `zeroDensityRho`. -/
noncomputable def smoothZeroCountingN0 (u : ℝ) : ℝ :=
  (u / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
    - u / (2 * Real.pi)
    + 7 / 8

/-- **PROVED — `ρ(u) ≥ 0` for `u ≥ 2π`.** Because `u/(2π) ≥ 1`, so
`log(u/(2π)) ≥ 0`, and `1/(2π) > 0`. -/
theorem zeroDensityRho_nonneg_of_ge_two_pi
    {u : ℝ} (hu : 2 * Real.pi ≤ u) :
    0 ≤ zeroDensityRho u := by
  unfold zeroDensityRho
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_ratio_ge_one : (1 : ℝ) ≤ u / (2 * Real.pi) := by
    rw [le_div_iff₀ h2pi_pos]
    linarith
  have h_log_nonneg : 0 ≤ Real.log (u / (2 * Real.pi)) :=
    Real.log_nonneg h_ratio_ge_one
  have h_coef_pos : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  exact mul_nonneg (le_of_lt h_coef_pos) h_log_nonneg

/-- **PROVED — `deriv smoothZeroCountingN0 u = zeroDensityRho u` for
`u > 0`.** Calculus chase:

  `N_0(u) = (u/(2π))·log(u/(2π)) − u/(2π) + 7/8`

Derivatives:

  `deriv (u ↦ u/(2π)) u = 1/(2π)`
  `deriv (u ↦ log(u/(2π))) u = 1/u`              (chain rule, log composed with linear)
  `deriv ((u/(2π))·log(u/(2π))) u`
      `= (1/(2π))·log(u/(2π)) + (u/(2π))·(1/u)`  (product rule)
      `= (1/(2π))·log(u/(2π)) + 1/(2π)`
  `deriv N_0 u`
      `= (1/(2π))·log(u/(2π)) + 1/(2π) − 1/(2π) + 0`
      `= (1/(2π))·log(u/(2π)) = ρ(u)`.
-/
theorem deriv_smoothZeroCountingN0
    {u : ℝ} (hu : 0 < u) :
    deriv smoothZeroCountingN0 u = zeroDensityRho u := by
  unfold smoothZeroCountingN0 zeroDensityRho
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi_pos
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have hq_pos : (0 : ℝ) < u / (2 * Real.pi) := div_pos hu h2pi_pos
  have hq_ne : u / (2 * Real.pi) ≠ 0 := ne_of_gt hq_pos
  -- HasDerivAt for u ↦ u/(2π)
  have h_lin : HasDerivAt (fun u : ℝ => u / (2 * Real.pi)) (1 / (2 * Real.pi)) u := by
    simpa using (hasDerivAt_id u).div_const (2 * Real.pi)
  -- HasDerivAt for u ↦ log(u/(2π))
  have h_log_inner :
      HasDerivAt (fun u : ℝ => Real.log (u / (2 * Real.pi))) (1 / u) u := by
    have hlog := Real.hasDerivAt_log hq_ne
    have h_comp := hlog.comp u h_lin
    have h_simp : (u / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) = 1 / u := by
      field_simp
    rw [h_simp] at h_comp
    simpa [Function.comp_def] using h_comp
  -- HasDerivAt for the product
  have h_prod :
      HasDerivAt
        (fun u : ℝ => (u / (2 * Real.pi)) * Real.log (u / (2 * Real.pi)))
        ((1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
          + (u / (2 * Real.pi)) * (1 / u)) u :=
    h_lin.mul h_log_inner
  -- Subtract u/(2π)
  have h_sub :
      HasDerivAt
        (fun u : ℝ =>
          (u / (2 * Real.pi)) * Real.log (u / (2 * Real.pi)) - u / (2 * Real.pi))
        ((1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
          + (u / (2 * Real.pi)) * (1 / u) - 1 / (2 * Real.pi)) u :=
    h_prod.sub h_lin
  -- Add the constant 7/8
  have h_final :
      HasDerivAt
        (fun u : ℝ =>
          (u / (2 * Real.pi)) * Real.log (u / (2 * Real.pi)) - u / (2 * Real.pi)
            + 7 / 8)
        ((1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
          + (u / (2 * Real.pi)) * (1 / u) - 1 / (2 * Real.pi)) u :=
    h_sub.add_const (7 / 8)
  rw [h_final.deriv]
  -- Cancel `(u/(2π)) · (1/u) − 1/(2π) = 0`, leaving `(1/(2π))·log(u/(2π))`
  field_simp
  ring

/-- **Smooth-density paired tail skeleton.** Bundles a real-axis density
`ρ` (nonneg above a threshold) with its associated paired-Cauchy tail
function on the upper half-plane and a hypothesis that the tail is
anti-Herglotz. The eventual integral instantiation is

  `tail z = ∫_{threshold}^∞ pairedCauchyKernel u z · ρ(u) du`,

at which point `tailAnti` becomes a theorem (each `pairedCauchyKernel`
contribution has nonpositive imaginary part on the UHP, and `ρ ≥ 0`).
For now `tailAnti` is a hypothesis. -/
structure SmoothDensityPairedTail where
  threshold : ℝ
  rho : ℝ → ℝ
  rho_nonneg_on_tail : ∀ u : ℝ, threshold ≤ u → 0 ≤ rho u
  tail : ℂ → ℂ
  tailAnti : AntiHerglotzUHP tail

/-- **Smooth-tail rational lower bound (absolute form).** The elementary
rational lower bound for `−Im(densityTail z)` at probe `(x, y)` with cutoff `T`:
  `ρ(T) · ( y(T − |x|)/((T − |x|)² + y²) + y(T + |x|)/((T + |x|)² + y²) )`
where `ρ(T) = (1/(2π))·log(T/(2π))`. Pulled from
`arctan s ≥ s/(1 + s²)` applied to the elementary
`∫ y/((u ± x)² + y²) du = arctan(y/(T ∓ x))`. -/
noncomputable def smoothTailRationalLowerBoundAbs (x y T : ℝ) : ℝ :=
  zeroDensityRho T *
    (y * (T - |x|) / ((T - |x|)^2 + y^2)
      + y * (T + |x|) / ((T + |x|)^2 + y^2))

/-- ⭐ **PROVED — `HasDerivAt smoothZeroCountingN0 (zeroDensityRho u) u` for
`u > 0`.** The `HasDerivAt`-flavoured version of the existing
`deriv_smoothZeroCountingN0`. Needed to apply
`monotoneOn_of_deriv_nonneg`. -/
theorem hasDerivAt_smoothZeroCountingN0
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt smoothZeroCountingN0 (zeroDensityRho u) u := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi_pos
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have hq_pos : (0 : ℝ) < u / (2 * Real.pi) := div_pos hu h2pi_pos
  have hq_ne : u / (2 * Real.pi) ≠ 0 := ne_of_gt hq_pos
  have h_lin : HasDerivAt (fun u : ℝ => u / (2 * Real.pi)) (1 / (2 * Real.pi)) u := by
    simpa using (hasDerivAt_id u).div_const (2 * Real.pi)
  have h_log_inner :
      HasDerivAt (fun u : ℝ => Real.log (u / (2 * Real.pi))) (1 / u) u := by
    have hlog := Real.hasDerivAt_log hq_ne
    have h_comp := hlog.comp u h_lin
    have h_simp : (u / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) = 1 / u := by
      field_simp
    rw [h_simp] at h_comp
    simpa [Function.comp_def] using h_comp
  have h_prod := h_lin.mul h_log_inner
  have h_sub := h_prod.sub h_lin
  have h_final := h_sub.add_const (7 / 8)
  -- Match function form to smoothZeroCountingN0 and simplify derivative.
  have h_func_eq :
      (fun u : ℝ => (u / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
                    - u / (2 * Real.pi) + 7 / 8)
        = smoothZeroCountingN0 := by
    funext v; rfl
  have h_deriv_eq :
      (1 / (2 * Real.pi)) * Real.log (u / (2 * Real.pi))
        + (u / (2 * Real.pi)) * (1 / u) - 1 / (2 * Real.pi)
      = zeroDensityRho u := by
    unfold zeroDensityRho
    field_simp
    ring
  rw [← h_func_eq, ← h_deriv_eq]
  exact h_final

/-- ⭐ **PROVED — `smoothZeroCountingN0` is monotone on `[2π, ∞)`.**

Direct from `monotoneOn_of_deriv_nonneg`:
* continuity and differentiability on the interior follow from
  `hasDerivAt_smoothZeroCountingN0`;
* the derivative `zeroDensityRho u` is `≥ 0` for `u ≥ 2π`
  (`zeroDensityRho_nonneg_of_ge_two_pi`). -/
theorem smoothZeroCountingN0_monotoneOn_Ici_two_pi :
    MonotoneOn smoothZeroCountingN0 (Set.Ici (2 * Real.pi)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro x hx
    have hx_ge : 2 * Real.pi ≤ x := hx
    have hx_pos : 0 < x := lt_of_lt_of_le (by positivity) hx_ge
    exact (hasDerivAt_smoothZeroCountingN0 hx_pos).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx_2pi : 2 * Real.pi < x := hx
    have hx_pos : 0 < x := lt_trans (by positivity) hx_2pi
    exact (hasDerivAt_smoothZeroCountingN0 hx_pos).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx_2pi : 2 * Real.pi < x := hx
    have hx_pos : 0 < x := lt_trans (by positivity) hx_2pi
    rw [(hasDerivAt_smoothZeroCountingN0 hx_pos).deriv]
    exact zeroDensityRho_nonneg_of_ge_two_pi (le_of_lt hx_2pi)

/-- ⭐ **PROVED — `smoothZeroCountingN0(2π) = -1/8`.**

Direct evaluation: `N₀(2π) = 1 · log(1) − 1 + 7/8 = -1/8`. -/
theorem smoothZeroCountingN0_at_two_pi :
    smoothZeroCountingN0 (2 * Real.pi) = -(1 / 8) := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi_pos
  unfold smoothZeroCountingN0
  have h_div_one : (2 * Real.pi) / (2 * Real.pi) = 1 := div_self h2pi_ne
  rw [h_div_one, Real.log_one]
  ring

/-- ⭐ **PROVED — `smoothZeroCountingN0(10) ≤ 1/2`.**

Chain: `5/π ≥ 5/3.15 > 1.58` (since `π < 3.15`), `5/π < 2` (since
`π > 2.5`), so `log(5/π) ≤ log 2 ≤ 0.7` (Mathlib `Real.log_two_lt_d9`),
giving `N₀(10) = (5/π)·log(5/π) − 5/π + 7/8 ≤ 1.58·0.7 − 1.58 + 7/8 ≈ 0.40 ≤ 1/2`. -/
theorem smoothZeroCountingN0_at_10_le_half :
    smoothZeroCountingN0 10 ≤ 1 / 2 := by
  unfold smoothZeroCountingN0
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_pi_gt : 3.14 < Real.pi := Real.pi_gt_d2
  -- 10/(2π) = 5/π
  have h_eq : (10 : ℝ) / (2 * Real.pi) = 5 / Real.pi := by ring
  rw [h_eq]
  have h_5_pi_pos : 0 < 5 / Real.pi := by positivity
  have h_5_pi_nn : 0 ≤ 5 / Real.pi := le_of_lt h_5_pi_pos
  -- 5/π > 1.58 (from π < 3.15)
  have h_5_pi_gt : (1.58 : ℝ) < 5 / Real.pi := by
    rw [lt_div_iff₀ h_pi_pos]; linarith
  -- 5/π < 2 (from π > 5/2)
  have h_5_pi_lt_2 : 5 / Real.pi < 2 := by
    rw [div_lt_iff₀ h_pi_pos]; linarith
  -- log(5/π) ≤ log 2
  have h_log_le_log2 : Real.log (5 / Real.pi) ≤ Real.log 2 :=
    Real.log_le_log h_5_pi_pos (le_of_lt h_5_pi_lt_2)
  -- log 2 ≤ 0.7
  have h_log2_lt : Real.log 2 ≤ 0.7 := by
    have := Real.log_two_lt_d9
    linarith
  have h_log_le : Real.log (5 / Real.pi) ≤ 0.7 :=
    le_trans h_log_le_log2 h_log2_lt
  -- log(5/π) ≥ 0 since 5/π ≥ 1
  have h_5_pi_ge_1 : (1 : ℝ) ≤ 5 / Real.pi := by
    rw [le_div_iff₀ h_pi_pos]; linarith
  have h_log_nn : 0 ≤ Real.log (5 / Real.pi) := Real.log_nonneg h_5_pi_ge_1
  -- (5/π)·log(5/π) ≤ (5/π)·0.7
  have h_mul_le : (5 / Real.pi) * Real.log (5 / Real.pi)
                ≤ (5 / Real.pi) * 0.7 :=
    mul_le_mul_of_nonneg_left h_log_le h_5_pi_nn
  -- Combine: closedForm ≤ -0.3·(5/π) + 7/8 ≤ 1/2 since 0.3·(5/π) > 0.474 ≥ 3/8
  nlinarith [h_mul_le, h_5_pi_gt]

/-- ⭐ **PROVED — `smoothZeroCountingN0(14) ≤ 1/2`.**

Chain (with `q := 7/π`):
* `7/π ∈ (2.222, 2.23)` from `Real.pi_lt_d2` / `Real.pi_gt_d2`;
* tangent at `q = 2`: `log q ≤ log 2 + q/2 − 1` via
  `Real.log_le_sub_one_of_pos` applied to `q/2`;
* `log 2 ≤ 0.6932` via `Real.log_two_lt_d9`;
* `q · q ≤ q · 2.23` from `q ≤ 2.23`;
* combine: `q · log q ≤ q · 0.6932 + q · 1.115 − q = q · 0.8082`;
* `N₀(14) = q · log q − q + 7/8 ≤ −0.1918 · q + 7/8`;
* `q > 2.222 ⟹ −0.1918 · q < −0.4262`, so `N₀(14) < 0.449 ≤ 1/2`. -/
theorem smoothZeroCountingN0_at_14_le_half :
    smoothZeroCountingN0 14 ≤ 1 / 2 := by
  unfold smoothZeroCountingN0
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_pi_gt : 3.14 < Real.pi := Real.pi_gt_d2
  -- 14/(2π) = 7/π
  have h_eq : (14 : ℝ) / (2 * Real.pi) = 7 / Real.pi := by ring
  rw [h_eq]
  -- 7/π positivity and bounds
  have h_7pi_pos : 0 < 7 / Real.pi := by positivity
  have h_7pi_nn : 0 ≤ 7 / Real.pi := le_of_lt h_7pi_pos
  -- 7/π < 2.23 (from π > 3.14: 2.23 · 3.14 = 7.0022 > 7)
  have h_7pi_lt : 7 / Real.pi < 2.23 := by
    rw [div_lt_iff₀ h_pi_pos]; linarith
  -- 7/π > 2.222 (from π < 3.15: 2.222 · 3.15 = 6.9993 < 7)
  have h_7pi_gt : (2.222 : ℝ) < 7 / Real.pi := by
    rw [lt_div_iff₀ h_pi_pos]; linarith
  -- (7/π)/2 > 0 for `log_le_sub_one_of_pos`
  have h_7pi_half_pos : 0 < 7 / Real.pi / 2 := by linarith
  -- Tangent at q=2: log(q/2) ≤ q/2 - 1
  have h_log_qhalf_le : Real.log (7 / Real.pi / 2) ≤ 7 / Real.pi / 2 - 1 :=
    Real.log_le_sub_one_of_pos h_7pi_half_pos
  -- log(q/2) = log q - log 2
  have h_log_div : Real.log (7 / Real.pi / 2)
                = Real.log (7 / Real.pi) - Real.log 2 :=
    Real.log_div (ne_of_gt h_7pi_pos) (by norm_num : (2 : ℝ) ≠ 0)
  -- log q ≤ log 2 + q/2 - 1
  have h_log_q_bound :
      Real.log (7 / Real.pi) ≤ Real.log 2 + 7 / Real.pi / 2 - 1 := by
    linarith
  -- log 2 ≤ 0.6932
  have h_log2_lt : Real.log 2 ≤ 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  -- q · log q ≤ q · (log 2 + q/2 - 1) = q · log 2 + q²/2 - q
  have h_mul1 : (7 / Real.pi) * Real.log (7 / Real.pi)
              ≤ (7 / Real.pi) * (Real.log 2 + 7 / Real.pi / 2 - 1) :=
    mul_le_mul_of_nonneg_left h_log_q_bound h_7pi_nn
  -- q · log 2 ≤ q · 0.6932
  have h_mul2 : (7 / Real.pi) * Real.log 2 ≤ (7 / Real.pi) * 0.6932 :=
    mul_le_mul_of_nonneg_left h_log2_lt h_7pi_nn
  -- q · q ≤ q · 2.23
  have h_qsq : (7 / Real.pi) * (7 / Real.pi) ≤ (7 / Real.pi) * 2.23 :=
    mul_le_mul_of_nonneg_left h_7pi_lt.le h_7pi_nn
  nlinarith [h_mul1, h_mul2, h_qsq, h_7pi_lt, h_7pi_gt, h_7pi_pos]

/-- ⭐ **PROVED — `smoothZeroCountingN0(14) ≤ 9/20`** (tightening of
the `_le_half` bound). Same proof technique: tangent at
`q = 2` via `Real.log_le_sub_one_of_pos` on `q/2`. The proof
actually shows `N₀(14) ≤ −0.1918·(7/π) + 7/8 < 0.4487`, which is
`< 9/20 = 0.45` (margin ≈ 0.0013). -/
theorem smoothZeroCountingN0_at_14_le_nine_twentieth :
    smoothZeroCountingN0 14 ≤ (9 / 20 : ℝ) := by
  unfold smoothZeroCountingN0
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_pi_gt : 3.14 < Real.pi := Real.pi_gt_d2
  have h_eq : (14 : ℝ) / (2 * Real.pi) = 7 / Real.pi := by ring
  rw [h_eq]
  have h_7pi_pos : 0 < 7 / Real.pi := by positivity
  have h_7pi_nn : 0 ≤ 7 / Real.pi := le_of_lt h_7pi_pos
  have h_7pi_lt : 7 / Real.pi < 2.23 := by
    rw [div_lt_iff₀ h_pi_pos]; linarith
  have h_7pi_gt : (2.222 : ℝ) < 7 / Real.pi := by
    rw [lt_div_iff₀ h_pi_pos]; linarith
  have h_7pi_half_pos : 0 < 7 / Real.pi / 2 := by linarith
  have h_log_qhalf_le : Real.log (7 / Real.pi / 2) ≤ 7 / Real.pi / 2 - 1 :=
    Real.log_le_sub_one_of_pos h_7pi_half_pos
  have h_log_div : Real.log (7 / Real.pi / 2)
                = Real.log (7 / Real.pi) - Real.log 2 :=
    Real.log_div (ne_of_gt h_7pi_pos) (by norm_num : (2 : ℝ) ≠ 0)
  have h_log_q_bound :
      Real.log (7 / Real.pi) ≤ Real.log 2 + 7 / Real.pi / 2 - 1 := by
    linarith
  have h_log2_lt : Real.log 2 ≤ 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  have h_mul1 : (7 / Real.pi) * Real.log (7 / Real.pi)
              ≤ (7 / Real.pi) * (Real.log 2 + 7 / Real.pi / 2 - 1) :=
    mul_le_mul_of_nonneg_left h_log_q_bound h_7pi_nn
  have h_mul2 : (7 / Real.pi) * Real.log 2 ≤ (7 / Real.pi) * 0.6932 :=
    mul_le_mul_of_nonneg_left h_log2_lt h_7pi_nn
  have h_qsq : (7 / Real.pi) * (7 / Real.pi) ≤ (7 / Real.pi) * 2.23 :=
    mul_le_mul_of_nonneg_left h_7pi_lt.le h_7pi_nn
  nlinarith [h_mul1, h_mul2, h_qsq, h_7pi_lt, h_7pi_gt, h_7pi_pos]

/-- ⭐ **PROVED — `smoothZeroCountingN0(10) ≥ -1/20`** via the Padé
lower bound `Real.le_log_one_add_of_nonneg`:
`2x/(x+2) ≤ log(1+x)` with `x := (5-π)/π ≥ 0` gives
`log(5/π) ≥ 2(5-π)/(5+π)`, hence
`(5/π)·log(5/π) ≥ 10(5-π)/(π(5+π))`. Clearing denominators reduces
to `37π² − 415π + 1000 ≥ 0` on `π ∈ (3.14, 3.15)`, which holds with
margin ≈ 60. Numerically `N₀(10) ≈ 0.023 ≥ -0.05`. -/
theorem smoothZeroCountingN0_at_10_ge_neg_one_twentieth :
    -(1 / 20 : ℝ) ≤ smoothZeroCountingN0 10 := by
  unfold smoothZeroCountingN0
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have h_pi_gt : 3.14 < Real.pi := Real.pi_gt_d2
  have h_eq : (10 : ℝ) / (2 * Real.pi) = 5 / Real.pi := by ring
  rw [h_eq]
  have h_5_lt_pi : Real.pi < 5 := by linarith
  have h_5pi_pos : 0 < 5 / Real.pi := by positivity
  -- x := (5 - π) / π ≥ 0
  have h_x_nn : (0 : ℝ) ≤ (5 - Real.pi) / Real.pi := by
    apply div_nonneg
    · linarith
    · exact le_of_lt h_pi_pos
  -- 1 + x = 5/π
  have h_one_add : 1 + (5 - Real.pi) / Real.pi = 5 / Real.pi := by
    field_simp
    ring
  -- Padé: log(5/π) ≥ 2x/(x+2) = 2(5-π)/(5+π)
  have h_pade_raw :
      2 * ((5 - Real.pi) / Real.pi) / ((5 - Real.pi) / Real.pi + 2)
        ≤ Real.log (1 + (5 - Real.pi) / Real.pi) :=
    Real.le_log_one_add_of_nonneg h_x_nn
  rw [h_one_add] at h_pade_raw
  -- Setup nonzero hypotheses and the polynomial-form Padé bound
  have h_5_plus_pi_pos : (0 : ℝ) < 5 + Real.pi := by linarith
  have hπ_ne : Real.pi ≠ 0 := ne_of_gt h_pi_pos
  have h5pπ_ne : (5 + Real.pi : ℝ) ≠ 0 := ne_of_gt h_5_plus_pi_pos
  have h_inner_pos : (0 : ℝ) < (5 - Real.pi) / Real.pi + 2 := by positivity
  have h_inner_ne : ((5 - Real.pi) / Real.pi + 2) ≠ 0 := ne_of_gt h_inner_pos
  -- Step 1: clear outer division by multiplying by ((5-π)/π + 2)
  have h_pade_step1 :
      2 * ((5 - Real.pi) / Real.pi)
        ≤ ((5 - Real.pi) / Real.pi + 2) * Real.log (5 / Real.pi) := by
    have h := mul_le_mul_of_nonneg_right h_pade_raw (le_of_lt h_inner_pos)
    rw [div_mul_cancel₀ _ h_inner_ne] at h
    linarith
  -- Step 2: multiply by π to clear inner /π
  -- π · 2((5-π)/π) = 2(5-π); π · ((5-π)/π + 2) = (5-π) + 2π = 5+π
  have h_pade_poly :
      2 * (5 - Real.pi) ≤ (5 + Real.pi) * Real.log (5 / Real.pi) := by
    have h := mul_le_mul_of_nonneg_left h_pade_step1 (le_of_lt h_pi_pos)
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
    linarith [h, hl.symm.le, hl.le, hr.le, hr.symm.le]
  -- Step 3: polynomial inequality from π bounds — `(200-37π)(5+π) ≤ 400(5-π)`
  -- equivalently `37π² - 415π + 1000 ≥ 0` (margin ≈ 60 on (3.14, 3.15))
  have h_polyq :
      (200 - 37 * Real.pi) * (5 + Real.pi) ≤ 400 * (5 - Real.pi) := by
    nlinarith [h_pi_lt, h_pi_gt, sq_nonneg (Real.pi - 3.14),
               sq_nonneg (3.15 - Real.pi)]
  -- Step 4: chain via h_pade_poly · 200: 200·(5+π)·log(5/π) ≥ 400(5-π) ≥ (200-37π)(5+π)
  have h_chain :
      (200 - 37 * Real.pi) * (5 + Real.pi)
        ≤ 200 * ((5 + Real.pi) * Real.log (5 / Real.pi)) := by
    have := mul_le_mul_of_nonneg_left h_pade_poly (by norm_num : (0 : ℝ) ≤ 200)
    linarith
  -- Step 5: divide by (5+π) > 0: 200 - 37π ≤ 200·log(5/π)
  have h_200_log :
      200 - 37 * Real.pi ≤ 200 * Real.log (5 / Real.pi) := by
    by_contra hneg
    push Not at hneg
    have h_mul := mul_lt_mul_of_pos_right hneg h_5_plus_pi_pos
    have h_assoc :
        200 * Real.log (5 / Real.pi) * (5 + Real.pi)
          = 200 * ((5 + Real.pi) * Real.log (5 / Real.pi)) := by ring
    rw [h_assoc] at h_mul
    linarith
  -- Step 6: derive goal by multiplying 1/(40π) to scale to (5/π)·log(5/π)
  -- Equivalently: 0 ≤ 200·log(5/π) - 200 + 37π (from h_200_log + linarith)
  have h_target_poly :
      (0 : ℝ) ≤ 200 * Real.log (5 / Real.pi) - 200 + 37 * Real.pi := by
    linarith
  -- Scale by 1/(40π) > 0 to convert to goal form
  have h_inv_pos : (0 : ℝ) < 1 / (40 * Real.pi) := by positivity
  have h_scaled := mul_le_mul_of_nonneg_left h_target_poly (le_of_lt h_inv_pos)
  rw [mul_zero] at h_scaled
  -- Simplify 1/(40π) · (200·log(5/π) - 200 + 37π) = (5/π)·log(5/π) - 5/π + 37/40
  have h_lhs_eq :
      (1 / (40 * Real.pi))
        * (200 * Real.log (5 / Real.pi) - 200 + 37 * Real.pi)
        = (5 / Real.pi) * Real.log (5 / Real.pi) - 5 / Real.pi + 37 / 40 := by
    field_simp
    ring
  rw [h_lhs_eq] at h_scaled
  -- 37/40 = 7/8 + 1/20, so the goal follows by linarith
  linarith

/-- ⭐ **PROVED — `zeroDensityRho T ≤ T`** for `T ≥ 2π`.
Via `log x ≤ x` applied to `x = T/(2π)`, then `log(T/(2π))/(2π) ≤ T/(4π²) ≤ T`
(since `4π² > 1`). -/
lemma zeroDensityRho_le_T
    {T : ℝ} (hT2pi : 2 * Real.pi ≤ T) :
    zeroDensityRho T ≤ T := by
  unfold zeroDensityRho
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_gt_d2 : 3.14 < Real.pi := Real.pi_gt_d2
  have h_2pi_pos : 0 < 2 * Real.pi := by linarith
  have hT_pos : 0 < T := by linarith
  have hT_2pi_pos : 0 < T / (2 * Real.pi) := by positivity
  have h_log_le : Real.log (T / (2 * Real.pi)) ≤ T / (2 * Real.pi) - 1 :=
    Real.log_le_sub_one_of_pos hT_2pi_pos
  have h_log_le_T_2pi : Real.log (T / (2 * Real.pi)) ≤ T / (2 * Real.pi) := by
    linarith
  have h_inv_pos : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  have h_step :
      (1 / (2 * Real.pi)) * Real.log (T / (2 * Real.pi))
        ≤ (1 / (2 * Real.pi)) * (T / (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_left h_log_le_T_2pi (le_of_lt h_inv_pos)
  -- (1/(2π))·(T/(2π)) = T/(4π²)
  have h_2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h_2pi_pos
  have h_eq :
      (1 / (2 * Real.pi)) * (T / (2 * Real.pi))
        = T / ((2 * Real.pi)^2) := by
    rw [sq, mul_comm (2 * Real.pi) (2 * Real.pi)]
    field_simp
  have h_2pi_sq_gt_1 : (1 : ℝ) ≤ (2 * Real.pi)^2 := by
    nlinarith [h_pi_gt_d2]
  have h_T_div_le : T / ((2 * Real.pi)^2) ≤ T := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2 * Real.pi)^2)]
    nlinarith [hT_pos, h_2pi_sq_gt_1]
  linarith [h_step, h_eq, h_T_div_le]

/-- ⭐ **PROVED — `|zeroDensityRho u| ≤ (1/(2π)) · log u` for `u ≥ 2π`.**
For `u ≥ 2π`, `ρ u = (1/(2π))·(log u - log(2π)) ≥ 0` and `log(2π) ≥ 0`
(since `2π ≥ 1`), so `|ρ u| = ρ u ≤ (1/(2π)) log u`. -/
lemma zeroDensityRho_abs_le_log_div_two_pi_of_ge_two_pi
    {u : ℝ} (hu : 2 * Real.pi ≤ u) :
    |zeroDensityRho u| ≤ (1 / (2 * Real.pi)) * Real.log u := by
  have h_nn : 0 ≤ zeroDensityRho u := zeroDensityRho_nonneg_of_ge_two_pi hu
  rw [abs_of_nonneg h_nn]
  unfold zeroDensityRho
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_inv_nn : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have h2pi_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have h_log_2pi_nn : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg h2pi_ge_one
  have h_log_eq : Real.log (u / (2 * Real.pi))
                  = Real.log u - Real.log (2 * Real.pi) := by
    have h_u_pos : 0 < u := lt_of_lt_of_le h2pi_pos hu
    rw [Real.log_div (ne_of_gt h_u_pos) (ne_of_gt h2pi_pos)]
  rw [h_log_eq]
  -- (1/(2π)) * (log u - log(2π)) ≤ (1/(2π)) * log u
  -- since -(1/(2π)) * log(2π) ≤ 0
  have h_diff_nn :
      (1 / (2 * Real.pi)) * Real.log u -
        (1 / (2 * Real.pi)) * (Real.log u - Real.log (2 * Real.pi))
        = (1 / (2 * Real.pi)) * Real.log (2 * Real.pi) := by ring
  nlinarith [mul_nonneg h2pi_inv_nn h_log_2pi_nn]

/-- ⭐ **PROVED — `zeroDensityRho` is monotone on `[2π, ∞)`.** Follows
from `log` monotonicity on `[1, ∞)` after dividing by `2π`. -/
lemma zeroDensityRho_mono_on_tail :
    MonotoneOn zeroDensityRho (Set.Ici (2 * Real.pi)) := by
  intro a ha b hb hab
  unfold zeroDensityRho
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_inv_nn : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hab_div : a / (2 * Real.pi) ≤ b / (2 * Real.pi) := by
    exact div_le_div_of_nonneg_right hab (le_of_lt h2pi_pos)
  have ha_div_pos : 0 < a / (2 * Real.pi) :=
    div_pos (lt_of_lt_of_le h2pi_pos ha) h2pi_pos
  have h_log_le :
      Real.log (a / (2 * Real.pi)) ≤ Real.log (b / (2 * Real.pi)) :=
    Real.log_le_log ha_div_pos hab_div
  exact mul_le_mul_of_nonneg_left h_log_le h2pi_inv_nn

/-- ⭐ **PROVED — `zeroDensityRho` is continuous at any `X > 0`.**
`ρ(u) = (1/(2π))·log(u/(2π))`; `log` is continuous away from `0`. -/
lemma zeroDensityRho_continuousAt {X : ℝ} (hX : 0 < X) :
    ContinuousAt zeroDensityRho X := by
  unfold zeroDensityRho
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_div_pos : 0 < X / (2 * Real.pi) := div_pos hX h2pi_pos
  have h_div_ne : X / (2 * Real.pi) ≠ 0 := ne_of_gt h_div_pos
  have h_inner : ContinuousAt (fun u : ℝ => u / (2 * Real.pi)) X :=
    (continuous_id.div_const _).continuousAt
  -- Use `ContinuousAt.log` which composes cleanly (avoids the
  -- `HDiv.hDiv` unification trap that bites `Real.continuousAt_log.comp`).
  have h_log : ContinuousAt (fun u : ℝ => Real.log (u / (2 * Real.pi))) X :=
    h_inner.log h_div_ne
  exact continuousAt_const.mul h_log

/-- ⭐ **PROVED — `ρ(T) ≤ ρ(u)` on the tail.** -/
lemma zeroDensityRho_le_of_tail
    {T u : ℝ} (hT : 2 * Real.pi ≤ T) (hTu : T ≤ u) :
    zeroDensityRho T ≤ zeroDensityRho u := by
  exact zeroDensityRho_mono_on_tail hT (le_trans hT hTu) hTu

/-- ⭐ **PROVED — eventual log-growth bound for `zeroDensityRho`.**
For `A := 1/(2π)`, `B := 0`, eventually `|ρ u| ≤ A · log u + B`. Direct
form for plugging into the smooth density majorant chain. -/
lemma zeroDensityRho_log_growth_eventually :
    ∀ᶠ u : ℝ in Filter.atTop,
      |zeroDensityRho u| ≤ (1 / (2 * Real.pi)) * Real.log u + 0 := by
  filter_upwards [Filter.eventually_ge_atTop (2 * Real.pi)] with u hu
  have := zeroDensityRho_abs_le_log_div_two_pi_of_ge_two_pi hu
  linarith

/-- ⭐ **PROVED — `|N₀(u)| ≤ 1/2` for `u ∈ [2π, U]`** given the right
endpoint bound `N₀(U) ≤ 1/2`. Parameterized generalization fixing the
upper endpoint `U`.

Lower bound is automatic from `smoothZeroCountingN0_at_two_pi`
(`N₀(2π) = -1/8 ≥ -1/2`) and monotonicity on `[2π, ∞)`. -/
theorem abs_smoothZeroCountingN0_le_half_on_first_band_param
    {U : ℝ} (hU_ge_two_pi : 2 * Real.pi ≤ U)
    (hN0_U_le_half : smoothZeroCountingN0 U ≤ 1 / 2)
    {u : ℝ}
    (hlo : 2 * Real.pi ≤ u) (hhi : u ≤ U) :
    |smoothZeroCountingN0 u| ≤ (1 / 2 : ℝ) := by
  have h_mono := smoothZeroCountingN0_monotoneOn_Ici_two_pi
  have h_2pi_mem : (2 * Real.pi : ℝ) ∈ Set.Ici (2 * Real.pi) := Set.self_mem_Ici
  have h_u_mem : u ∈ Set.Ici (2 * Real.pi) := Set.mem_Ici.mpr hlo
  have h_U_mem : U ∈ Set.Ici (2 * Real.pi) := Set.mem_Ici.mpr hU_ge_two_pi
  have h_low : smoothZeroCountingN0 (2 * Real.pi) ≤ smoothZeroCountingN0 u :=
    h_mono h_2pi_mem h_u_mem hlo
  have h_high : smoothZeroCountingN0 u ≤ smoothZeroCountingN0 U :=
    h_mono h_u_mem h_U_mem hhi
  rw [smoothZeroCountingN0_at_two_pi] at h_low
  have h_high' : smoothZeroCountingN0 u ≤ 1 / 2 :=
    le_trans h_high hN0_U_le_half
  rw [abs_le]
  refine ⟨?_, h_high'⟩
  linarith

/-- 🌟 **PROVED — endpoint difference `N₀(14) − N₀(10) ≤ 1/2`** by
combining the bounds `N₀(14) ≤ 9/20` and `N₀(10) ≥ -1/20`. -/
theorem smoothZeroCountingN0_14_sub_10_le_half :
    smoothZeroCountingN0 14 - smoothZeroCountingN0 10 ≤ (1 / 2 : ℝ) := by
  have h14 := smoothZeroCountingN0_at_14_le_nine_twentieth
  have h10 := smoothZeroCountingN0_at_10_ge_neg_one_twentieth
  linarith

/-- 🌟 **PROVED — `|N₀(u)| ≤ 1/2` for `u ∈ [2π, 14]`.**
Specialization of `abs_smoothZeroCountingN0_le_half_on_first_band_param`
with the new endpoint `smoothZeroCountingN0_at_14_le_half`. -/
theorem abs_smoothZeroCountingN0_le_half_on_first_band_14
    {u : ℝ}
    (hlo : 2 * Real.pi ≤ u) (hhi : u ≤ 14) :
    |smoothZeroCountingN0 u| ≤ (1 / 2 : ℝ) := by
  have h14_ge_2pi : 2 * Real.pi ≤ 14 := by
    have : Real.pi < 4 := Real.pi_lt_four
    linarith
  exact abs_smoothZeroCountingN0_le_half_on_first_band_param
    h14_ge_2pi smoothZeroCountingN0_at_14_le_half hlo hhi

/-- 🌟 **PROVED — uniform diff bound** `|N₀(10) − N₀(u)| ≤ 1/2` on
`[11, 14]`. By monotonicity (`N₀` increasing on `[2π, ∞)`), the
absolute value equals `N₀(u) − N₀(10)`, and the worst case is at
`u = 14`. -/
theorem abs_N0_10_sub_N0_le_half_on_11_14
    {u : ℝ} (hu11 : 11 ≤ u) (hu14 : u ≤ 14) :
    |smoothZeroCountingN0 10 - smoothZeroCountingN0 u| ≤ (1 / 2 : ℝ) := by
  have h_pi_lt_four : Real.pi < 4 := Real.pi_lt_four
  have h_2pi_le_10 : (2 * Real.pi : ℝ) ≤ 10 := by linarith
  have h_10_le_u : (10 : ℝ) ≤ u := by linarith
  have h_10_le_14 : (10 : ℝ) ≤ 14 := by norm_num
  have h_mono := smoothZeroCountingN0_monotoneOn_Ici_two_pi
  have h_10_mem : (10 : ℝ) ∈ Set.Ici (2 * Real.pi) :=
    Set.mem_Ici.mpr h_2pi_le_10
  have h_u_mem : u ∈ Set.Ici (2 * Real.pi) :=
    Set.mem_Ici.mpr (le_trans h_2pi_le_10 h_10_le_u)
  have h_14_mem : (14 : ℝ) ∈ Set.Ici (2 * Real.pi) :=
    Set.mem_Ici.mpr (le_trans h_2pi_le_10 h_10_le_14)
  have h_10_le_N0_u : smoothZeroCountingN0 10 ≤ smoothZeroCountingN0 u :=
    h_mono h_10_mem h_u_mem h_10_le_u
  have h_N0_u_le_14 : smoothZeroCountingN0 u ≤ smoothZeroCountingN0 14 :=
    h_mono h_u_mem h_14_mem hu14
  have h_diff_le : smoothZeroCountingN0 14 - smoothZeroCountingN0 10
                 ≤ (1 / 2 : ℝ) :=
    smoothZeroCountingN0_14_sub_10_le_half
  -- |N₀(10) - N₀(u)| = N₀(u) - N₀(10), since N₀(10) ≤ N₀(u)
  have h_eq : |smoothZeroCountingN0 10 - smoothZeroCountingN0 u|
            = smoothZeroCountingN0 u - smoothZeroCountingN0 10 := by
    rw [abs_of_nonpos (by linarith : smoothZeroCountingN0 10
                                       - smoothZeroCountingN0 u ≤ 0)]
    ring
  rw [h_eq]
  linarith

/-- 🌟 **PROVED — `ρ(10) ≥ 259/3586`.** -/
theorem zeroDensityRho_10_ge_259_div_3586 :
    (259 / 3586 : ℝ) ≤ zeroDensityRho 10 := by
  have h_eq : (10 : ℝ) / (2 * Real.pi) = 5 / Real.pi := by ring
  have h_inv : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) :=
    one_div_two_pi_ge_seven_fortyfour
  have h_log : (74 / 163 : ℝ) ≤ Real.log (5 / Real.pi) :=
    log_5_div_pi_ge_74_div_163
  have h_44_nn : (0 : ℝ) ≤ (74 / 163 : ℝ) := by norm_num
  have h_inv_nn : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    positivity
  calc (259 / 3586 : ℝ)
      = (7 / 44) * (74 / 163) := by norm_num
    _ ≤ (1 / (2 * Real.pi)) * Real.log (5 / Real.pi) :=
        mul_le_mul h_inv h_log h_44_nn h_inv_nn
    _ = zeroDensityRho 10 := by
        unfold zeroDensityRho
        rw [h_eq]

end OverflowResidueRH
