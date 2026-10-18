/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecificLimits.Normed
import RiemannHypothesis.Xi.EntireXiMellinGrowth
import RiemannHypothesis.ComplexAnalysis.RealPartGrowth

/-!
# Unconditional subquadratic logarithmic growth of the xi pullback

The theta--Mellin factorial envelope gives an explicit order-one estimate on
the dyadic Jensen circles centered at `I / 2`.  This file propagates that
boundary estimate to arbitrary points by the maximum-modulus principle and
then proves that its logarithm is `o(‖z‖²)`.

The intermediate theorem is deliberately phrased for any
`EntireXiPullbackDyadicBoundaryGrowthData`.  Its final specialization uses the
unconditional data constructed from Mathlib's modified Hurwitz theta kernel.
-/

open Filter Metric Real Set
open scoped Topology

namespace OverflowResidueRH

private lemma four_pow_eq_two_pow_sq (n : ℕ) :
    (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  omega

/-- A dyadic order-one boundary estimate on the Jensen circles implies
subquadratic logarithmic norm growth of the entire xi pullback.

The proof chooses the dyadic annulus containing `‖z‖`, observes that the
corresponding Jensen disk contains `z`, and applies maximum modulus.  Dividing
the resulting order-one exponent by `‖z‖²` leaves a linear-over-exponential
sequence, which tends to zero. -/
theorem
    EntireXiPullbackDyadicBoundaryGrowthData.hasSubquadraticLogNormGrowthAtInfinity
    (H : EntireXiPullbackDyadicBoundaryGrowthData) :
    HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback := by
  intro ε hε
  have hshift : Tendsto
      (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ 1) / (2 : ℝ) ^ (n + 1))
      atTop (𝓝 0) :=
    (tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)).comp (tendsto_add_atTop_nat 1)
  have hlin0 : Tendsto
      (fun n : ℕ ↦ (2 * H.A) *
        ((((n + 1 : ℕ) : ℝ) ^ 1) / (2 : ℝ) ^ (n + 1)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hshift
  have hlin : Tendsto
      (fun n : ℕ ↦ H.A * ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    convert hlin0 using 1
    funext n
    rw [pow_one, pow_succ]
    field_simp
  have hinvfour : Tendsto (fun n : ℕ ↦ ((1 / 4 : ℝ) ^ n))
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hconst : Tendsto (fun n : ℕ ↦ H.A₀ / (4 : ℝ) ^ n)
      atTop (𝓝 0) := by
    have hmul : Tendsto (fun n : ℕ ↦ H.A₀ * (1 / 4 : ℝ) ^ n)
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hinvfour
    convert hmul using 1
    funext n
    rw [div_pow]
    simp [div_eq_mul_inv]
  have hlin_small : ∀ᶠ n : ℕ in atTop,
      H.A * ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n < ε / 2 :=
    hlin.eventually (Iio_mem_nhds (by positivity))
  have hconst_small : ∀ᶠ n : ℕ in atTop,
      H.A₀ / (4 : ℝ) ^ n < ε / 2 :=
    hconst.eventually (Iio_mem_nhds (by positivity))
  have henv_event : ∀ᶠ n : ℕ in atTop,
      H.A * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n + H.A₀ ≤
        ε * ((2 : ℝ) ^ n) ^ 2 := by
    filter_upwards [hlin_small, hconst_small] with n hnlin hnconst
    have htwo : 0 < (2 : ℝ) ^ n := by positivity
    have hfour : 0 < (4 : ℝ) ^ n := by positivity
    have hnlin' : H.A * ((n + 1 : ℕ) : ℝ) <
        (ε / 2) * (2 : ℝ) ^ n := (div_lt_iff₀ htwo).mp hnlin
    have hnconst' : H.A₀ < (ε / 2) * (4 : ℝ) ^ n :=
      (div_lt_iff₀ hfour).mp hnconst
    calc
      H.A * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n + H.A₀ ≤
          ((ε / 2) * (2 : ℝ) ^ n) * (2 : ℝ) ^ n +
            (ε / 2) * (4 : ℝ) ^ n := by
        gcongr
      _ = ε * ((2 : ℝ) ^ n) ^ 2 := by
        rw [four_pow_eq_two_pow_sq]
        ring
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 henv_event)
  let N : ℕ := max H.lower N₀
  let R : ℝ := (2 : ℝ) ^ N
  refine ⟨R, by positivity, ?_⟩
  intro z hz
  let r : ℝ := ‖z‖
  have hr1 : 1 ≤ r := by
    have hR1 : 1 ≤ R := by
      dsimp [R]
      exact one_le_pow₀ (by norm_num)
    exact hR1.trans hz
  obtain ⟨n, hnlow, hnup⟩ := exists_nat_pow_near hr1
    (by norm_num : (1 : ℝ) < 2)
  have hNn : N ≤ n := by
    by_contra hnot
    have hnN : n + 1 ≤ N := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnot)
    have hpows : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ N := by
      exact pow_le_pow_right₀ (by norm_num) hnN
    have hRr : R ≤ r := by simpa [r] using hz
    dsimp [R] at hRr
    linarith
  have hnlower : H.lower ≤ n :=
    (le_max_left H.lower N₀).trans hNn
  have hnN₀ : N₀ ≤ n :=
    (le_max_right H.lower N₀).trans hNn
  have henv := hN₀ n hnN₀
  let q : ℝ :=
    H.A * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n + H.A₀
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact add_nonneg
      (mul_nonneg (mul_nonneg H.A_nonneg (by positivity)) (by positivity))
      H.A₀_nonneg
  have houter_pos : 0 < entireXiPullbackJensenOuterRadius n := by
    dsimp [entireXiPullbackJensenOuterRadius,
      entireXiPullbackJensenInnerRadius]
    positivity
  have hzclosed : z ∈ closedBall entireXiPullbackJensenCenter
      (entireXiPullbackJensenOuterRadius n) := by
    rw [mem_closedBall]
    calc
      dist z entireXiPullbackJensenCenter ≤ dist z 0 +
          dist 0 entireXiPullbackJensenCenter := dist_triangle _ _ _
      _ = r + 1 / 2 := by
        simp [r, entireXiPullbackJensenCenter, dist_zero_right]
      _ ≤ entireXiPullbackJensenOuterRadius n := by
        dsimp [entireXiPullbackJensenOuterRadius,
          entireXiPullbackJensenInnerRadius]
        rw [pow_succ] at hnup
        nlinarith
  have hmax : ‖EntireXiPullback z‖ ≤ Real.exp q := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      isBounded_ball EntireXiPullback_differentiable.diffContOnCl
    · intro w hw
      apply H.boundary_norm_le n hnlower w
      rw [frontier_ball _ houter_pos.ne'] at hw
      exact hw
    · rwa [closure_ball _ houter_pos.ne']
  have hlog : Real.log ‖EntireXiPullback z‖ ≤ q := by
    by_cases hzero : EntireXiPullback z = 0
    · simpa [hzero] using hq_nonneg
    · have hnormpos : 0 < ‖EntireXiPullback z‖ := norm_pos_iff.mpr hzero
      have := Real.log_le_log hnormpos hmax
      simpa using this
  calc
    Real.log ‖EntireXiPullback z‖ ≤ q := hlog
    _ ≤ ε * ((2 : ℝ) ^ n) ^ 2 := by simpa [q] using henv
    _ ≤ ε * ‖z‖ ^ 2 := by
      gcongr

/-- The actual critical-line xi pullback has unconditional logarithmic norm
growth `o(‖z‖²)`.  No xi-specific growth datum is assumed: the input is the
theta--Mellin factorial estimate proved in `EntireXiMellinGrowth`. -/
theorem entireXiPullback_hasSubquadraticLogNormGrowthAtInfinity :
    HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback :=
  entireXiPullbackThetaDyadicBoundaryGrowthData
    |>.hasSubquadraticLogNormGrowthAtInfinity

end OverflowResidueRH
