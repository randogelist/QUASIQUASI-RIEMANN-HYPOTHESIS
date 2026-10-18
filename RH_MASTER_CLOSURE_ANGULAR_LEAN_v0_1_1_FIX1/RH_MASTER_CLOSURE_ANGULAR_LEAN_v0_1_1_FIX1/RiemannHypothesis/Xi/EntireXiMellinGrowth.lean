import RiemannHypothesis.Xi.ThetaKernelMellinGrowth
import RiemannHypothesis.Xi.Definitions
import RiemannHypothesis.ComplexAnalysis.FactorialDyadicGrowth
import RiemannHypothesis.Xi.JensenDyadicCountBridge

/-!
# Unconditional dyadic growth and zero distribution for the xi pullback

This file finishes the analytic count side of the classical criterion for the
concrete function `EntireXiPullback`.  The actual modified Hurwitz theta kernel
has two-sided exponential decay; its Mellin transform therefore has a
factorial envelope.  The polynomial prefactor in `entireRiemannXi` is absorbed
by shifting the factorial index, and `FactorialDyadicGrowth` converts the
result to the boundary estimate required by the Jensen bridge.

Consequently the canonical xi zeros have inverse-square summable moduli with
no xi-specific growth hypothesis left in the public statement.
-/

namespace OverflowResidueRH

open Real Complex

/-- The theta-kernel factorial envelope survives multiplication by the
quadratic prefactor defining the entire Riemann xi function. -/
theorem norm_entireRiemannXi_le_factorial
    (s : ℂ) (n : ℕ)
    (hupper : (s / 2).re - 1 ≤ n)
    (hlower : -(n : ℝ) - 2 ≤ (s / 2).re - 1 - (1 / 2 : ℝ)) :
    ‖entireRiemannXi s‖ ≤
      (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ *
        (hurwitzThetaMellinTwoSidedExponentialDecay.A *
          ((1 / hurwitzThetaMellinTwoSidedExponentialDecay.p) ^
            (n + 1 : ℝ) * n.factorial)) + 1 / 2 := by
  rw [entireRiemannXi]
  calc
    ‖(1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)‖ ≤
        ‖(1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s‖ +
          ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
    _ = (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ +
          1 / 2 := by
      rw [norm_mul, norm_mul, norm_mul]
      norm_num [Complex.norm_real]
    _ ≤ (1 / 2 : ℝ) * ‖s‖ * ‖s - 1‖ *
        (hurwitzThetaMellinTwoSidedExponentialDecay.A *
          ((1 / hurwitzThetaMellinTwoSidedExponentialDecay.p) ^
            (n + 1 : ℝ) * n.factorial)) + 1 / 2 := by
      gcongr
      exact norm_completedRiemannZeta₀_le_factorial s n hupper hlower

/-- A radial factorial envelope for the critical-line pullback of xi.  The
same natural number controls the norm of the input and the factorial index. -/
theorem norm_entireXiPullback_le_factorial_of_norm_le_nat
    (z : ℂ) (n : ℕ) (hn : 1 ≤ n) (hz : ‖z‖ ≤ n) :
    ‖EntireXiPullback z‖ ≤
      (1 / 2 : ℝ) * (‖z‖ + 1 / 2) ^ 2 *
        (hurwitzThetaMellinTwoSidedExponentialDecay.A *
          ((1 / hurwitzThetaMellinTwoSidedExponentialDecay.p) ^
            (n + 1 : ℝ) * n.factorial)) + 1 / 2 := by
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * z
  have hs_norm : ‖s‖ ≤ ‖z‖ + 1 / 2 := by
    dsimp [s]
    calc
      ‖(1 / 2 : ℂ) + Complex.I * z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖Complex.I * z‖ :=
        norm_add_le _ _
      _ = ‖z‖ + 1 / 2 := by
        rw [norm_mul, norm_I, one_mul]
        norm_num [Complex.norm_real]
        ring
  have hs_sub_norm : ‖s - 1‖ ≤ ‖z‖ + 1 / 2 := by
    dsimp [s]
    rw [show (1 / 2 : ℂ) + Complex.I * z - 1 =
      -(1 / 2 : ℂ) + Complex.I * z by ring]
    calc
      ‖-(1 / 2 : ℂ) + Complex.I * z‖ ≤ ‖-(1 / 2 : ℂ)‖ + ‖Complex.I * z‖ :=
        norm_add_le _ _
      _ = ‖z‖ + 1 / 2 := by
        rw [norm_neg, norm_mul, norm_I, one_mul]
        norm_num [Complex.norm_real]
        ring
  have hs_half_norm : ‖s / 2‖ ≤ n := by
    calc
      ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, Complex.norm_two]
      _ ≤ (‖z‖ + 1 / 2) / 2 := div_le_div_of_nonneg_right hs_norm (by norm_num)
      _ ≤ n := by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
  have hupper : (s / 2).re - 1 ≤ n := by
    calc
      (s / 2).re - 1 ≤ ‖s / 2‖ - 1 := sub_le_sub_right (Complex.re_le_norm _) _
      _ ≤ n := by linarith
  have hlower : -(n : ℝ) - 2 ≤ (s / 2).re - 1 - (1 / 2 : ℝ) := by
    have hre : -(n : ℝ) ≤ (s / 2).re := by
      calc
        -(n : ℝ) ≤ -‖s / 2‖ := neg_le_neg hs_half_norm
        _ ≤ (s / 2).re := neg_le_of_abs_le (abs_re_le_norm (s / 2))
    linarith
  rw [EntireXiPullback]
  refine (norm_entireRiemannXi_le_factorial s n hupper hlower).trans ?_
  have hprod : ‖s‖ * ‖s - 1‖ ≤ (‖z‖ + 1 / 2) ^ 2 := by
    calc
      ‖s‖ * ‖s - 1‖ ≤ (‖z‖ + 1 / 2) * (‖z‖ + 1 / 2) := by
        gcongr
      _ = (‖z‖ + 1 / 2) ^ 2 := by ring
  have hfactor : 0 ≤
      hurwitzThetaMellinTwoSidedExponentialDecay.A *
        ((1 / hurwitzThetaMellinTwoSidedExponentialDecay.p) ^
          (n + 1 : ℝ) * n.factorial) := by
    exact mul_nonneg hurwitzThetaMellinTwoSidedExponentialDecay.A_nonneg
      (mul_nonneg
        (Real.rpow_nonneg
          (div_nonneg (by norm_num)
            hurwitzThetaMellinTwoSidedExponentialDecay.p_pos.le) _)
        (Nat.cast_nonneg _))
  simpa [add_comm, mul_assoc] using
    (add_le_add_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod
          (show 0 ≤ (1 / 2 : ℝ) by norm_num)) hfactor) (1 / 2 : ℝ))

/-- Unconditional Jensen boundary-growth data for the actual xi pullback,
constructed from Mathlib's theta kernel and explicit factorial arithmetic. -/
noncomputable def entireXiPullbackThetaDyadicBoundaryGrowthData :
    EntireXiPullbackDyadicBoundaryGrowthData := by
  let Aθ : ℝ := hurwitzThetaMellinTwoSidedExponentialDecay.A
  let B₀ : ℝ := 1 / hurwitzThetaMellinTwoSidedExponentialDecay.p
  let B : ℝ := max 1 B₀
  let C : ℝ := Aθ / 2 + 1 / 2
  let K : ℕ := 6
  let A : ℝ := factorialDyadicGrowthRate C B K
  have hAθ : 0 ≤ Aθ := hurwitzThetaMellinTwoSidedExponentialDecay.A_nonneg
  have hB₀ : 0 ≤ B₀ :=
    div_nonneg (by norm_num) hurwitzThetaMellinTwoSidedExponentialDecay.p_pos.le
  have hB : 0 ≤ B := le_trans (by norm_num) (le_max_left 1 B₀)
  have hB₀B : B₀ ≤ B := le_max_right 1 B₀
  have hBone : 1 ≤ B := le_max_left 1 B₀
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine
    { lower := 1
      A := A
      A₀ := 0
      A_nonneg := factorialDyadicGrowthRate_nonneg C B K hC hB
      A₀_nonneg := le_rfl
      boundary_norm_le := ?_ }
  intro m hm z hz
  let N : ℕ := 4 * 2 ^ m
  let J : ℕ := N + 2
  have hm_two : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
    simpa using
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hm)
  have hdist : dist z entireXiPullbackJensenCenter =
      entireXiPullbackJensenOuterRadius m := hz
  have hzN : ‖z‖ ≤ (N : ℝ) := by
    calc
      ‖z‖ = dist z 0 := by simp
      _ ≤ dist z entireXiPullbackJensenCenter +
          dist entireXiPullbackJensenCenter 0 := dist_triangle _ _ _
      _ = 2 * ((2 : ℝ) ^ m + 1) + 1 / 2 := by
        rw [hdist]
        simp [entireXiPullbackJensenOuterRadius,
          entireXiPullbackJensenInnerRadius,
          entireXiPullbackJensenCenter]
      _ ≤ (N : ℝ) := by
        dsimp [N]
        push_cast
        nlinarith
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hN_one : 1 ≤ N := hN_pos
  have hxi := norm_entireXiPullback_le_factorial_of_norm_le_nat
    z N hN_one hzN
  have hxi' : ‖EntireXiPullback z‖ ≤
      (1 / 2 : ℝ) * (‖z‖ + 1 / 2) ^ 2 *
        (Aθ * (B₀ ^ ((N + 1 : ℕ) : ℝ) * N.factorial)) + 1 / 2 := by
    simpa [Aθ, B₀, Nat.cast_add, Nat.cast_one] using hxi
  let X : ℝ := B ^ ((J + 1 : ℕ) : ℝ) * J.factorial
  have hpoly : (‖z‖ + 1 / 2) ^ 2 ≤ (((N + 1 : ℕ) : ℝ)) ^ 2 := by
    have hbase : ‖z‖ + 1 / 2 ≤ ((N + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    gcongr
  have hpolyfact :
      (‖z‖ + 1 / 2) ^ 2 * (N.factorial : ℝ) ≤
        (J.factorial : ℝ) := by
    calc
      (‖z‖ + 1 / 2) ^ 2 * (N.factorial : ℝ) ≤
          (((N + 1 : ℕ) : ℝ)) ^ 2 * (N.factorial : ℝ) := by
        gcongr
      _ = (N.factorial : ℝ) * (((N + 1 : ℕ) : ℝ)) ^ 2 := by ring
      _ ≤ (J.factorial : ℝ) := by
        dsimp [J]
        exact_mod_cast
          (Nat.factorial_mul_pow_le_factorial (m := N) (n := 2))
  have hpow₀ : B₀ ^ ((N + 1 : ℕ) : ℝ) ≤
      B ^ ((N + 1 : ℕ) : ℝ) :=
    Real.rpow_le_rpow hB₀ hB₀B (by positivity)
  have hpow₁ : B ^ ((N + 1 : ℕ) : ℝ) ≤
      B ^ ((J + 1 : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hBone
    exact_mod_cast (show N + 1 ≤ J + 1 by omega)
  have hcore :
      B₀ ^ ((N + 1 : ℕ) : ℝ) *
          ((‖z‖ + 1 / 2) ^ 2 * (N.factorial : ℝ)) ≤ X := by
    dsimp [X]
    exact mul_le_mul (hpow₀.trans hpow₁) hpolyfact
      (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg hB _)
  have hmain :
      (1 / 2 : ℝ) * (‖z‖ + 1 / 2) ^ 2 *
          (Aθ * (B₀ ^ ((N + 1 : ℕ) : ℝ) * N.factorial)) ≤
        (Aθ / 2) * X := by
    calc
      (1 / 2 : ℝ) * (‖z‖ + 1 / 2) ^ 2 *
          (Aθ * (B₀ ^ ((N + 1 : ℕ) : ℝ) * N.factorial)) =
          (Aθ / 2) *
            (B₀ ^ ((N + 1 : ℕ) : ℝ) *
              ((‖z‖ + 1 / 2) ^ 2 * N.factorial)) := by ring
      _ ≤ (Aθ / 2) * X :=
        mul_le_mul_of_nonneg_left hcore (div_nonneg hAθ (by norm_num))
  have hX : 1 ≤ X := by
    dsimp [X]
    have hpowX : 1 ≤ B ^ ((J + 1 : ℕ) : ℝ) :=
      Real.one_le_rpow hBone (by positivity)
    have hfactX : 1 ≤ (J.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos J)
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ B ^ ((J + 1 : ℕ) : ℝ) * J.factorial :=
        mul_le_mul hpowX hfactX (by norm_num) (Real.rpow_nonneg hB _)
  have henvelope : ‖EntireXiPullback z‖ ≤
      C * (B ^ ((J + 1 : ℕ) : ℝ) * J.factorial) := by
    refine hxi'.trans ?_
    change _ ≤ C * X
    calc
      (1 / 2 : ℝ) * (‖z‖ + 1 / 2) ^ 2 *
          (Aθ * (B₀ ^ ((N + 1 : ℕ) : ℝ) * N.factorial)) + 1 / 2 ≤
          (Aθ / 2) * X + (1 / 2) * X := by
        exact add_le_add hmain
          (by simpa using
            (mul_le_mul_of_nonneg_left hX
              (show 0 ≤ (1 / 2 : ℝ) by norm_num)))
      _ = C * X := by dsimp [C]; ring
  have hJ : J ≤ K * 2 ^ m + K := by
    dsimp [J, N, K]
    omega
  refine henvelope.trans ?_
  simpa [A, mul_assoc] using
    (mul_rpow_factorial_le_exp_dyadic C B hC hB K m J hJ)

/-- The canonical xi-zero distribution, including inverse-square
summability, obtained unconditionally from the theta-kernel/Jensen route. -/
noncomputable def entireXiPullbackCanonicalZeroDistributionFromTheta :
    EntireXiPullbackCanonicalZeroDistribution :=
  entireXiPullbackThetaDyadicBoundaryGrowthData.toCanonicalZeroDistribution

end OverflowResidueRH
