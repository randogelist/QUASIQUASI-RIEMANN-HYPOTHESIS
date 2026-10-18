import AWPIRH.NativeInput

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace AWPIRH

/-- Finite Cauchy--Schwarz, proved by a sum of squared pairwise differences. -/
theorem finite_sum_sq_bound (s : Finset ℕ) (x : ℕ → ℝ) :
    (∑ j ∈ s, x j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (x j) ^ 2 := by
  have h : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (x i - x j) ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul] at h
  nlinarith

theorem row_norm_sq_le_energy (c : ℕ → ℂ) (N : ℕ) {η : ℂ}
    (hη : ‖η‖ ≤ 1) : ‖rowPolynomial c N η‖ ^ 2 ≤ bernsteinEnergy c N := by
  have hnorm : ‖rowPolynomial c N η‖ ≤
      ∑ j ∈ Finset.range (N + 1), ‖bernsteinCell c N j‖ := by
    unfold rowPolynomial
    calc
      _ ≤ ∑ j ∈ Finset.range (N + 1), ‖bernsteinCell c N j * η ^ j‖ :=
        norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg η) hη)
  have hs := finite_sum_sq_bound (Finset.range (N + 1))
    (fun j => ‖bernsteinCell c N j‖)
  have hsum : 0 ≤ ∑ j ∈ Finset.range (N + 1), ‖bernsteinCell c N j‖ := by
    positivity
  have hrow := norm_nonneg (rowPolynomial c N η)
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at hs
  unfold bernsteinEnergy
  nlinarith

theorem row_norm_le_sqrt_energy (c : ℕ → ℂ) (N : ℕ) {η : ℂ}
    (hη : ‖η‖ ≤ 1) : ‖rowPolynomial c N η‖ ≤ Real.sqrt (bernsteinEnergy c N) := by
  have hs := row_norm_sq_le_energy c N hη
  have he := Real.sq_sqrt (bernsteinEnergy_nonneg c N)
  have hp := Real.sqrt_nonneg (bernsteinEnergy c N)
  nlinarith [norm_nonneg (rowPolynomial c N η)]

/-- The energy input alone gives an eventual arbitrarily small exponential bound. -/
theorem energy_eventually_le_exp {c : ℕ → ℂ}
    (hUS : SubexponentialEnergy c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, bernsteinEnergy c N ≤ Real.exp (ε * (N : ℝ)) := by
  have hlim : Tendsto
      (fun N : ℕ => Real.log (1 + bernsteinEnergy c N) / (N : ℝ))
      atTop (𝓝 0) := hUS
  have hev := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  have hNat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hNpos
  have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNat
  have hlog : Real.log (1 + bernsteinEnergy c N) < ε * (N : ℝ) :=
    (div_lt_iff₀ hpos).mp hN
  have hexp := Real.exp_lt_exp.mpr hlog
  have hone : 0 < 1 + bernsteinEnergy c N := by
    have := bernsteinEnergy_nonneg c N
    linarith
  rw [Real.exp_log hone] at hexp
  linarith

theorem row_eventually_le_exp {c : ℕ → ℂ}
    (hUS : SubexponentialEnergy c) {η : ℂ} (hη : ‖η‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ‖rowPolynomial c N η‖ ≤ Real.exp (δ * (N : ℝ)) := by
  have he := energy_eventually_le_exp hUS (show 0 < 2 * δ by positivity)
  filter_upwards [he] with N hN
  have hs := row_norm_sq_le_energy c N hη
  have hexp : Real.exp (2 * δ * (N : ℝ)) = (Real.exp (δ * (N : ℝ))) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hN
  nlinarith [Real.exp_pos (δ * (N : ℝ)), norm_nonneg (rowPolynomial c N η)]

end AWPIRH
