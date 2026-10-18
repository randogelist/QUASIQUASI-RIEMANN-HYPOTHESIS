import AWPIRH.BernsteinTransform
import AWPIRH.RowAnalytic
import Mathlib.Data.Finset.NatAntidiagonal

/-!
Locally convergent Bernstein/binomial row transform.  Both the finite identity
and the exchange of the infinite sums are proved.  No subexponential-energy
assumption is needed for this LOCAL theorem: a positive local Taylor radius
already suffices.  No native coefficients are replaced by another sequence.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open Filter
namespace AWPIRH

/-- Pin the efficient Nat `HasAntidiagonal` instance explicitly, avoiding overload resolution
    with the order-theoretic `Finset.antidiagonal`. -/
private abbrev natAntidiagonal (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.HasAntidiagonal.antidiagonal (A := ℕ) N

/-- Unfolding the already fixed row sum; valid even outside convergence. -/
theorem rowAnalyticSum_eq_tsum (c : ℕ → ℂ) (η v : ℂ) :
    rowAnalyticSum c η v = ∑' N, rowPolynomial c N η * v^N := by
  unfold rowAnalyticSum rowSeries FormalMultilinearSeries.sum
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- Any scalar analytic germ has an exponential coefficient bound. -/
theorem scalar_coefficients_exponential_bound {c : ℕ → ℂ} {F : ℂ → ℂ}
    (hF : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ c) (0 : ℂ)) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ n, ‖c n‖ ≤ C * R^n := by
  obtain ⟨C, R, hC, hR, hc⟩ :=
    (FormalMultilinearSeries.ofScalars ℂ c).le_mul_pow_of_radius_pos hF.radius_pos
  refine ⟨C, R, hC, hR, ?_⟩
  intro n
  simpa only [FormalMultilinearSeries.ofScalars_norm] using hc n

/-- The double series indexed by moment index and geometric-series index. -/
def rowDoubleTerm (c : ℕ → ℂ) (η v : ℂ) (p : ℕ × ℕ) : ℂ :=
  ((p.1+p.2).choose p.1 : ℂ) * c p.1 * (η-1)^p.1 * v^(p.1+p.2)

theorem rowDoubleTerm_norm_bound {c : ℕ → ℂ} {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : ∀ n, ‖c n‖ ≤ C*R^n)
    (η v : ℂ) (k m : ℕ) :
    ‖rowDoubleTerm c η v (k,m)‖ ≤
      C * (2*R*‖η-1‖*‖v‖)^k * (2*‖v‖)^m := by
  have hchoose : (((k+m).choose k : ℕ) : ℝ) ≤ (2 : ℝ)^(k+m) := by
    exact_mod_cast choose_le_two_pow (k+m) k
  calc
    ‖rowDoubleTerm c η v (k,m)‖ =
        (((k+m).choose k : ℕ) : ℝ) * ‖c k‖ * ‖η-1‖^k * ‖v‖^(k+m) := by
      simp only [rowDoubleTerm, norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ (2 : ℝ)^(k+m) * (C*R^k) * ‖η-1‖^k * ‖v‖^(k+m) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hchoose (hc k) (norm_nonneg _) (by positivity))
          (pow_nonneg (norm_nonneg _) k))
        (pow_nonneg (norm_nonneg _) (k+m))
    _ = C * (2*R*‖η-1‖*‖v‖)^k * (2*‖v‖)^m := by
      simp only [pow_add, mul_pow]
      ring

/-- The exchange of sums is supported by a product-geometric majorant. -/
theorem rowDoubleTerm_summable {c : ℕ → ℂ} {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : ∀ n, ‖c n‖ ≤ C*R^n)
    {η v : ℂ} (h₁ : 2*R*‖η-1‖*‖v‖ < 1) (h₂ : 2*‖v‖ < 1) :
    Summable (rowDoubleTerm c η v) := by
  have hp : 0 ≤ 2*R*‖η-1‖*‖v‖ := by positivity
  have hq : 0 ≤ 2*‖v‖ := by positivity
  have hs₁ := summable_geometric_of_lt_one hp h₁
  have hs₂ := summable_geometric_of_lt_one hq h₂
  have hm : Summable (fun p : ℕ × ℕ =>
      C * ((2*R*‖η-1‖*‖v‖)^p.1 * (2*‖v‖)^p.2)) :=
    (hs₁.mul_of_nonneg hs₂ (fun n => pow_nonneg hp n)
      (fun n => pow_nonneg hq n)).mul_left C
  apply hm.of_norm_bounded
  intro p
  rcases p with ⟨k,m⟩
  simpa only [mul_assoc] using rowDoubleTerm_norm_bound hC hR hc η v k m

/-- Reorganize any summable two-index series into finite antidiagonals. -/
theorem tsum_antidiagonal_eq_tsum_prod {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    (∑' N, ∑ p ∈ natAntidiagonal N, f p) = ∑' p, f p := by
  have hs : Summable (fun p : Σ N : ℕ, ↥(natAntidiagonal N) => f p.2) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf
  calc
    (∑' N, ∑ p ∈ natAntidiagonal N, f p) =
        ∑' N, ∑' p : ↥(natAntidiagonal N), f p := by
      apply tsum_congr
      intro N
      rw [tsum_fintype, Finset.univ_eq_attach]
      exact (Finset.sum_attach (natAntidiagonal N) f).symm
    _ = ∑' p : Σ N : ℕ, ↥(natAntidiagonal N), f p.2 := hs.tsum_sigma.symm
    _ = ∑' p, f p :=
      Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f

/-- A finite antidiagonal gives exactly one original Bernstein row. -/
theorem rowDoubleTerm_antidiagonal (c : ℕ → ℂ) (η v : ℂ) (N : ℕ) :
    (∑ p ∈ natAntidiagonal N, rowDoubleTerm c η v p) =
      rowPolynomial c N η * v^N := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    rowPolynomial_eq_binomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ N := by
    have hklt := Finset.mem_range.mp hk
    omega
  have hsum : k + (N-k) = N := by omega
  simp only [rowDoubleTerm, hsum]

/-- Sum the inner geometric series using its exact binomial coefficients. -/
theorem rowDoubleTerm_inner_tsum (c : ℕ → ℂ) (η : ℂ) {v : ℂ}
    (hv : ‖v‖ < 1) (k : ℕ) :
    (∑' m, rowDoubleTerm c η v (k,m)) =
      (c k * (phaseMap η v)^k) / (1-v) := by
  have hd : (1 : ℂ)-v ≠ 0 := by
    intro he
    have hv1 : v = 1 := (sub_eq_zero.mp he).symm
    simpa [hv1] using hv
  have heq : (fun m => rowDoubleTerm c η v (k,m)) =
      (fun m => (c k * (η-1)^k * v^k) *
        (((m+k).choose k : ℂ) * v^m)) := by
    funext m
    dsimp [rowDoubleTerm]
    rw [Nat.add_comm k m, pow_add]
    ring
  rw [heq, tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one k hv]
  unfold phaseMap
  rw [div_pow, mul_pow, pow_succ]
  field_simp [hd]

/-- Exact row transform at every point satisfying the local geometric majorant. -/
theorem rowAnalyticSum_transform_at {c : ℕ → ℂ} {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : ∀ n, ‖c n‖ ≤ C*R^n)
    {η v : ℂ} (hv : ‖v‖ < 1)
    (h₁ : 2*R*‖η-1‖*‖v‖ < 1) (h₂ : 2*‖v‖ < 1) :
    rowAnalyticSum c η v = (∑' k, c k * (phaseMap η v)^k) / (1-v) := by
  have hs := rowDoubleTerm_summable hC hR hc h₁ h₂
  calc
    rowAnalyticSum c η v = ∑' N, rowPolynomial c N η * v^N :=
      rowAnalyticSum_eq_tsum c η v
    _ = ∑' N, ∑ p ∈ natAntidiagonal N, rowDoubleTerm c η v p := by
      apply tsum_congr
      intro N
      exact (rowDoubleTerm_antidiagonal c η v N).symm
    _ = ∑' p, rowDoubleTerm c η v p := tsum_antidiagonal_eq_tsum_prod hs
    _ = ∑' k, ∑' m, rowDoubleTerm c η v (k,m) := hs.tsum_prod
    _ = ∑' k, (c k * (phaseMap η v)^k) / (1-v) := by
      apply tsum_congr
      intro k
      exact rowDoubleTerm_inner_tsum c η hv k
    _ = (∑' k, c k * (phaseMap η v)^k) / (1-v) := tsum_div_const

/-- Main local transport theorem. No assumption about global energy growth. -/
theorem rowAnalyticSum_transform_eventually {c : ℕ → ℂ} {F : ℂ → ℂ}
    (hF : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ c) (0 : ℂ))
    (η : ℂ) :
    ∀ᶠ v in 𝓝 (0 : ℂ), rowAnalyticSum c η v = F (phaseMap η v) / (1-v) := by
  obtain ⟨C,R,hC,hR,hc⟩ := scalar_coefficients_exponential_bound hF
  have hmap : ContinuousAt (phaseMap η) (0 : ℂ) := by
    unfold phaseMap
    have hnum : ContinuousAt (fun v : ℂ => (η - 1) * v) 0 :=
      continuousAt_const.mul continuousAt_id
    have hden : ContinuousAt (fun v : ℂ => 1 - v) 0 :=
      continuousAt_const.sub continuousAt_id
    have hden0 : (1 - (0 : ℂ)) ≠ 0 := by norm_num
    exact hnum.div hden hden0
  have hmap₀ : Tendsto (phaseMap η) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [phaseMap_zero] using hmap.tendsto
  have hfs : ∀ᶠ r in 𝓝 (0 : ℂ), HasSum (fun k => c k * r^k) (F r) := by
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      using hF.eventually_hasSum
  have hv₁ : ∀ᶠ v : ℂ in 𝓝 0, ‖v‖ < 1 := by
    exact (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  have hv₂ : ∀ᶠ v : ℂ in 𝓝 0, 2*‖v‖ < 1 := by
    exact (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  have hv₃ : ∀ᶠ v : ℂ in 𝓝 0, 2*R*‖η-1‖*‖v‖ < 1 := by
    exact (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  filter_upwards [hv₁,hv₂,hv₃,hmap₀.eventually hfs] with v h1 h2 h3 hf
  rw [rowAnalyticSum_transform_at hC.le hR.le hc h1 h3 h2, hf.tsum_eq]

end AWPIRH
