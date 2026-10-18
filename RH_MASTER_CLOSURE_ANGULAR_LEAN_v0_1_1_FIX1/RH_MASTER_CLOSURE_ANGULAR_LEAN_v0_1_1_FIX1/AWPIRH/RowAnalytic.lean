import AWPIRH.BernsteinEnergy
import AWPIRH.PhaseGeometry

set_option autoImplicit false
noncomputable section
open scoped Topology NNReal ENNReal
open Filter
namespace AWPIRH

def rowSeries (c : ℕ → ℂ) (η : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun N => rowPolynomial c N η)

def rowAnalyticSum (c : ℕ → ℂ) (η : ℂ) : ℂ → ℂ := (rowSeries c η).sum

private theorem exp_mul_nat (x : ℝ) (n : ℕ) :
    Real.exp (x * (n : ℝ)) = (Real.exp x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, mul_add, mul_one, Real.exp_add, ih, pow_succ]

theorem rowSeries_radius_ge_one {c : ℕ → ℂ}
    (hUS : SubexponentialEnergy c) {η : ℂ} (hη : ‖η‖ ≤ 1) :
    (1 : ℝ≥0∞) ≤ (rowSeries c η).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  by_cases hz : r = 0
  · simp [hz]
  · have hr0 : (0 : ℝ) < (r : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hz : 0 < r)
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    let δ : ℝ := -Real.log (r : ℝ)
    have hδ : 0 < δ := neg_pos.mpr (Real.log_neg hr0 hr1)
    have hev := row_eventually_le_exp hUS hη hδ
    apply (rowSeries c η).le_radius_of_eventually_le (C := (1 : ℝ))
    filter_upwards [hev] with n hn
    have he : Real.exp δ * (r : ℝ) = 1 := by
      dsimp [δ]
      rw [Real.exp_neg, Real.exp_log hr0]
      exact inv_mul_cancel₀ (ne_of_gt hr0)
    have hpow : Real.exp (δ * (n : ℝ)) * (r : ℝ) ^ n = 1 := by
      rw [exp_mul_nat, ← mul_pow, he, one_pow]
    have hn' := mul_le_mul_of_nonneg_right hn (pow_nonneg (le_of_lt hr0) n)
    rw [hpow] at hn'
    simpa [rowSeries, FormalMultilinearSeries.ofScalars_norm] using hn'

theorem rowAnalyticSum_analyticOnNhd {c : ℕ → ℂ}
    (hUS : SubexponentialEnergy c) {η : ℂ} (hη : ‖η‖ ≤ 1) :
    AnalyticOnNhd ℂ (rowAnalyticSum c η) unitDisc := by
  intro v hv
  have hr := rowSeries_radius_ge_one hUS hη
  have hnorm : (‖v‖₊ : ℝ≥0∞) < 1 := by
    exact_mod_cast (unitDisc_iff v).mp hv
  have hmem : v ∈ Metric.eball (0 : ℂ) (rowSeries c η).radius := by
    rw [Metric.mem_eball, edist_nndist, nndist_zero_right]
    exact lt_of_lt_of_le hnorm hr
  exact (FormalMultilinearSeries.analyticOnNhd (p := rowSeries c η)) v hmem

/-- The implemented left-hand block of the requested forward theorem. -/
theorem US_AWPI_IMPLIES_ACTUAL_ROW_ANALYTIC (hUS : US_AWPI)
    {η : ℂ} (hη : ‖η‖ ≤ 1) :
    AnalyticOnNhd ℂ (rowAnalyticSum nativeCoefficients η) unitDisc :=
  rowAnalyticSum_analyticOnNhd hUS hη

end AWPIRH
