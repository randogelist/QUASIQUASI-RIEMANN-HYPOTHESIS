import Merger02.SlitTransport

/-!
Actual zero placement, with the anchor and coefficient sequence unchanged.
The strict amplification is derived from the horizontal displacement itself.
-/
namespace Merger02
open Complex Filter
open scoped Topology

/-- Every actual off-line zero produces an interior denominator zero.
The final equality records which original zero is being transported. -/
theorem actual_offline_denominator_zero {rho : ℂ}
    (hzeta : NontrivialZero rho) (hOff : rho.re ≠ (1 / 2 : ℝ)) :
    ∃ z v : ℂ, ‖z‖ = 1 ∧ z ≠ 1 ∧ v ≠ 0 ∧ ‖v‖ < 1 ∧
      thetaMobius z v = 0 ∧ mobius z v ≠ 0 ∧
      mobius z v = (rho - (1 / 2 : ℂ)) ^ 2 := by
  let w : ℂ := rho - (1 / 2 : ℂ)
  let t : ℂ := -(w ^ 2)
  have hwre : w.re = rho.re - (1 / 2 : ℝ) := by simp [w]
  have hwre0 : w.re ≠ 0 := by rw [hwre]; exact sub_ne_zero.mpr hOff
  have hw0 : w ≠ 0 := by
    intro h
    apply hwre0
    simpa using congrArg Complex.re h
  have ht0 : t ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hw0)
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have httheta : theta (-t) = 0 := by
    simpa [t, w] using theta_zero_of_nontrivialZero hzeta
  have h1t : (1 : ℂ) + t ≠ 0 := by
    intro h
    have he : -t = (1 : ℂ) := by linear_combination -h
    apply theta_one_ne_zero
    rwa [he] at httheta
  have htnorm : ‖t‖ = ‖w‖ ^ 2 := by simp only [t, norm_neg, norm_pow]
  have hgap : (1 + ‖t‖) ^ 2 - ‖(1 : ℂ) + t‖ ^ 2 = 4 * w.re ^ 2 := by
    rw [htnorm, Complex.sq_norm w, Complex.sq_norm ((1 : ℂ) + t)]
    simp only [t, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
      pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hgapPos : 0 < 4 * w.re ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hwre0)
  have hstrict : ‖(1 : ℂ) + t‖ < 1 + ‖t‖ := by
    nlinarith [norm_nonneg ((1 : ℂ) + t), norm_nonneg t]
  let z : ℂ := t / (‖t‖ : ℂ)
  have htcast : (‖t‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
  have hznorm : ‖z‖ = 1 := by
    simp only [z, norm_div, Complex.norm_real, norm_norm]
    exact div_self htpos.ne'
  have hzsum : z + t = ((1 + ‖t‖ : ℝ) : ℂ) * z := by
    dsimp [z]
    push_cast
    field_simp [htcast]
  have hztNorm : ‖z + t‖ = 1 + ‖t‖ := by
    rw [hzsum, norm_mul, Complex.norm_of_nonneg (by positivity : 0 ≤ 1 + ‖t‖),
      hznorm, mul_one]
  have hzt0 : z + t ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hztNorm]
    positivity
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hztNorm
    linarith
  let v : ℂ := (1 + t) / (z + t)
  have hv0 : v ≠ 0 := div_ne_zero h1t hzt0
  have hvnorm : ‖v‖ < 1 := by
    rw [show ‖v‖ = ‖(1 : ℂ) + t‖ / ‖z + t‖ by exact norm_div _ _, hztNorm]
    exact (div_lt_one (by positivity : 0 < 1 + ‖t‖)).mpr hstrict
  have huv : mobius z v = -t := mobius_at_pole t z hzt0 hz1
  refine ⟨z, v, hznorm, hz1, hv0, hvnorm, ?_, ?_, ?_⟩
  · simpa only [thetaMobius, huv] using httheta
  · rw [huv]
    exact neg_ne_zero.mpr ht0
  · simpa only [t, w, neg_neg] using huv

/-- The selected multiplier is strictly expanding, without any pole-growth input. -/
theorem inverse_norm_gt_one {v : ℂ} (hv0 : v ≠ 0) (hv : ‖v‖ < 1) :
    1 < ‖v⁻¹‖ := by
  rw [norm_inv]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [inv_eq_one_div]
  exact (one_lt_div hvp).mpr hv

/-- Includes the actual finite zero order needed by the logarithmic-derivative pole.
No assumption of simple zeta zeros is used. -/
theorem actual_offline_positive_order {rho : ℂ}
    (hzeta : NontrivialZero rho) (hOff : rho.re ≠ (1 / 2 : ℝ)) :
    ∃ (z v : ℂ) (m : ℕ) (h : ℂ → ℂ),
      ‖z‖ = 1 ∧ z ≠ 1 ∧ v ≠ 0 ∧ ‖v‖ < 1 ∧ 1 < ‖v⁻¹‖ ∧
      0 < m ∧ AnalyticAt ℂ h v ∧ h v ≠ 0 ∧ mobius z v ≠ 0 ∧
      (∀ᶠ u in 𝓝 v, thetaMobius z u = (u - v) ^ m * h u) := by
  obtain ⟨z, v, hz, hz1, hv0, hv, hzero, hun, _⟩ :=
    actual_offline_denominator_zero hzeta hOff
  have hvball : v ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hv
  obtain ⟨m, h, hm, hh, hn, he⟩ := thetaMobius_zero_finite_order hz.le hvball hzero
  exact ⟨z, v, m, h, hz, hz1, hv0, hv, inverse_norm_gt_one hv0 hv,
    hm, hh, hn, hun, he⟩

end Merger02
