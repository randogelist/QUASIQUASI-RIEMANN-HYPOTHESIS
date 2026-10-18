import Derivations.Geometry.CayleyChannelKernel
import Mathlib

namespace NativeSoloboloNegativity

open NativeSolobolo.Derivations.Geometry
open scoped BigOperators

noncomputable section

/-- The original literal Cayley channel is reused, not redefined spectrally. -/
abbrev channelQ := cayleyChannelQ

/-- A compact-anchor denominator estimate. -/
theorem CHANNEL_DENOMINATOR_LOWER_BOUND
    (a A : ℝ) (t : ℂ) (ha : 0 ≤ a) (haA : a ≤ A)
    (ht : 2 * A ≤ ‖t‖) :
    ‖t‖ / 2 ≤ ‖(a : ℂ) + t‖ := by
  have htri : ‖t‖ ≤ ‖(a : ℂ) + t‖ + a := by
    calc
      ‖t‖ = ‖((a : ℂ) + t) - (a : ℂ)‖ := by congr 1; ring
      _ ≤ ‖(a : ℂ) + t‖ + ‖(a : ℂ)‖ := norm_sub_le _ _
      _ = ‖(a : ℂ) + t‖ + a := by
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  linarith

/-- The explicit bound used for the infinite zero tail:
    0 <= a <= A and |t| >= 2A imply |q_a(t)| <= 16A/|t|. -/
theorem CAYLEY_CHANNEL_COMPACT_TAIL_BOUND
    (a A : ℝ) (t : ℂ) (ha : 0 ≤ a) (hA : 0 < A)
    (haA : a ≤ A) (ht : 2 * A ≤ ‖t‖) :
    ‖channelQ a t‖ ≤ 16 * A / ‖t‖ := by
  have htpos : 0 < ‖t‖ := by linarith
  have hd := CHANNEL_DENOMINATOR_LOWER_BOUND a A t ha haA ht
  have hdpos : 0 < ‖(a : ℂ) + t‖ := lt_of_lt_of_le (half_pos htpos) hd
  calc
    ‖channelQ a t‖ = (4 * a * ‖t‖) / ‖(a : ℂ) + t‖ ^ 2 := by
      simp [channelQ, cayleyChannelQ, norm_div, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ (4 * A * ‖t‖) / (‖t‖ / 2) ^ 2 := by
      gcongr
    _ = 16 * A / ‖t‖ := by
      field_simp [ne_of_gt htpos] <;> ring

/-- Pointwise power extraction. This is where a first-power summable envelope
    is converted to an all-depth geometric remainder. -/
theorem WEIGHTED_POWER_NORM_BOUND
    (w eta M : ℝ) (q : ℂ) (n : ℕ)
    (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hq : ‖q‖ ≤ eta) (hfirst : w * ‖q‖ ≤ M) :
    ‖(w : ℂ) * q ^ (n + 1)‖ ≤ M * eta ^ n := by
  have hp : ‖q‖ ^ n ≤ eta ^ n :=
    pow_le_pow_left₀ (norm_nonneg q) hq n
  calc
    ‖(w : ℂ) * q ^ (n + 1)‖ =
        (w * ‖q‖) * ‖q‖ ^ n := by
      simp only [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hw, pow_succ]
      ring
    _ ≤ M * eta ^ n :=
      mul_le_mul hfirst hp (pow_nonneg (norm_nonneg q) n) hM

/-- Absolute convergence and the exact bound B eta^n are both derived.
No conditional or divergent tsum is used as a spectral expansion. -/
theorem SUMMABLE_CHANNEL_POWER_REMAINDER_BOUND
    {ι : Type*} (w : ι → ℝ) (q : ι → ℂ) (M : ι → ℝ)
    (eta : ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hM : ∀ i, 0 ≤ M i)
    (hsum : Summable M)
    (hgap : ∀ i, ‖q i‖ ≤ eta)
    (hfirst : ∀ i, w i * ‖q i‖ ≤ M i) :
    Summable (fun i => (w i : ℂ) * q i ^ (n + 1)) ∧
      ‖∑' i, (w i : ℂ) * q i ^ (n + 1)‖ ≤
        (∑' i, M i) * eta ^ n := by
  have hmajor : Summable (fun i => M i * eta ^ n) := hsum.mul_right _
  have hpoint : ∀ i,
      ‖(w i : ℂ) * q i ^ (n + 1)‖ ≤ M i * eta ^ n := by
    intro i
    exact WEIGHTED_POWER_NORM_BOUND (w i) eta (M i) (q i) n
      (hw i) (hM i) (hgap i) (hfirst i)
  have htotal : HasSum (fun i => M i * eta ^ n)
      ((∑' i, M i) * eta ^ n) := by
    simpa only [tsum_mul_right] using hmajor.hasSum
  exact ⟨hmajor.of_norm_bounded hpoint, tsum_of_norm_bounded htotal hpoint⟩

/-- Conjugate phases contribute the same negative real power. -/
theorem CONJUGATE_CHANNEL_NEGATIVE_POWER
    (q : ℂ) (b : ℝ) (n : ℕ)
    (h : q ^ (n + 1) = -((b ^ (n + 1) : ℝ) : ℂ)) :
    (starRingEnd ℂ q) ^ (n + 1) = -((b ^ (n + 1) : ℝ) : ℂ) := by
  have hc := congrArg (starRingEnd ℂ) h
  simpa using hc

/-- A finite cluster with a common tuned phase reinforces, rather than cancels. -/
theorem FINITE_CLUSTER_REINFORCES
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (q : ι → ℂ)
    (b : ℝ) (n : ℕ)
    (hphase : ∀ i ∈ s, q i ^ (n + 1) = -((b ^ (n + 1) : ℝ) : ℂ)) :
    (∑ i ∈ s, (w i : ℂ) * q i ^ (n + 1)) =
      -(((∑ i ∈ s, w i) * b ^ (n + 1) : ℝ) : ℂ) := by
  calc
    (∑ i ∈ s, (w i : ℂ) * q i ^ (n + 1)) =
        ∑ i ∈ s, (w i : ℂ) * (-((b ^ (n + 1) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hphase i hi]
    _ = (∑ i ∈ s, (w i : ℂ)) * (-((b ^ (n + 1) : ℝ) : ℂ)) := by
      rw [Finset.sum_mul]
    _ = -(((∑ i ∈ s, w i) * b ^ (n + 1) : ℝ) : ℂ) := by
      push_cast
      ring

end
end NativeSoloboloNegativity
