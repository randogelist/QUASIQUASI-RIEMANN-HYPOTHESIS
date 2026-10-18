import Mathlib

namespace NativeSoloboloNegativity

open Filter
open scoped Topology

/-- No asymptotic-rate guess: every eta<b is eventually dominated, with the
    constants A and B retained. -/
theorem GEOMETRIC_REMAINDER_EVENTUALLY_SMALLER
    (A B eta b : ℝ) (hA : 0 < A) (heta : 0 ≤ eta)
    (hb : 0 < b) (hgap : eta < b) :
    ∀ᶠ n : ℕ in atTop, B * eta ^ n < A * b ^ (n + 1) := by
  have hratio0 : 0 ≤ eta / b := div_nonneg heta hb.le
  have hratio1 : eta / b < 1 := (div_lt_one hb).2 hgap
  have hp : Tendsto (fun n : ℕ => (eta / b) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1
  have hlim : Tendsto (fun n : ℕ => B * (eta / b) ^ n) atTop (𝓝 0) := by
    simpa using hp.const_mul B
  have hev : ∀ᶠ n : ℕ in atTop, B * (eta / b) ^ n < A * b :=
    hlim.eventually (gt_mem_nhds (mul_pos hA hb))
  filter_upwards [hev] with n hn
  calc
    B * eta ^ n = (B * (eta / b) ^ n) * b ^ n := by
      rw [div_pow]
      field_simp [ne_of_gt hb] <;> ring
    _ < (A * b) * b ^ n := mul_lt_mul_of_pos_right hn (pow_pos hb n)
    _ = A * b ^ (n + 1) := by rw [pow_succ]; ring

/-- A finite negative cluster wins against the derived geometric remainder. -/
theorem NEGATIVE_CLUSTER_PLUS_REMAINDER_IS_EVENTUALLY_NEGATIVE
    (F amp : ℕ → ℝ) (A B eta b : ℝ)
    (hA : 0 < A) (heta : 0 ≤ eta) (hb : 0 < b) (hgap : eta < b)
    (hamp : ∀ᶠ n : ℕ in atTop, b ≤ amp n)
    (hbound : ∀ᶠ n : ℕ in atTop,
      F n ≤ -A * (amp n) ^ (n + 1) + B * eta ^ n) :
    ∀ᶠ n : ℕ in atTop, F n < 0 := by
  have hsmall := GEOMETRIC_REMAINDER_EVENTUALLY_SMALLER A B eta b hA heta hb hgap
  filter_upwards [hamp, hbound, hsmall] with n han hbn hsn
  have hp : b ^ (n + 1) ≤ (amp n) ^ (n + 1) :=
    pow_le_pow_left₀ hb.le han (n + 1)
  have hmul : A * b ^ (n + 1) ≤ A * (amp n) ^ (n + 1) :=
    mul_le_mul_of_nonneg_left hp hA.le
  linarith

/-- It is enough that the tuned moduli tend to a strict dominant maximum. -/
theorem NEGATIVE_CLUSTER_FROM_AMPLITUDE_LIMIT
    (F amp : ℕ → ℝ) (A B eta M : ℝ)
    (hA : 0 < A) (heta : 0 ≤ eta) (hgap : eta < M)
    (hlim : Tendsto amp atTop (𝓝 M))
    (hbound : ∀ᶠ n : ℕ in atTop,
      F n ≤ -A * (amp n) ^ (n + 1) + B * eta ^ n) :
    ∀ᶠ n : ℕ in atTop, F n < 0 := by
  let b : ℝ := (eta + M) / 2
  have heb : eta < b := by dsimp [b]; linarith
  have hbM : b < M := by dsimp [b]; linarith
  have hb : 0 < b := lt_of_le_of_lt heta heb
  have hamp : ∀ᶠ n : ℕ in atTop, b ≤ amp n := by
    filter_upwards [hlim.eventually (lt_mem_nhds hbM)] with n hn
    exact hn.le
  exact NEGATIVE_CLUSTER_PLUS_REMAINDER_IS_EVENTUALLY_NEGATIVE
    F amp A B eta b hA heta hb heb hamp hbound

end NativeSoloboloNegativity
