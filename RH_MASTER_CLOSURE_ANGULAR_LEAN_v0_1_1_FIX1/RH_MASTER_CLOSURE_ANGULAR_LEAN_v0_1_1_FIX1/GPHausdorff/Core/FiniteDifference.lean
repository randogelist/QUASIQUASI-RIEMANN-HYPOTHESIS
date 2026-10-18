import Mathlib

namespace GPHausdorff

/-- `hdiff c n k` is the Hausdorff-signed forward difference
    `(-1)^k Δ^k c_n`, encoded recursively without signs. -/
def hdiff (c : ℕ → ℝ) : ℕ → ℕ → ℝ
  | n, 0 => c n
  | n, Nat.succ k => hdiff c n k - hdiff c (n + 1) k

/-- Complete Hausdorff finite-difference positivity. -/
def HausdorffPositive (c : ℕ → ℝ) : Prop :=
  ∀ n k, 0 ≤ hdiff c n k

@[simp] theorem hdiff_zero (c : ℕ → ℝ) (n : ℕ) :
    hdiff c n 0 = c n := rfl

@[simp] theorem hdiff_succ (c : ℕ → ℝ) (n k : ℕ) :
    hdiff c n (k + 1) = hdiff c n k - hdiff c (n + 1) k := by
  change hdiff c n (Nat.succ k) = _
  rfl

/-- Exact binary passivity/refinement identity:
    H(n,k) = H(n+1,k) + H(n,k+1). -/
theorem hdiff_split (c : ℕ → ℝ) (n k : ℕ) :
    hdiff c n k = hdiff c (n + 1) k + hdiff c n (k + 1) := by
  rw [hdiff_succ]
  ring

/-- A Hausdorff-positive sequence is pointwise nonnegative. -/
theorem hausdorff_c_nonneg {c : ℕ → ℝ} (h : HausdorffPositive c) (n : ℕ) :
    0 ≤ c n := by
  simpa [HausdorffPositive] using h n 0

/-- Both children in the binary refinement are nonnegative. -/
theorem hausdorff_split_nonneg {c : ℕ → ℝ} (h : HausdorffPositive c) (n k : ℕ) :
    0 ≤ hdiff c (n + 1) k ∧ 0 ≤ hdiff c n (k + 1) := by
  constructor
  · exact h (n + 1) k
  · exact h n (k + 1)

end GPHausdorff
