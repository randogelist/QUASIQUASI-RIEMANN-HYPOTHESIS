import GPHausdorff.Our.PassivityLedger

namespace GPHausdorff.Our

/-- Positivity of all Hausdorff certificates inside the finite triangle `n+k ≤ N`. -/
def FiniteHausdorffPositive (c : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ n k, n + k ≤ N → 0 ≤ hdiff c n k

/-- ! Global positivity gives every finite certificate triangle. -/
theorem finite_of_global {c : ℕ → ℝ} (h : HausdorffPositive c) (N : ℕ) :
    FiniteHausdorffPositive c N := by
  intro n k _
  exact h n k

/-- ! Finite certificate triangles are monotone in the cutoff. -/
theorem finite_mono {c : ℕ → ℝ} {M N : ℕ}
    (hMN : M ≤ N) (h : FiniteHausdorffPositive c N) :
    FiniteHausdorffPositive c M := by
  intro n k hnk
  exact h n k (le_trans hnk hMN)

/-- !!! The infinite Hausdorff frontier is exactly the conjunction of all finite certificate triangles. -/
theorem hausdorff_positive_iff_all_finite (c : ℕ → ℝ) :
    HausdorffPositive c ↔ ∀ N, FiniteHausdorffPositive c N := by
  constructor
  · intro h N
    exact finite_of_global h N
  · intro h n k
    exact h (n + k) n k (le_rfl)

/-- ! First Hausdorff difference certificate. -/
theorem hausdorff_first_difference {c : ℕ → ℝ}
    (h : HausdorffPositive c) (n : ℕ) :
    0 ≤ c n - c (n + 1) := by
  simpa [hdiff] using h n 1

/-- !! Second Hausdorff difference certificate. -/
theorem hausdorff_second_difference {c : ℕ → ℝ}
    (h : HausdorffPositive c) (n : ℕ) :
    0 ≤ c n - 2 * c (n + 1) + c (n + 2) := by
  have h2 := h n 2
  simp [hdiff, Nat.add_assoc] at h2
  linarith

end GPHausdorff.Our
