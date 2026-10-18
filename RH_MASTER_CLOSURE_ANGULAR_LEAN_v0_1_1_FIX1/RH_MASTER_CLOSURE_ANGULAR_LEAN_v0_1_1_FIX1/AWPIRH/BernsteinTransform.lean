import AWPIRH.NativeInput

/-!
Exact finite binomial transform of the ORIGINAL signed Bernstein rows.
This file has no convergence, positivity or native-identity input.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AWPIRH

/-- Reindex a cell by the coefficient index, rather than difference order. -/
theorem bernsteinCell_eq_Ico (c : ℕ → ℂ) (N j : ℕ) (hj : j ≤ N) :
    bernsteinCell c N j =
      ∑ m ∈ Finset.Ico j (N + 1),
        (N.choose m : ℂ) * (m.choose j : ℂ) * (-1 : ℂ) ^ (m-j) * c m := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : N + 1 - j = N - j + 1 := by omega
  rw [hlen]
  unfold bernsteinCell
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hchoose : (N.choose (j+k) : ℂ) * ((j+k).choose j : ℂ) =
      (N.choose j : ℂ) * ((N-j).choose k : ℂ) := by
    exact_mod_cast (show N.choose (j+k) * (j+k).choose j =
      N.choose j * (N-j).choose k by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul (n := N) (k := j+k) (s := j) (by omega)))
  rw [Nat.add_sub_cancel_left, hchoose]
  ring

/-- The complete original Bernstein row is exactly the binomial transform. -/
theorem rowPolynomial_eq_binomial (c : ℕ → ℂ) (N : ℕ) (η : ℂ) :
    rowPolynomial c N η =
      ∑ k ∈ Finset.range (N+1), (N.choose k : ℂ) * c k * (η-1)^k := by
  let F : ℕ → ℕ → ℂ := fun j m =>
    (N.choose m : ℂ) * (m.choose j : ℂ) * (-1 : ℂ)^(m-j) * c m * η^j
  have hfirst : rowPolynomial c N η =
      ∑ j ∈ Finset.Ico 0 (N+1), ∑ m ∈ Finset.Ico j (N+1), F j m := by
    rw [Nat.Ico_zero_eq_range]
    unfold rowPolynomial
    apply Finset.sum_congr rfl
    intro j hj
    rw [bernsteinCell_eq_Ico c N j (by
      have hjlt := Finset.mem_range.mp hj
      omega),
      Finset.sum_mul]
  rw [hfirst, Finset.sum_Ico_Ico_comm, Nat.Ico_zero_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.Ico_zero_eq_range]
  have hsum : (∑ j ∈ Finset.range (k+1), F j k) =
      (N.choose k : ℂ) * c k *
        ∑ j ∈ Finset.range (k+1), η^j * (-1 : ℂ)^(k-j) * (k.choose j : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F]
    ring
  rw [hsum, ← add_pow]
  simp only [sub_eq_add_neg]

/-- All cells sum to the zeroth coefficient, without a sign assumption. -/
theorem sum_bernsteinCell (c : ℕ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.range (N+1), bernsteinCell c N j) = c 0 := by
  calc
    (∑ j ∈ Finset.range (N+1), bernsteinCell c N j) =
        rowPolynomial c N (1 : ℂ) := by
          simp [rowPolynomial]
    _ = ∑ k ∈ Finset.range (N+1),
          (N.choose k : ℂ) * c k * ((1 : ℂ) - 1)^k :=
        rowPolynomial_eq_binomial c N (1 : ℂ)
    _ = (N.choose 0 : ℂ) * c 0 * ((1 : ℂ) - 1)^0 := by
        apply Finset.sum_eq_single 0
        · intro b hb hb0
          have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
          simp [hbpos.ne']
        · simp
    _ = c 0 := by simp

/-- A bound used only for a local, absolutely convergent double series. -/
theorem choose_le_two_pow (N k : ℕ) : N.choose k ≤ 2^N := by
  by_cases hk : k ≤ N
  · rw [← Nat.sum_range_choose N]
    exact Finset.single_le_sum (fun j hj => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

end AWPIRH
