import Merger02.Actual

namespace Merger02
open scoped BigOperators

/-- The Cauchy--Schwarz envelope, at every finite depth. -/
theorem rowPolynomial_norm_sq_le_energy
    (s : ℕ → ℂ) (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖rowPolynomial s N z‖ ^ 2 ≤ energy s N := by
  -- Prove this before introducing finite-range membership: otherwise Lean
  -- generalizes that dependent hypothesis in the induction step.
  have hpow : ∀ j : ℕ, ‖z‖ ^ j ≤ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        calc
          ‖z‖ ^ j * ‖z‖ ≤ 1 * 1 :=
            mul_le_mul ih hz (norm_nonneg z) (by norm_num)
          _ = 1 := by norm_num
  have hnorm : ‖rowPolynomial s N z‖ ≤
      ∑ j ∈ Finset.range (N + 1), ‖row s N j‖ := by
    unfold rowPolynomial
    calc
      ‖∑ j ∈ Finset.range (N + 1), row s N j * z ^ j‖
          ≤ ∑ j ∈ Finset.range (N + 1), ‖row s N j * z ^ j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (N + 1), ‖row s N j‖ := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [norm_mul, norm_pow]
        simpa using mul_le_mul_of_nonneg_left (hpow j)
          (norm_nonneg (row s N j))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range (N + 1)) (fun j => ‖row s N j‖) (fun _ => (1 : ℝ))
  have hsq : (∑ j ∈ Finset.range (N + 1), ‖row s N j‖) ^ 2 ≤
      energy s N := by
    simpa [energy, mul_comm] using hcs
  have hsnonneg : 0 ≤ ∑ j ∈ Finset.range (N + 1), ‖row s N j‖ := by positivity
  nlinarith [norm_nonneg (rowPolynomial s N z)]

end Merger02
