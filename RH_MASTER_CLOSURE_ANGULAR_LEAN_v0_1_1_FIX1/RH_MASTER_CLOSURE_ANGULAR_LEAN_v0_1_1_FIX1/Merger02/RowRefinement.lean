import Merger02.Envelope

/-!
All-depth degree elevation and variation bounds for the unchanged finite rows.
Everything in this module applies to any complex sequence. No measure,
positivity of cells, or growth assumption is used.
-/
namespace Merger02
open scoped BigOperators

noncomputable def differenceTerm (s : ℕ → ℂ) (k j r : ℕ) : ℂ :=
  (-1 : ℂ) ^ r * (k.choose r : ℂ) * s (j + r)

noncomputable def differenceSum (s : ℕ → ℂ) (k j : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (k + 1), differenceTerm s k j r

@[simp] theorem differenceTerm_zero (s : ℕ → ℂ) (k j : ℕ) :
    differenceTerm s k j 0 = s j := by
  simp [differenceTerm]

@[simp] theorem differenceTerm_last (s : ℕ → ℂ) (k j : ℕ) :
    differenceTerm s k j (k + 1) = 0 := by
  simp [differenceTerm]

theorem differenceTerm_pascal (s : ℕ → ℂ) (k j r : ℕ) :
    differenceTerm s (k + 1) j (r + 1) =
      -differenceTerm s k (j + 1) r + differenceTerm s k j (r + 1) := by
  unfold differenceTerm
  rw [Nat.choose_succ_succ']
  push_cast
  simp only [pow_succ]
  have hj : j + (r + 1) = (j + 1) + r := by omega
  rw [hj]
  ring

theorem differenceSum_succ (s : ℕ → ℂ) (k j : ℕ) :
    differenceSum s (k + 1) j =
      differenceSum s k j - differenceSum s k (j + 1) := by
  have hshift :
      (∑ r ∈ Finset.range (k + 1), differenceTerm s k j (r + 1)) + s j =
        differenceSum s k j := by
    calc
      _ = ∑ r ∈ Finset.range (k + 1 + 1), differenceTerm s k j r := by
        conv_rhs => rw [Finset.sum_range_succ']
        simp only [differenceTerm_zero]
      _ = differenceSum s k j := by
        rw [Finset.sum_range_succ]
        simp [differenceSum]
  calc
    differenceSum s (k + 1) j =
        (∑ r ∈ Finset.range (k + 1), differenceTerm s (k + 1) j (r + 1)) + s j := by
      unfold differenceSum
      rw [Finset.sum_range_succ']
      simp only [differenceTerm_zero]
    _ = (∑ r ∈ Finset.range (k + 1),
        (-differenceTerm s k (j + 1) r + differenceTerm s k j (r + 1))) + s j := by
      simp only [differenceTerm_pascal]
    _ = -differenceSum s k (j + 1) +
        ((∑ r ∈ Finset.range (k + 1), differenceTerm s k j (r + 1)) + s j) := by
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      unfold differenceSum
      ring
    _ = differenceSum s k j - differenceSum s k (j + 1) := by
      rw [hshift]
      ring

theorem row_eq_differenceSum (s : ℕ → ℂ) (N j : ℕ) :
    row s N j = (N.choose j : ℂ) * differenceSum s (N - j) j := rfl

/-- Cross-multiplied degree elevation. -/
theorem row_degree_elevation (s : ℕ → ℂ) (N j : ℕ) (hj : j ≤ N) :
    (N + 1 : ℂ) * row s N j =
      ((N + 1 - j : ℕ) : ℂ) * row s (N + 1) j +
        (j + 1 : ℂ) * row s (N + 1) (j + 1) := by
  have hk : N + 1 - j = (N - j) + 1 := by omega
  have hk' : N + 1 - (j + 1) = N - j := by omega
  have hleft : ((N + 1 - j : ℕ) : ℂ) * ((N + 1).choose j : ℂ) =
      (N + 1 : ℂ) * (N.choose j : ℂ) := by
    have hn : (N + 1 - j) * (N + 1).choose j = (N + 1) * N.choose j := by
      calc
        _ = (N + 1).choose j * (N + 1 - j) := mul_comm _ _
        _ = N.choose j * (N + 1) := (Nat.choose_mul_succ_eq N j).symm
        _ = (N + 1) * N.choose j := mul_comm _ _
    exact_mod_cast hn
  have hright : (j + 1 : ℂ) * ((N + 1).choose (j + 1) : ℂ) =
      (N + 1 : ℂ) * (N.choose j : ℂ) := by
    exact_mod_cast (mul_comm (j + 1) ((N + 1).choose (j + 1))).trans
      (Nat.add_one_mul_choose_eq N j).symm
  have hrow0 : row s N j = (N.choose j : ℂ) * differenceSum s (N - j) j := rfl
  have hrow1 : row s (N + 1) j = ((N + 1).choose j : ℂ) *
      (differenceSum s (N - j) j - differenceSum s (N - j) (j + 1)) := by
    rw [row_eq_differenceSum, hk, differenceSum_succ]
  have hrow2 : row s (N + 1) (j + 1) = ((N + 1).choose (j + 1) : ℂ) *
      differenceSum s (N - j) (j + 1) := by
    rw [row_eq_differenceSum, hk']
  rw [hrow0, hrow1, hrow2]
  calc
    _ = ((N + 1 : ℂ) * (N.choose j : ℂ)) * differenceSum s (N - j) j := by ring
    _ = (((N + 1 - j : ℕ) : ℂ) * ((N + 1).choose j : ℂ)) *
          (differenceSum s (N - j) j - differenceSum s (N - j) (j + 1)) +
        ((j + 1 : ℂ) * ((N + 1).choose (j + 1) : ℂ)) *
          differenceSum s (N - j) (j + 1) := by
      rw [hleft, hright]
      ring
    _ = _ := by ring

noncomputable def variation (s : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ‖row s N j‖

theorem variation_nonneg (s : ℕ → ℂ) (N : ℕ) : 0 ≤ variation s N := by
  unfold variation
  positivity

/-- Finite telescoping of the degree-elevation weights. -/
theorem elevation_weight_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      (((N + 1 - j : ℕ) : ℝ) * f j + (j + 1 : ℝ) * f (j + 1))) =
        (N + 1 : ℝ) * ∑ j ∈ Finset.range (N + 2), f j := by
  have hshift :
      (∑ j ∈ Finset.range (N + 1), (j + 1 : ℝ) * f (j + 1)) =
        (∑ j ∈ Finset.range (N + 1), (j : ℝ) * f j) +
          (N + 1 : ℝ) * f (N + 1) := by
    calc
      _ = ∑ j ∈ Finset.range (N + 2), (j : ℝ) * f j := by
        conv_rhs => rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ']
        simp
      _ = _ := by
        rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ = ∑ j ∈ Finset.range (N + 1),
        (((N + 1 : ℝ) - j) * f j + (j + 1 : ℝ) * f (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hle : j ≤ N + 1 := by simpa using (Nat.le_of_lt (Finset.mem_range.mp hj))
      rw [Nat.cast_sub hle]
      simp only [Nat.cast_add, Nat.cast_one]
    _ = (N + 1 : ℝ) * (∑ j ∈ Finset.range (N + 1), f j) -
          (∑ j ∈ Finset.range (N + 1), (j : ℝ) * f j) +
          (∑ j ∈ Finset.range (N + 1), (j + 1 : ℝ) * f (j + 1)) := by
      simp only [sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
    _ = (N + 1 : ℝ) * ∑ j ∈ Finset.range (N + 2), f j := by
      rw [hshift]
      conv_rhs => rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ]
      ring

theorem variation_step (s : ℕ → ℂ) (N : ℕ) :
    variation s N ≤ variation s (N + 1) := by
  have hrow : ∀ j ∈ Finset.range (N + 1),
      (N + 1 : ℝ) * ‖row s N j‖ ≤
        ((N + 1 - j : ℕ) : ℝ) * ‖row s (N + 1) j‖ +
          (j + 1 : ℝ) * ‖row s (N + 1) (j + 1)‖ := by
    intro j hj
    have hj' : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have he : ((N + 1 : ℕ) : ℂ) * row s N j =
        ((N + 1 - j : ℕ) : ℂ) * row s (N + 1) j +
        ((j + 1 : ℕ) : ℂ) * row s (N + 1) (j + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using row_degree_elevation s N j hj'
    have hn := norm_add_le
      (((N + 1 - j : ℕ) : ℂ) * row s (N + 1) j)
      (((j + 1 : ℕ) : ℂ) * row s (N + 1) (j + 1))
    rw [← he] at hn
    -- Remove norms of natural-number casts before expanding casts of sums.
    simp only [norm_mul, Complex.norm_natCast] at hn
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  have hsum := Finset.sum_le_sum hrow
  rw [← Finset.mul_sum, elevation_weight_sum] at hsum
  have hpos : 0 < (N + 1 : ℝ) := by positivity
  have hscaled : (N + 1 : ℝ) * variation s N ≤
      (N + 1 : ℝ) * variation s (N + 1) := by
    simpa only [variation, Nat.add_assoc] using hsum
  -- Cancel the positive scalar by strict-order contradiction.
  apply le_of_not_gt
  intro hlt
  exact (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_left hlt hpos)

theorem variation_monotone (s : ℕ → ℂ) : Monotone (variation s) :=
  monotone_nat_of_le_succ (variation_step s)

theorem variation_sq_le_energy (s : ℕ → ℂ) (N : ℕ) :
    (variation s N) ^ 2 ≤ energy s N := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range (N + 1)) (fun j => ‖row s N j‖) (fun _ => (1 : ℝ))
  simpa [variation, energy, mul_comm] using h

theorem rowPolynomial_norm_le_variation (s : ℕ → ℂ) (N : ℕ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖rowPolynomial s N z‖ ≤ variation s N := by
  have hp : ∀ j : ℕ, ‖z‖ ^ j ≤ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        simpa using mul_le_mul ih hz (norm_nonneg z) zero_le_one
  unfold rowPolynomial variation
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_pow]
  simpa using mul_le_mul_of_nonneg_left (hp j) (norm_nonneg (row s N j))

/-- Earlier rows are bounded using only the energy at the observed depth. -/
theorem earlier_rowPolynomial_norm_le_sqrt_energy (s : ℕ → ℂ)
    {n N : ℕ} (hn : n ≤ N) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖rowPolynomial s n z‖ ≤ Real.sqrt (energy s N) := by
  have hV := variation_nonneg s N
  have hsq := variation_sq_le_energy s N
  have hroot := Real.sqrt_nonneg (energy s N)
  have hid := Real.sq_sqrt (energy_nonneg s N)
  have hupper : variation s N ≤ Real.sqrt (energy s N) := by nlinarith
  exact (rowPolynomial_norm_le_variation s n hz).trans
    ((variation_monotone s hn).trans hupper)

end Merger02
