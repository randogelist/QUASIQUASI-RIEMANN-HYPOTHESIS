/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Data.Nat.Log
import RiemannHypothesis.HadamardProduct.LogDerivative

/-!
# Cumulative dyadic divisor counts imply inverse-square summability

Jensen's inequality naturally gives a cumulative radial count such as
`N(R) = O(R log R)`.  This is weaker than the unit-shell estimate
`N(R + 1) - N(R) = O(log R)` supplied by a Riemann--von Mangoldt theorem, but
it is already enough for the genus-one inverse-square sum.

This file makes that distinction formal.  It partitions a norm-proper zero
system into dyadic shells by

`Nat.clog 2 (Nat.ceil ‖rho‖)`.

If the cumulative multiplicity count in the ball of radius `2 ^ n` satisfies

`N(2 ^ n) ≤ C * (n + 1) * 2 ^ n + C₀`

eventually, then shell `n` has inverse-square mass at most

`4 * C * (n + 1) * 2⁻ⁿ + 4 * C₀ * 4⁻ⁿ`.

Both majorants are summable.  No Jensen estimate or completed-L-function
growth theorem is assumed here: the module isolates only the rigorous handoff
from a cumulative radial count to the canonical Hadamard input.
-/

open Metric Set

namespace OverflowResidueRH

/-! ## Generic dyadic partition -/

/-- The least dyadic exponent whose radius contains the zero occurrence.
The natural ceiling lets us use `Nat.clog` while retaining strict control of
the preceding dyadic radius. -/
noncomputable def hadamardZeroDyadicBin
    {ι : Type*} (zeroLoc : ι → ℂ) (i : ι) : Nat :=
  Nat.clog 2 (Nat.ceil ‖zeroLoc i‖)

/-- The cumulative number of occurrences in the closed norm ball of radius
`2 ^ n`.  Repeated locations are counted because the index type carries the
multiplicity. -/
noncomputable def hadamardZeroDyadicBallCard
    {ι : Type*} (zeroLoc : ι → ℂ) (n : Nat) : Nat :=
  Nat.card {i : ι // ‖zeroLoc i‖ ≤ (2 : Real) ^ n}

/-- The inverse-square mass in one exact dyadic bin. -/
noncomputable def hadamardZeroDyadicShellInvSqMass
    {ι : Type*} (zeroLoc : ι → ℂ) (n : Nat) : Real :=
  ∑' i : {i : ι // hadamardZeroDyadicBin zeroLoc i = n},
    (‖zeroLoc i.1‖ ^ 2)⁻¹

/-- Every occurrence in dyadic bin `n` lies in the ball of radius `2 ^ n`. -/
theorem hadamardZero_norm_le_pow_two_dyadicBin
    {ι : Type*} (zeroLoc : ι → ℂ) (i : ι) :
    ‖zeroLoc i‖ ≤ (2 : Real) ^ hadamardZeroDyadicBin zeroLoc i := by
  have h :=
    Nat.ceil_le.mp
      (Nat.le_pow_clog Nat.one_lt_two (Nat.ceil ‖zeroLoc i‖))
  exact_mod_cast h

/-- An occurrence in positive dyadic bin `n` lies strictly outside the
preceding dyadic radius `2 ^ (n - 1)`. -/
theorem pow_two_pred_lt_norm_of_hadamardZeroDyadicBin_eq
    {ι : Type*} {zeroLoc : ι → ℂ} {i : ι} {n : Nat}
    (hn : 1 ≤ n) (hi : hadamardZeroDyadicBin zeroLoc i = n) :
    (2 : Real) ^ (n - 1) < ‖zeroLoc i‖ := by
  have hceil_one : 1 < Nat.ceil ‖zeroLoc i‖ := by
    by_contra h
    have hle : Nat.ceil ‖zeroLoc i‖ ≤ 1 := Nat.le_of_not_gt h
    have hclog : hadamardZeroDyadicBin zeroLoc i = 0 := by
      unfold hadamardZeroDyadicBin
      exact Nat.clog_of_right_le_one hle 2
    omega
  have hp := Nat.pow_pred_clog_lt_self Nat.one_lt_two hceil_one
  unfold hadamardZeroDyadicBin at hi
  rw [hi] at hp
  simpa [Nat.pred_eq_sub_one] using Nat.lt_ceil.mp hp

/-- Norm properness makes every exact dyadic bin finite. -/
theorem hadamardZeroDyadicBin_finite
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (n : Nat) :
    {i : ι | hadamardZeroDyadicBin zeroLoc i = n}.Finite := by
  exact (Hproper.finite_norm_le ((2 : Real) ^ n)).subset (by
    intro i hi
    have h := hadamardZero_norm_le_pow_two_dyadicBin zeroLoc i
    rw [hi] at h
    exact h)

/-- Each dyadic inverse-square shell mass is nonnegative. -/
theorem hadamardZeroDyadicShellInvSqMass_nonneg
    {ι : Type*} (zeroLoc : ι → ℂ) (n : Nat) :
    0 ≤ hadamardZeroDyadicShellInvSqMass zeroLoc n :=
  tsum_nonneg fun _ ↦ by positivity

/-- The elementary dyadic ratio used for the `C * (n + 1) * 2 ^ n`
part of the cumulative count. -/
private lemma pow_two_mul_inv_sq_pred_eq (k : Nat) :
    (2 : Real) ^ (k + 1) * ((((2 : Real) ^ k) ^ 2)⁻¹) =
      4 * ((1 / 2 : Real) ^ (k + 1)) := by
  norm_num [div_pow, pow_succ]
  field_simp
  norm_num

/-- The elementary dyadic ratio used for the additive constant in the
cumulative count. -/
private lemma inv_sq_pow_two_eq (k : Nat) :
    ((((2 : Real) ^ k) ^ 2)⁻¹) =
      4 * ((1 / 4 : Real) ^ (k + 1)) := by
  norm_num [div_pow, pow_succ]
  field_simp
  rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  rw [pow_two]

private lemma pow_two_mul_inv_sq_pred_eq_of_pos
    (n : Nat) (hn : 1 ≤ n) :
    (2 : Real) ^ n * ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) =
      4 * ((1 / 2 : Real) ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [Nat.succ_eq_add_one] using pow_two_mul_inv_sq_pred_eq k

private lemma inv_sq_pow_two_pred_eq_of_pos
    (n : Nat) (hn : 1 ≤ n) :
    ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) =
      4 * ((1 / 4 : Real) ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [Nat.succ_eq_add_one] using inv_sq_pow_two_eq k

/-- The inverse-square mass in positive bin `n` is bounded by the cumulative
count in the radius-`2 ^ n` ball times the inverse square of the preceding
dyadic radius. -/
theorem hadamardZeroDyadicShellInvSqMass_le_ballCard_mul
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (n : Nat) (hn : 1 ≤ n) :
    hadamardZeroDyadicShellInvSqMass zeroLoc n ≤
      (hadamardZeroDyadicBallCard zeroLoc n : Real) *
        ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := by
  classical
  have hsub :
      {i : ι | hadamardZeroDyadicBin zeroLoc i = n} ⊆
        {i : ι | ‖zeroLoc i‖ ≤ (2 : Real) ^ n} := by
    intro i hi
    have h := hadamardZero_norm_le_pow_two_dyadicBin zeroLoc i
    rw [hi] at h
    exact h
  have hcard :
      Nat.card {i : ι // hadamardZeroDyadicBin zeroLoc i = n} ≤
        Nat.card {i : ι // ‖zeroLoc i‖ ≤ (2 : Real) ^ n} := by
    let f : {i : ι // hadamardZeroDyadicBin zeroLoc i = n} →
        {i : ι // ‖zeroLoc i‖ ≤ (2 : Real) ^ n} :=
      fun i ↦ ⟨i.1, hsub i.2⟩
    letI : Finite {i : ι // ‖zeroLoc i‖ ≤ (2 : Real) ^ n} :=
      Hproper.finite_norm_le ((2 : Real) ^ n)
    exact Nat.card_le_card_of_injective f (by
      intro i j hij
      apply Subtype.ext
      exact congrArg
        (fun x : {i : ι // ‖zeroLoc i‖ ≤ (2 : Real) ^ n} ↦ x.1) hij)
  haveI : Fintype {i : ι // hadamardZeroDyadicBin zeroLoc i = n} :=
    (hadamardZeroDyadicBin_finite Hproper n).fintype
  unfold hadamardZeroDyadicShellInvSqMass hadamardZeroDyadicBallCard
  rw [tsum_fintype]
  calc
    ∑ i : {i : ι // hadamardZeroDyadicBin zeroLoc i = n},
        (‖zeroLoc i.1‖ ^ 2)⁻¹
        ≤ ∑ _i : {i : ι // hadamardZeroDyadicBin zeroLoc i = n},
            ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := by
          apply Finset.sum_le_sum
          intro i _hi
          have hlower :=
            pow_two_pred_lt_norm_of_hadamardZeroDyadicBin_eq hn i.2
          have hpow_pos : 0 < (2 : Real) ^ (n - 1) := by positivity
          have hnorm_pos : 0 < ‖zeroLoc i.1‖ := lt_trans hpow_pos hlower
          apply
            (inv_le_inv₀ (sq_pos_of_pos hnorm_pos)
              (sq_pos_of_pos hpow_pos)).mpr
          nlinarith [hlower]
    _ = (Fintype.card
          {i : ι // hadamardZeroDyadicBin zeroLoc i = n} : Real) *
          ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Nat.card
          {i : ι // hadamardZeroDyadicBin zeroLoc i = n} : Real) *
          ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := by
        rw [Nat.card_eq_fintype_card]
    _ ≤ (Nat.card
          {i : ι // ‖zeroLoc i‖ ≤ (2 : Real) ^ n} : Real) *
          ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := by
        gcongr

/-! ## Cumulative dyadic count package -/

/-- Explicit data for an eventual cumulative `O(R log R)` count on dyadic
radii.  At `R = 2 ^ n`, the factor `(n + 1) * 2 ^ n` is the dyadic form of
`R log R`; `C₀` retains an additive error term instead of silently absorbing
it into the leading constant. -/
structure HadamardZeroDyadicCumulativeCountData
    {ι : Type*} (zeroLoc : ι → ℂ) : Type where
  zero_ne : ∀ i, zeroLoc i ≠ 0
  normProper : HadamardZeroNormProper zeroLoc
  lower : Nat
  C : Real
  C₀ : Real
  C_nonneg : 0 ≤ C
  C₀_nonneg : 0 ≤ C₀
  count_le : ∀ n : Nat, lower ≤ n →
    (hadamardZeroDyadicBallCard zeroLoc n : Real) ≤
      C * ((n + 1 : Nat) : Real) * (2 : Real) ^ n + C₀

/-- The summable per-bin majorant forced by a cumulative dyadic count. -/
noncomputable def hadamardZeroDyadicInvSqMajorant
    (C C₀ : Real) (n : Nat) : Real :=
  4 * C * ((n + 1 : Nat) : Real) * (1 / 2 : Real) ^ n +
    4 * C₀ * (1 / 4 : Real) ^ n

/-- The explicit dyadic inverse-square majorant is summable. -/
theorem hadamardZeroDyadicInvSqMajorant_summable (C C₀ : Real) :
    Summable (hadamardZeroDyadicInvSqMajorant C C₀) := by
  have hhalf :
      Summable (fun n : Nat ↦ (n : Real) * (1 / 2 : Real) ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (R := Real) 1
        (r := (1 / 2 : Real)) (by norm_num))
  have hhalf_succ :
      Summable
        (fun n : Nat ↦ ((n + 1 : Nat) : Real) * (1 / 2 : Real) ^ n) := by
    simpa [Nat.cast_add, add_mul] using hhalf.add summable_geometric_two
  have hquarter : Summable (fun n : Nat ↦ (1 / 4 : Real) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  refine
    ((hhalf_succ.mul_left (4 * C)).add
      (hquarter.mul_left (4 * C₀))).congr ?_
  intro n
  unfold hadamardZeroDyadicInvSqMajorant
  ring

/-- An eventual cumulative `O(R log R)` dyadic count makes the sequence of
dyadic inverse-square shell masses summable.  Finitely many bins below the
explicit threshold `lower + 1` are harmless. -/
theorem HadamardZeroDyadicCumulativeCountData.shellInvSqMass_summable
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc) :
    Summable (hadamardZeroDyadicShellInvSqMass zeroLoc) := by
  let shift := H.lower + 1
  refine (summable_nat_add_iff shift).mp ?_
  refine Summable.of_nonneg_of_le
    (f := fun n ↦ hadamardZeroDyadicInvSqMajorant H.C H.C₀ (n + shift))
    (g := fun n ↦ hadamardZeroDyadicShellInvSqMass zeroLoc (n + shift))
    (fun n ↦ hadamardZeroDyadicShellInvSqMass_nonneg zeroLoc (n + shift)) ?_ ?_
  · intro n
    have hm_one : 1 ≤ n + shift := by
      dsimp [shift]
      omega
    have hm_lower : H.lower ≤ n + shift := by
      dsimp [shift]
      omega
    have hmass :=
      hadamardZeroDyadicShellInvSqMass_le_ballCard_mul
        H.normProper (n + shift) hm_one
    have hcount := H.count_le (n + shift) hm_lower
    have hinv_nonneg :
        0 ≤ ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) := by positivity
    calc
      hadamardZeroDyadicShellInvSqMass zeroLoc (n + shift)
          ≤ (hadamardZeroDyadicBallCard zeroLoc (n + shift) : Real) *
              ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) := hmass
      _ ≤ (H.C * (((n + shift) + 1 : Nat) : Real) *
              (2 : Real) ^ (n + shift) + H.C₀) *
              ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right hcount hinv_nonneg
      _ = hadamardZeroDyadicInvSqMajorant H.C H.C₀ (n + shift) := by
          unfold hadamardZeroDyadicInvSqMajorant
          have hratio :=
            pow_two_mul_inv_sq_pred_eq_of_pos (n + shift) hm_one
          have hratio₀ :=
            inv_sq_pow_two_pred_eq_of_pos (n + shift) hm_one
          calc
            (H.C * (((n + shift) + 1 : Nat) : Real) *
                (2 : Real) ^ (n + shift) + H.C₀) *
                ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) =
                H.C * (((n + shift) + 1 : Nat) : Real) *
                    ((2 : Real) ^ (n + shift) *
                      ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹)) +
                  H.C₀ *
                    ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) := by
                      ring
            _ = 4 * H.C * (((n + shift) + 1 : Nat) : Real) *
                  (1 / 2 : Real) ^ (n + shift) +
                4 * H.C₀ * (1 / 4 : Real) ^ (n + shift) := by
                    rw [hratio, hratio₀]
                    ring
  · exact
      (hadamardZeroDyadicInvSqMajorant_summable H.C H.C₀).comp_injective
        (fun _ _ h ↦ Nat.add_right_cancel h)

/-- A cumulative dyadic `O(R log R)` count implies inverse-square
summability of all zero occurrences. -/
theorem HadamardZeroDyadicCumulativeCountData.invSq_summable
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc) :
    Summable fun i : ι ↦ (‖zeroLoc i‖ ^ 2)⁻¹ := by
  refine summable_of_nonneg_fiber_tsum_le
    (hadamardZeroDyadicBin zeroLoc) (fun _ ↦ by positivity)
    (hadamardZeroDyadicBin_finite H.normProper)
    H.shellInvSqMass_summable ?_
  intro n
  exact le_rfl

/-- A cumulative dyadic `O(R log R)` count supplies the full generic
Hadamard zero-summability package, including cofinite escape. -/
theorem HadamardZeroDyadicCumulativeCountData.toHadamardZeroInvSqSummability
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc) :
    HadamardZeroInvSqSummability zeroLoc :=
  HadamardZeroInvSqSummability.of_invSqSummable_normProper
    H.zero_ne H.invSq_summable H.normProper

end OverflowResidueRH
