/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.CanonicalProductGrowth
import RiemannHypothesis.HadamardProduct.DyadicZeroCount

/-!
# Explicit dyadic growth of genus-one canonical products

A cumulative dyadic zero count of size `O(2^n n)` gives an explicit
`O(r (log r + 1)^2)` upper bound for the logarithmic norm of the genus-one
canonical product.  The one unavoidable datum not controlled by the
cumulative count is the reciprocal-norm mass of the finitely many low
dyadic bins: zeros may lie arbitrarily close to the origin.

The main result is stated on a dyadic scale.  If `1 ≤ K`, the count estimate
is valid from `K` onward, and `‖z‖ ≤ 2^K`, then the product norm is at most

`exp ((2 * lowMass + 20 * C + 14 * C₀) * ‖z‖ * (K + 1)^2)`.

No cancellation or symmetry of the divisor is used.  In particular, this is
an order-one logarithmic-square bound, not a finite-exponential-type bound.
-/

open Filter Metric Real Set Topology
open scoped Real

namespace OverflowResidueRH

/-- The reciprocal-norm mass in one exact dyadic bin. -/
noncomputable def hadamardZeroDyadicShellInvMass
    {ι : Type*} (zeroLoc : ι → ℂ) (n : Nat) : Real :=
  ∑' i : {i : ι // hadamardZeroDyadicBin zeroLoc i = n},
    ‖zeroLoc i.1‖⁻¹

/-- Each reciprocal-norm shell mass is nonnegative. -/
theorem hadamardZeroDyadicShellInvMass_nonneg
    {ι : Type*} (zeroLoc : ι → ℂ) (n : Nat) :
    0 ≤ hadamardZeroDyadicShellInvMass zeroLoc n :=
  tsum_nonneg fun _ ↦ by positivity

/-- The reciprocal-norm mass in the finitely many bins below `lower`. -/
noncomputable def hadamardZeroDyadicLowInvMass
    {ι : Type*} (zeroLoc : ι → ℂ) (lower : Nat) : Real :=
  ∑ n ∈ Finset.range lower, hadamardZeroDyadicShellInvMass zeroLoc n

/-- Norm properness makes the union of the dyadic bins below any fixed
threshold finite. -/
theorem hadamardZeroDyadicBelow_finite
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (lower : Nat) :
    {i : ι | hadamardZeroDyadicBin zeroLoc i < lower}.Finite := by
  refine (Hproper.finite_norm_le ((2 : Real) ^ lower)).subset ?_
  intro i hi
  exact (hadamardZero_norm_le_pow_two_dyadicBin zeroLoc i).trans
    (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) (Nat.le_of_lt hi))

/-- The finite low reciprocal mass is nonnegative. -/
theorem hadamardZeroDyadicLowInvMass_nonneg
    {ι : Type*} (zeroLoc : ι → ℂ) (lower : Nat) :
    0 ≤ hadamardZeroDyadicLowInvMass zeroLoc lower := by
  unfold hadamardZeroDyadicLowInvMass
  exact Finset.sum_nonneg fun n _ ↦
    hadamardZeroDyadicShellInvMass_nonneg zeroLoc n

/-- The reciprocal mass in a positive dyadic bin is bounded by the
cumulative count in the enclosing ball times the reciprocal of the
preceding dyadic radius. -/
theorem hadamardZeroDyadicShellInvMass_le_ballCard_mul
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (n : Nat) (hn : 1 ≤ n) :
    hadamardZeroDyadicShellInvMass zeroLoc n ≤
      (hadamardZeroDyadicBallCard zeroLoc n : Real) *
        ((2 : Real) ^ (n - 1))⁻¹ := by
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
  unfold hadamardZeroDyadicShellInvMass hadamardZeroDyadicBallCard
  rw [tsum_fintype]
  calc
    ∑ i : {i : ι // hadamardZeroDyadicBin zeroLoc i = n},
        ‖zeroLoc i.1‖⁻¹
        ≤ ∑ _i : {i : ι // hadamardZeroDyadicBin zeroLoc i = n},
            ((2 : Real) ^ (n - 1))⁻¹ := by
          apply Finset.sum_le_sum
          intro i _hi
          have hlower :=
            pow_two_pred_lt_norm_of_hadamardZeroDyadicBin_eq hn i.2
          have hpow_pos : 0 < (2 : Real) ^ (n - 1) := by positivity
          have hnorm_pos : 0 < ‖zeroLoc i.1‖ := lt_trans hpow_pos hlower
          exact (inv_le_inv₀ hnorm_pos hpow_pos).2 hlower.le
    _ = (Fintype.card
          {i : ι // hadamardZeroDyadicBin zeroLoc i = n} : Real) *
          ((2 : Real) ^ (n - 1))⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Nat.card
          {i : ι // hadamardZeroDyadicBin zeroLoc i = n} : Real) *
          ((2 : Real) ^ (n - 1))⁻¹ := by
        rw [Nat.card_eq_fintype_card]
    _ ≤ (Nat.card
          {i : ι // ‖zeroLoc i‖ ≤ (2 : Real) ^ n} : Real) *
          ((2 : Real) ^ (n - 1))⁻¹ := by
        gcongr

private lemma pow_two_mul_inv_pred_eq_of_pos (n : Nat) (hn : 1 ≤ n) :
    (2 : Real) ^ n * ((2 : Real) ^ (n - 1))⁻¹ = 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
  field_simp

private lemma inv_pow_two_pred_eq_of_pos (n : Nat) (hn : 1 ≤ n) :
    ((2 : Real) ^ (n - 1))⁻¹ = 2 * (1 / 2 : Real) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ, div_pow]
  field_simp
  simp

private lemma pow_two_mul_inv_sq_pred_eq_of_pos_explicit
    (n : Nat) (hn : 1 ≤ n) :
    (2 : Real) ^ n * ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) =
      4 * ((1 / 2 : Real) ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  norm_num [div_pow, pow_succ]
  field_simp
  norm_num

private lemma inv_sq_pow_two_pred_eq_of_pos_explicit
    (n : Nat) (hn : 1 ≤ n) :
    ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) =
      4 * ((1 / 4 : Real) ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  norm_num [div_pow, pow_succ]
  field_simp
  rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  rw [pow_two]

/-- The explicit reciprocal-mass bound forced by the cumulative dyadic
count in every bin where the count estimate is available. -/
theorem HadamardZeroDyadicCumulativeCountData.shellInvMass_le
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc)
    (n : Nat) (hn_one : 1 ≤ n) (hn_lower : H.lower ≤ n) :
    hadamardZeroDyadicShellInvMass zeroLoc n ≤
      2 * H.C * ((n + 1 : Nat) : Real) +
        2 * H.C₀ * (1 / 2 : Real) ^ n := by
  have hmass :=
    hadamardZeroDyadicShellInvMass_le_ballCard_mul H.normProper n hn_one
  have hcount := H.count_le n hn_lower
  have hinv_nonneg : 0 ≤ ((2 : Real) ^ (n - 1))⁻¹ := by positivity
  calc
    hadamardZeroDyadicShellInvMass zeroLoc n ≤
        (hadamardZeroDyadicBallCard zeroLoc n : Real) *
          ((2 : Real) ^ (n - 1))⁻¹ := hmass
    _ ≤ (H.C * ((n + 1 : Nat) : Real) * (2 : Real) ^ n + H.C₀) *
          ((2 : Real) ^ (n - 1))⁻¹ :=
      mul_le_mul_of_nonneg_right hcount hinv_nonneg
    _ = H.C * ((n + 1 : Nat) : Real) *
          ((2 : Real) ^ n * ((2 : Real) ^ (n - 1))⁻¹) +
        H.C₀ * ((2 : Real) ^ (n - 1))⁻¹ := by ring
    _ = H.C * ((n + 1 : Nat) : Real) * 2 +
        H.C₀ * (2 * (1 / 2 : Real) ^ n) := by
      rw [pow_two_mul_inv_pred_eq_of_pos n hn_one,
        inv_pow_two_pred_eq_of_pos n hn_one]
    _ = 2 * H.C * ((n + 1 : Nat) : Real) +
          2 * H.C₀ * (1 / 2 : Real) ^ n := by ring

/-- Public per-shell form of the inverse-square majorant used by the
summability bridge. -/
theorem HadamardZeroDyadicCumulativeCountData.shellInvSqMass_le
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc)
    (n : Nat) (hn_one : 1 ≤ n) (hn_lower : H.lower ≤ n) :
    hadamardZeroDyadicShellInvSqMass zeroLoc n ≤
      hadamardZeroDyadicInvSqMajorant H.C H.C₀ n := by
  have hmass :=
    hadamardZeroDyadicShellInvSqMass_le_ballCard_mul H.normProper n hn_one
  have hcount := H.count_le n hn_lower
  have hinv_nonneg : 0 ≤ ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := by positivity
  calc
    hadamardZeroDyadicShellInvSqMass zeroLoc n ≤
        (hadamardZeroDyadicBallCard zeroLoc n : Real) *
          ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := hmass
    _ ≤ (H.C * ((n + 1 : Nat) : Real) * (2 : Real) ^ n + H.C₀) *
          ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_right hcount hinv_nonneg
    _ = H.C * ((n + 1 : Nat) : Real) *
          ((2 : Real) ^ n * ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹)) +
        H.C₀ * ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) := by ring
    _ = H.C * ((n + 1 : Nat) : Real) *
          (4 * (1 / 2 : Real) ^ n) +
        H.C₀ * (4 * (1 / 4 : Real) ^ n) := by
      rw [pow_two_mul_inv_sq_pred_eq_of_pos_explicit n hn_one,
        inv_sq_pow_two_pred_eq_of_pos_explicit n hn_one]
    _ = hadamardZeroDyadicInvSqMajorant H.C H.C₀ n := by
      unfold hadamardZeroDyadicInvSqMajorant
      ring

/-! ## Finite heads and elementary geometric tails -/

/-- All occurrences in bins at most `K`, as a finite set. -/
noncomputable def hadamardZeroDyadicHeadFinset
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (K : Nat) : Finset ι :=
  (hadamardZeroDyadicBelow_finite Hproper (K + 1)).toFinset

@[simp] theorem mem_hadamardZeroDyadicHeadFinset
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (K : Nat) (i : ι) :
    i ∈ hadamardZeroDyadicHeadFinset Hproper K ↔
      hadamardZeroDyadicBin zeroLoc i ≤ K := by
  unfold hadamardZeroDyadicHeadFinset
  rw [Set.Finite.mem_toFinset]
  simp

private lemma hasSum_half_explicit :
    HasSum (fun j : Nat ↦ (1 / 2 : Real) ^ j) 2 := by
  have h :=
    hasSum_geometric_of_norm_lt_one (K := Real) (ξ := (1 / 2 : Real))
      (by norm_num)
  norm_num at h
  exact h

private lemma hasSum_nat_mul_half_explicit :
    HasSum (fun j : Nat ↦ (j : Real) * (1 / 2 : Real) ^ j) 2 := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := Real) (r := (1 / 2 : Real)) (by norm_num)
  norm_num at h
  exact h

private lemma hasSum_quarter_explicit :
    HasSum (fun j : Nat ↦ (1 / 4 : Real) ^ j) (4 / 3) := by
  have h :=
    hasSum_geometric_of_norm_lt_one (K := Real) (ξ := (1 / 4 : Real))
      (by norm_num)
  norm_num at h
  exact h

/-- Exact tail of the weighted half-geometric series. -/
theorem hasSum_hadamardDyadicWeightedHalf_tail (K : Nat) :
    HasSum
      (fun j : Nat ↦ (((K + 1 + j) + 1 : Nat) : Real) *
        (1 / 2 : Real) ^ (K + 1 + j))
      (((K + 3 : Nat) : Real) * (1 / 2 : Real) ^ K) := by
  have h := hasSum_nat_mul_half_explicit.add
    (hasSum_half_explicit.mul_left ((K + 2 : Nat) : Real))
  have hs := h.mul_left ((1 / 2 : Real) ^ (K + 1))
  have hvalue :
      (1 / 2 : Real) ^ (K + 1) * (2 + ((K + 2 : Nat) : Real) * 2) =
        ((K + 3 : Nat) : Real) * (1 / 2 : Real) ^ K := by
    push_cast
    rw [pow_succ]
    ring
  have hfun :
      (fun j : Nat ↦ (((K + 1 + j) + 1 : Nat) : Real) *
        (1 / 2 : Real) ^ (K + 1 + j)) =
      (fun j : Nat ↦ (1 / 2 : Real) ^ (K + 1) *
        ((j : Real) * (1 / 2 : Real) ^ j +
          ((K + 2 : Nat) : Real) * (1 / 2 : Real) ^ j)) := by
    funext j
    push_cast
    rw [pow_add]
    ring
  rw [hfun, ← hvalue]
  exact hs

/-- Exact tail of the quarter-geometric series. -/
theorem hasSum_hadamardDyadicQuarter_tail (K : Nat) :
    HasSum (fun j : Nat ↦ (1 / 4 : Real) ^ (K + 1 + j))
      ((1 / 3 : Real) * (1 / 4 : Real) ^ K) := by
  have hs := hasSum_quarter_explicit.mul_left ((1 / 4 : Real) ^ (K + 1))
  have hvalue :
      (1 / 4 : Real) ^ (K + 1) * (4 / 3) =
        (1 / 3 : Real) * (1 / 4 : Real) ^ K := by
    rw [pow_succ]
    ring
  have hfun :
      (fun j : Nat ↦ (1 / 4 : Real) ^ (K + 1 + j)) =
      (fun j : Nat ↦ (1 / 4 : Real) ^ (K + 1) *
        (1 / 4 : Real) ^ j) := by
    funext j
    rw [pow_add]
  rw [hfun, ← hvalue]
  exact hs

/-! ## Explicit head and tail masses -/

/-- A finite dyadic head is exactly the sum of its shell reciprocal masses. -/
theorem sum_hadamardZeroDyadicHead_inv_eq_sum_shellInvMass
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (K : Nat) :
    (∑ i ∈ hadamardZeroDyadicHeadFinset Hproper K, ‖zeroLoc i‖⁻¹) =
      ∑ n ∈ Finset.range (K + 1),
        hadamardZeroDyadicShellInvMass zeroLoc n := by
  classical
  let F := hadamardZeroDyadicHeadFinset Hproper K
  have hmaps : ∀ i ∈ F,
      hadamardZeroDyadicBin zeroLoc i ∈ Finset.range (K + 1) := by
    intro i hi
    rw [Finset.mem_range]
    have hi' : hadamardZeroDyadicBin zeroLoc i ≤ K := by
      simpa [F] using hi
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro n hn
  have hnK : n ≤ K := by
    rw [Finset.mem_range] at hn
    omega
  haveI : Fintype {i : ι // hadamardZeroDyadicBin zeroLoc i = n} :=
    (hadamardZeroDyadicBin_finite Hproper n).fintype
  unfold hadamardZeroDyadicShellInvMass
  rw [tsum_fintype]
  change (∑ i ∈ F with hadamardZeroDyadicBin zeroLoc i = n,
      ‖zeroLoc i‖⁻¹) =
    ∑ i : {i : ι // hadamardZeroDyadicBin zeroLoc i = n},
      ‖zeroLoc i.1‖⁻¹
  refine Finset.sum_bij
    (fun i hi ↦
      (⟨i, (Finset.mem_filter.1 hi).2⟩ :
        {i : ι // hadamardZeroDyadicBin zeroLoc i = n})) ?_ ?_ ?_ ?_
  · intro i hi
    simp
  · intro i₁ hi₁ i₂ hi₂ heq
    exact congrArg Subtype.val heq
  · intro j hj
    refine ⟨j.1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, j.2⟩
      rw [mem_hadamardZeroDyadicHeadFinset]
      simpa [j.2] using hnK
    · exact Subtype.ext (by rfl)
  · intro i hi
    rfl

/-- The reciprocal mass of a dyadic head is controlled by the exact finite
low-bin mass and a quadratic polynomial in the dyadic index. -/
theorem HadamardZeroDyadicCumulativeCountData.sum_head_inv_le
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc)
    (K : Nat) (hK_one : 1 ≤ K) (hK_lower : H.lower ≤ K) :
    (∑ i ∈ hadamardZeroDyadicHeadFinset H.normProper K,
        ‖zeroLoc i‖⁻¹) ≤
      hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
        ((K + 1 : Nat) : Real) *
          (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀) := by
  let L : Nat := max 1 H.lower
  have hL_one : 1 ≤ L := le_max_left _ _
  have hL_lower : H.lower ≤ L := le_max_right _ _
  have hLK : L ≤ K := max_le hK_one hK_lower
  have hLK1 : L ≤ K + 1 := hLK.trans (Nat.le_add_right K 1)
  rw [sum_hadamardZeroDyadicHead_inv_eq_sum_shellInvMass H.normProper K]
  have hhigh :
      (∑ n ∈ Finset.Ico L (K + 1),
          hadamardZeroDyadicShellInvMass zeroLoc n) ≤
        ((K + 1 : Nat) : Real) *
          (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀) := by
    calc
      (∑ n ∈ Finset.Ico L (K + 1),
          hadamardZeroDyadicShellInvMass zeroLoc n) ≤
          ∑ _n ∈ Finset.Ico L (K + 1),
            (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnL : L ≤ n := (Finset.mem_Ico.1 hn).1
        have hnK : n ≤ K := by
          have := (Finset.mem_Ico.1 hn).2
          omega
        have hshell := H.shellInvMass_le n
          (hL_one.trans hnL) (hL_lower.trans hnL)
        have hcast : ((n + 1 : Nat) : Real) ≤ ((K + 1 : Nat) : Real) := by
          exact_mod_cast Nat.add_le_add_right hnK 1
        have hpow : (1 / 2 : Real) ^ n ≤ 1 :=
          pow_le_one₀ (by norm_num) (by norm_num)
        have hCpart :
            2 * H.C * ((n + 1 : Nat) : Real) ≤
              2 * H.C * ((K + 1 : Nat) : Real) :=
          mul_le_mul_of_nonneg_left hcast
            (mul_nonneg (by norm_num) H.C_nonneg)
        have hC₀part :
            2 * H.C₀ * (1 / 2 : Real) ^ n ≤ 2 * H.C₀ := by
          calc
            2 * H.C₀ * (1 / 2 : Real) ^ n ≤ 2 * H.C₀ * 1 :=
              mul_le_mul_of_nonneg_left hpow
                (mul_nonneg (by norm_num) H.C₀_nonneg)
            _ = 2 * H.C₀ := by ring
        calc
          hadamardZeroDyadicShellInvMass zeroLoc n ≤
              2 * H.C * ((n + 1 : Nat) : Real) +
                2 * H.C₀ * (1 / 2 : Real) ^ n := hshell
          _ ≤ 2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀ :=
            add_le_add hCpart hC₀part
      _ = (((K + 1 - L : Nat) : Real)) *
          (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp
      _ ≤ ((K + 1 : Nat) : Real) *
          (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀) := by
        have hcast : (((K + 1 - L : Nat) : Real)) ≤
            ((K + 1 : Nat) : Real) := by
          exact_mod_cast Nat.sub_le (K + 1) L
        have hfactor :
            0 ≤ 2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀ :=
          add_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) H.C_nonneg) (by positivity))
            (mul_nonneg (by norm_num) H.C₀_nonneg)
        exact mul_le_mul_of_nonneg_right hcast hfactor
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n ↦ hadamardZeroDyadicShellInvMass zeroLoc n) hLK1
  calc
    (∑ n ∈ Finset.range (K + 1),
        hadamardZeroDyadicShellInvMass zeroLoc n) =
        hadamardZeroDyadicLowInvMass zeroLoc L +
          ∑ n ∈ Finset.Ico L (K + 1),
            hadamardZeroDyadicShellInvMass zeroLoc n := by
      unfold hadamardZeroDyadicLowInvMass
      exact hsplit.symm
    _ ≤ hadamardZeroDyadicLowInvMass zeroLoc L +
        ((K + 1 : Nat) : Real) *
          (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀) :=
      add_le_add_right hhigh _
    _ = hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
        ((K + 1 : Nat) : Real) *
          (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀) := by rfl

/-- The inverse-square mass beyond dyadic bin `K` has the exact geometric
tail bound forced by the cumulative count. -/
theorem HadamardZeroDyadicCumulativeCountData.tailInvSqMass_le
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc)
    (K : Nat) (hK_lower : H.lower ≤ K) :
    (∑' i : {i : ι // K < hadamardZeroDyadicBin zeroLoc i},
        (‖zeroLoc i.1‖ ^ 2)⁻¹) ≤
      4 * H.C * (((K + 3 : Nat) : Real) * (1 / 2 : Real) ^ K) +
        4 * H.C₀ * ((1 / 3 : Real) * (1 / 4 : Real) ^ K) := by
  let tail : Set ι := {i | K < hadamardZeroDyadicBin zeroLoc i}
  let f : tail → Real := fun i ↦ (‖zeroLoc i.1‖ ^ 2)⁻¹
  let g : tail → Nat :=
    fun i ↦ hadamardZeroDyadicBin zeroLoc i.1 - (K + 1)
  have hf : Summable f := by
    exact H.invSq_summable.subtype tail
  have hregroup := hf.hasSum.tsum_fiberwise g
  have hfiber_le : ∀ j : Nat,
      (∑' x : g ⁻¹' {j}, f x.1) ≤
        hadamardZeroDyadicShellInvSqMass zeroLoc (K + 1 + j) := by
    intro j
    let e : (g ⁻¹' {j}) →
        {i : ι // hadamardZeroDyadicBin zeroLoc i = K + 1 + j} :=
      fun x ↦ ⟨x.1.1, by
        have htail : K < hadamardZeroDyadicBin zeroLoc x.1.1 := x.1.2
        have hx := x.2
        change g x.1 = j at hx
        dsimp [g] at hx
        omega⟩
    have he : Function.Injective e := by
      intro x y hxy
      have hval : x.1.1 = y.1.1 := congrArg
        (fun w : {i : ι // hadamardZeroDyadicBin zeroLoc i = K + 1 + j} ↦ w.1)
        hxy
      have htail : x.1 = y.1 := Subtype.ext hval
      exact Subtype.ext htail
    have hsource : Summable (fun x : g ⁻¹' {j} ↦ f x.1) := hf.subtype _
    have htarget : Summable
        (fun i : {i : ι // hadamardZeroDyadicBin zeroLoc i = K + 1 + j} ↦
          (‖zeroLoc i.1‖ ^ 2)⁻¹) :=
      H.invSq_summable.subtype _
    unfold hadamardZeroDyadicShellInvSqMass
    exact Summable.tsum_le_tsum_of_inj e he
      (fun i _hi ↦ by positivity)
      (fun x ↦ by rfl) hsource htarget
  have hpoint : ∀ j : Nat,
      (∑' x : g ⁻¹' {j}, f x.1) ≤
        hadamardZeroDyadicInvSqMajorant H.C H.C₀ (K + 1 + j) := by
    intro j
    exact (hfiber_le j).trans
      (H.shellInvSqMass_le (K + 1 + j) (by omega) (by omega))
  have hmajorant : HasSum
      (fun j : Nat ↦
        hadamardZeroDyadicInvSqMajorant H.C H.C₀ (K + 1 + j))
      (4 * H.C * (((K + 3 : Nat) : Real) * (1 / 2 : Real) ^ K) +
        4 * H.C₀ * ((1 / 3 : Real) * (1 / 4 : Real) ^ K)) := by
    have h1 :=
      (hasSum_hadamardDyadicWeightedHalf_tail K).mul_left (4 * H.C)
    have h2 :=
      (hasSum_hadamardDyadicQuarter_tail K).mul_left (4 * H.C₀)
    have hfun :
        (fun j : Nat ↦
          hadamardZeroDyadicInvSqMajorant H.C H.C₀ (K + 1 + j)) =
        (fun j : Nat ↦
          4 * H.C * ((((K + 1 + j) + 1 : Nat) : Real) *
            (1 / 2 : Real) ^ (K + 1 + j)) +
          4 * H.C₀ * (1 / 4 : Real) ^ (K + 1 + j)) := by
      funext j
      unfold hadamardZeroDyadicInvSqMajorant
      ring
    rw [hfun]
    exact h1.add h2
  change (∑' i : tail, f i) ≤ _
  calc
    (∑' i : tail, f i) = ∑' j, ∑' x : g ⁻¹' {j}, f x.1 :=
      hregroup.tsum_eq.symm
    _ ≤ ∑' j, hadamardZeroDyadicInvSqMajorant H.C H.C₀ (K + 1 + j) :=
      hregroup.summable.tsum_le_tsum hpoint hmajorant.summable
    _ = _ := hmajorant.tsum_eq

/-! ## Canonical-product norm bounds -/

private theorem tsum_compl_hadamardZeroDyadicHead_eq_tail
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hproper : HadamardZeroNormProper zeroLoc) (K : Nat) :
    (∑' i : {i : ι // i ∉ hadamardZeroDyadicHeadFinset Hproper K},
        (‖zeroLoc i.1‖ ^ 2)⁻¹) =
      ∑' i : {i : ι // K < hadamardZeroDyadicBin zeroLoc i},
        (‖zeroLoc i.1‖ ^ 2)⁻¹ := by
  let e : {i : ι // i ∉ hadamardZeroDyadicHeadFinset Hproper K} ≃
      {i : ι // K < hadamardZeroDyadicBin zeroLoc i} := {
    toFun i := ⟨i.1, by
      rw [← Nat.not_le]
      simpa using i.2⟩
    invFun i := ⟨i.1, by
      rw [mem_hadamardZeroDyadicHeadFinset]
      exact Nat.not_le_of_lt i.2⟩
    left_inv i := Subtype.ext rfl
    right_inv i := Subtype.ext rfl }
  simpa [e] using
    (e.tsum_eq
      (fun i : {i : ι // K < hadamardZeroDyadicBin zeroLoc i} ↦
        (‖zeroLoc i.1‖ ^ 2)⁻¹))

/-- Fully explicit head-tail exponent bound for a genus-one canonical
product under a cumulative dyadic count.  This is the sharper result from
which the clean logarithmic-square estimate is derived. -/
theorem HadamardZeroDyadicCumulativeCountData.norm_infiniteHadamardProduct_le_exp_dyadic
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc)
    (K : Nat) (hK_one : 1 ≤ K) (hK_lower : H.lower ≤ K) (z : ℂ) :
    ‖infiniteHadamardProduct zeroLoc z‖ ≤
      Real.exp
        (2 * ‖z‖ *
            (hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
              ((K + 1 : Nat) : Real) *
                (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀)) +
          4 * ‖z‖ ^ 2 *
            (4 * H.C * (((K + 3 : Nat) : Real) * (1 / 2 : Real) ^ K) +
              4 * H.C₀ * ((1 / 3 : Real) * (1 / 4 : Real) ^ K))) := by
  classical
  let F := hadamardZeroDyadicHeadFinset H.normProper K
  have hsplit := norm_infiniteHadamardProduct_le_exp_split
    H.toHadamardZeroInvSqSummability F z
  have hhead_eq :
      (∑ i ∈ F, 2 * ‖z‖ / ‖zeroLoc i‖) =
        2 * ‖z‖ * ∑ i ∈ F, ‖zeroLoc i‖⁻¹ := by
    calc
      (∑ i ∈ F, 2 * ‖z‖ / ‖zeroLoc i‖) =
          ∑ i ∈ F, (2 * ‖z‖) * ‖zeroLoc i‖⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [div_eq_mul_inv]
      _ = 2 * ‖z‖ * ∑ i ∈ F, ‖zeroLoc i‖⁻¹ := by
        rw [Finset.mul_sum]
  have hhead := H.sum_head_inv_le K hK_one hK_lower
  have hhead' :
      (∑ i ∈ F, 2 * ‖z‖ / ‖zeroLoc i‖) ≤
        2 * ‖z‖ *
          (hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
            ((K + 1 : Nat) : Real) *
              (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀)) := by
    rw [hhead_eq]
    exact mul_le_mul_of_nonneg_left (by simpa [F] using hhead) (by positivity)
  have htail_eq :
      (∑' i : {i : ι // i ∉ F}, (‖zeroLoc i.1‖ ^ 2)⁻¹) =
        ∑' i : {i : ι // K < hadamardZeroDyadicBin zeroLoc i},
          (‖zeroLoc i.1‖ ^ 2)⁻¹ := by
    simpa [F] using
      tsum_compl_hadamardZeroDyadicHead_eq_tail H.normProper K
  have htail := H.tailInvSqMass_le K hK_lower
  have htail' :
      4 * ‖z‖ ^ 2 *
          (∑' i : {i : ι // i ∉ F}, (‖zeroLoc i.1‖ ^ 2)⁻¹) ≤
        4 * ‖z‖ ^ 2 *
          (4 * H.C * (((K + 3 : Nat) : Real) * (1 / 2 : Real) ^ K) +
            4 * H.C₀ * ((1 / 3 : Real) * (1 / 4 : Real) ^ K)) := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  apply hsplit.trans
  apply Real.exp_le_exp.mpr
  exact add_le_add hhead' htail'

private lemma sq_mul_half_pow_le_self
    (r : Real) (K : Nat) (hr0 : 0 ≤ r) (hr : r ≤ (2 : Real) ^ K) :
    r ^ 2 * (1 / 2 : Real) ^ K ≤ r := by
  have hpowpos : 0 < (2 : Real) ^ K := by positivity
  have hpow : (1 / 2 : Real) ^ K = ((2 : Real) ^ K)⁻¹ := by
    rw [div_pow]
    norm_num
  have hratio : r * ((2 : Real) ^ K)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hpowpos]
    simpa using hr
  rw [hpow]
  calc
    r ^ 2 * ((2 : Real) ^ K)⁻¹ =
        r * (r * ((2 : Real) ^ K)⁻¹) := by ring
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left hratio hr0
    _ = r := mul_one r

private lemma sq_mul_quarter_pow_le_self
    (r : Real) (K : Nat) (hr0 : 0 ≤ r) (hr : r ≤ (2 : Real) ^ K) :
    r ^ 2 * (1 / 4 : Real) ^ K ≤ r := by
  calc
    r ^ 2 * (1 / 4 : Real) ^ K ≤ r ^ 2 * (1 / 2 : Real) ^ K := by
      gcongr
      norm_num
    _ ≤ r := sq_mul_half_pow_le_self r K hr0 hr

private lemma dyadic_exponent_algebra
    (r low C C₀ k half quarter : Real)
    (hr0 : 0 ≤ r) (hlow : 0 ≤ low) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hk : 1 ≤ k)
    (hhalf : r ^ 2 * half ≤ r)
    (hquarter : r ^ 2 * quarter ≤ r) :
    2 * r * (low + (k + 1) * (2 * C * (k + 1) + 2 * C₀)) +
        4 * r ^ 2 *
          (4 * C * ((k + 3) * half) + 4 * C₀ * ((1 / 3) * quarter)) ≤
      (2 * low + 20 * C + 14 * C₀) * r * (k + 1) ^ 2 := by
  have hk3 : 0 ≤ k + 3 := by linarith
  have htailC :
      16 * C * (k + 3) * (r ^ 2 * half) ≤ 16 * C * (k + 3) * r :=
    mul_le_mul_of_nonneg_left hhalf (by positivity)
  have htailC₀ :
      (16 / 3) * C₀ * (r ^ 2 * quarter) ≤ (16 / 3) * C₀ * r :=
    mul_le_mul_of_nonneg_left hquarter (by positivity)
  have htail :
      4 * r ^ 2 *
          (4 * C * ((k + 3) * half) + 4 * C₀ * ((1 / 3) * quarter)) ≤
        16 * C * r * (k + 3) + (16 / 3) * C₀ * r := by
    calc
      4 * r ^ 2 *
          (4 * C * ((k + 3) * half) + 4 * C₀ * ((1 / 3) * quarter)) =
          16 * C * (k + 3) * (r ^ 2 * half) +
            (16 / 3) * C₀ * (r ^ 2 * quarter) := by ring
      _ ≤ 16 * C * (k + 3) * r + (16 / 3) * C₀ * r :=
        add_le_add htailC htailC₀
      _ = 16 * C * r * (k + 3) + (16 / 3) * C₀ * r := by ring
  have hsquare_one : 1 ≤ (k + 1) ^ 2 := by nlinarith
  have hlow_scaled : 2 * low * r ≤ 2 * low * r * (k + 1) ^ 2 := by
    have hcoef : 0 ≤ 2 * low * r := by positivity
    nlinarith
  have hk_poly : k + 3 ≤ (k + 1) ^ 2 := by nlinarith
  have hC_scaled :
      4 * C * r * (k + 1) ^ 2 + 16 * C * r * (k + 3) ≤
        20 * C * r * (k + 1) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hk_poly
      (by positivity : 0 ≤ 16 * C * r)
    nlinarith
  have hC₀_poly : 4 * (k + 1) + 16 / 3 ≤ 14 * (k + 1) ^ 2 := by
    nlinarith
  have hC₀_scaled :
      4 * C₀ * r * (k + 1) + (16 / 3) * C₀ * r ≤
        14 * C₀ * r * (k + 1) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hC₀_poly
      (mul_nonneg hC₀ hr0)
    nlinarith
  calc
    2 * r * (low + (k + 1) * (2 * C * (k + 1) + 2 * C₀)) +
        4 * r ^ 2 *
          (4 * C * ((k + 3) * half) + 4 * C₀ * ((1 / 3) * quarter)) ≤
        2 * r * (low + (k + 1) * (2 * C * (k + 1) + 2 * C₀)) +
          (16 * C * r * (k + 3) + (16 / 3) * C₀ * r) :=
      add_le_add le_rfl htail
    _ = 2 * low * r +
        (4 * C * r * (k + 1) ^ 2 + 16 * C * r * (k + 3)) +
        (4 * C₀ * r * (k + 1) + (16 / 3) * C₀ * r) := by ring
    _ ≤ 2 * low * r * (k + 1) ^ 2 +
        20 * C * r * (k + 1) ^ 2 +
        14 * C₀ * r * (k + 1) ^ 2 := by
      exact add_le_add (add_le_add hlow_scaled hC_scaled) hC₀_scaled
    _ = (2 * low + 20 * C + 14 * C₀) * r * (k + 1) ^ 2 := by ring

/-- Clean order-one logarithmic-square bound on a dyadic scale.  The
coefficient includes the exact finite reciprocal mass of the bins below
`max 1 lower`; no symmetry cancellation is assumed. -/
theorem HadamardZeroDyadicCumulativeCountData.norm_infiniteHadamardProduct_le_exp_logSq
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc)
    (K : Nat) (hK_one : 1 ≤ K) (hK_lower : H.lower ≤ K)
    (z : ℂ) (hz : ‖z‖ ≤ (2 : Real) ^ K) :
    ‖infiniteHadamardProduct zeroLoc z‖ ≤
      Real.exp
        ((2 * hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
            20 * H.C + 14 * H.C₀) *
          ‖z‖ * (((K + 1 : Nat) : Real) ^ 2)) := by
  have hraw :=
    H.norm_infiniteHadamardProduct_le_exp_dyadic K hK_one hK_lower z
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  let r : Real := ‖z‖
  let A : Real :=
    hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact hadamardZeroDyadicLowInvMass_nonneg _ _
  have hhalf : r ^ 2 * (1 / 2 : Real) ^ K ≤ r := by
    exact sq_mul_half_pow_le_self r K hr0 (by simpa [r] using hz)
  have hquarter : r ^ 2 * (1 / 4 : Real) ^ K ≤ r := by
    exact sq_mul_quarter_pow_le_self r K hr0 (by simpa [r] using hz)
  have hKcast : (1 : Real) ≤ (K : Real) := by exact_mod_cast hK_one
  change
    2 * r *
        (A + ((K + 1 : Nat) : Real) *
          (2 * H.C * ((K + 1 : Nat) : Real) + 2 * H.C₀)) +
      4 * r ^ 2 *
        (4 * H.C * (((K + 3 : Nat) : Real) * (1 / 2 : Real) ^ K) +
          4 * H.C₀ * ((1 / 3 : Real) * (1 / 4 : Real) ^ K)) ≤
      (2 * A + 20 * H.C + 14 * H.C₀) * r *
        (((K + 1 : Nat) : Real) ^ 2)
  convert dyadic_exponent_algebra r A H.C H.C₀ (K : Real)
      ((1 / 2 : Real) ^ K) ((1 / 4 : Real) ^ K)
      hr0 hA0 H.C_nonneg H.C₀_nonneg hKcast hhalf hquarter using 1 <;>
    norm_num [Nat.cast_add]

/-- Logarithmic-norm form of the explicit dyadic logarithmic-square bound. -/
theorem HadamardZeroDyadicCumulativeCountData.log_norm_infiniteHadamardProduct_le_logSq
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc)
    (K : Nat) (hK_one : 1 ≤ K) (hK_lower : H.lower ≤ K)
    (z : ℂ) (hz : ‖z‖ ≤ (2 : Real) ^ K) :
    Real.log ‖infiniteHadamardProduct zeroLoc z‖ ≤
      (2 * hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
          20 * H.C + 14 * H.C₀) *
        ‖z‖ * (((K + 1 : Nat) : Real) ^ 2) := by
  have hcoeff :
      0 ≤ 2 * hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
          20 * H.C + 14 * H.C₀ := by
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num)
          (hadamardZeroDyadicLowInvMass_nonneg zeroLoc (max 1 H.lower)))
        (mul_nonneg (by norm_num) H.C_nonneg))
      (mul_nonneg (by norm_num) H.C₀_nonneg)
  by_cases hp : infiniteHadamardProduct zeroLoc z = 0
  · rw [hp, norm_zero, Real.log_zero]
    positivity
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hp)).2
      (H.norm_infiniteHadamardProduct_le_exp_logSq
        K hK_one hK_lower z hz)

/-- Reusable package for dyadic logarithmic-square canonical-product growth. -/
structure HadamardCanonicalProductDyadicLogSqGrowthData
    {ι : Type*} (zeroLoc : ι → ℂ) : Type where
  lower : Nat
  coefficient : Real
  lower_one : 1 ≤ lower
  coefficient_nonneg : 0 ≤ coefficient
  norm_le : ∀ K : Nat, lower ≤ K → ∀ z : ℂ,
    ‖z‖ ≤ (2 : Real) ^ K →
      ‖infiniteHadamardProduct zeroLoc z‖ ≤
        Real.exp (coefficient * ‖z‖ * (((K + 1 : Nat) : Real) ^ 2))

/-- A cumulative dyadic count canonically supplies explicit
logarithmic-square canonical-product growth data. -/
noncomputable def HadamardZeroDyadicCumulativeCountData.toCanonicalProductDyadicLogSqGrowthData
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc) :
    HadamardCanonicalProductDyadicLogSqGrowthData zeroLoc where
  lower := max 1 H.lower
  coefficient :=
    2 * hadamardZeroDyadicLowInvMass zeroLoc (max 1 H.lower) +
      20 * H.C + 14 * H.C₀
  lower_one := le_max_left _ _
  coefficient_nonneg := by
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num)
          (hadamardZeroDyadicLowInvMass_nonneg zeroLoc (max 1 H.lower)))
        (mul_nonneg (by norm_num) H.C_nonneg))
      (mul_nonneg (by norm_num) H.C₀_nonneg)
  norm_le K hK z hz :=
    H.norm_infiniteHadamardProduct_le_exp_logSq K
      ((le_max_left 1 H.lower).trans hK)
      ((le_max_right 1 H.lower).trans hK) z hz

end OverflowResidueRH
