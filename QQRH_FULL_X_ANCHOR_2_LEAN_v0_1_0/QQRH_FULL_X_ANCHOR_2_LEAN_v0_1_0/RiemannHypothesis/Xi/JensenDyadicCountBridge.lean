/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.JensenFormula
import RiemannHypothesis.Xi.CanonicalQuotientCriterion

/-!
# Jensen growth implies the canonical dyadic xi zero count

This file closes the formal handoff from a boundary growth estimate for the
*actual* entire xi pullback to the cumulative multiplicity count used by the
canonical Hadamard construction.

There are two points that must be handled carefully.

* Jensen's inequality counts the analytic divisor, whereas the Hadamard layer
  uses `EntireXiPullbackZeroOccurrence`, with one index for every unit of
  analytic multiplicity.  The theorem
  `entireXiPullbackZeroOccurrence_dyadicBallCard_le_divisor` constructs the
  required multiplicity-preserving injection and identifies the cardinal of
  its target with Mathlib's divisor sum.
* Jensen requires a nonzero center.  We use `I / 2`, where the pullback is
  exactly `1 / 2`.  The ball of radius `2 ^ n + 1` around this center contains
  the origin-centered ball of radius `2 ^ n`; applying Jensen on the doubled
  radius leaves the fixed denominator `log 2`.

Consequently, a dyadic order-one boundary estimate

`‖EntireXiPullback z‖ ≤ exp (A (n + 1) 2^n + A₀)`

on those doubled circles gives

`N(2^n) ≤ (A / log 2) (n + 1) 2^n + (A₀ / log 2 + 1)`.

No zero-counting hypothesis is used in this module.  The only undischarged
field is the displayed boundary growth estimate itself.  Proving that estimate
from the Mellin/theta representation of `completedRiemannZeta₀` is the exact
remaining analytic task on this route.
-/

open Metric Set

namespace OverflowResidueRH

/-! ## The fixed Jensen geometry -/

/-- A concrete nonzero center for Jensen's inequality.  It corresponds to
`s = 0` under `s = 1 / 2 + I * z`. -/
noncomputable def entireXiPullbackJensenCenter : ℂ := Complex.I / 2

/-- The inner Jensen radius used for dyadic bin `n`.  The additive `1`
absorbs the displacement of the center from the origin. -/
noncomputable def entireXiPullbackJensenInnerRadius (n : Nat) : Real :=
  (2 : Real) ^ n + 1

/-- The outer Jensen radius.  Its ratio to the inner radius is exactly `2`. -/
noncomputable def entireXiPullbackJensenOuterRadius (n : Nat) : Real :=
  2 * entireXiPullbackJensenInnerRadius n

/-- The xi pullback has the exact value `1 / 2` at the Jensen center. -/
theorem entireXiPullback_jensenCenter_value :
    EntireXiPullback entireXiPullbackJensenCenter = (1 / 2 : ℂ) := by
  exact EntireXiPullback_apply_I_div_two

/-- In particular, the fixed Jensen center is not a zero. -/
theorem entireXiPullback_jensenCenter_ne_zero :
    EntireXiPullback entireXiPullbackJensenCenter ≠ 0 := by
  rw [entireXiPullback_jensenCenter_value]
  norm_num

private theorem analyticOnNhd_entireXiPullback (s : Set ℂ) :
    AnalyticOnNhd ℂ EntireXiPullback s := by
  intro z _hz
  exact EntireXiPullback_analyticAt z

/-! ## Occurrence cardinal versus analytic divisor -/

/-- The multiplicity-bearing canonical occurrence count in the origin-centered
dyadic ball is bounded by the analytic divisor sum in the enlarged Jensen
ball.

The proof does not discard multiplicity: an occurrence `⟨ρ, k⟩` is sent to
the `k`-th element of the `Fin (analyticOrderNatAt ... ρ)` fiber over the
corresponding point of the divisor support. -/
theorem entireXiPullbackZeroOccurrence_dyadicBallCard_le_divisor
    (n : Nat) :
    (hadamardZeroDyadicBallCard
        entireXiPullbackZeroOccurrenceLoc n : Int) ≤
      ∑ᶠ z, MeromorphicOn.divisor EntireXiPullback
        (closedBall entireXiPullbackJensenCenter
          (entireXiPullbackJensenInnerRadius n)) z := by
  classical
  let r : Real := entireXiPullbackJensenInnerRadius n
  let B : Set ℂ := closedBall entireXiPullbackJensenCenter r
  let D := MeromorphicOn.divisor EntireXiPullback B
  have hAn : AnalyticOnNhd ℂ EntireXiPullback B :=
    analyticOnNhd_entireXiPullback B
  have hDfinite : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall entireXiPullbackJensenCenter r)
  letI : Fintype D.support := hDfinite.fintype
  let Target := Sigma fun z : D.support =>
    Fin (analyticOrderNatAt EntireXiPullback z.1)
  let Source := {i : EntireXiPullbackZeroOccurrence //
    ‖entireXiPullbackZeroOccurrenceLoc i‖ ≤ (2 : Real) ^ n}
  have hmem (i : Source) :
      entireXiPullbackZeroOccurrenceLoc i.1 ∈ B := by
    change dist (entireXiPullbackZeroOccurrenceLoc i.1)
      entireXiPullbackJensenCenter ≤ r
    calc
      dist (entireXiPullbackZeroOccurrenceLoc i.1)
          entireXiPullbackJensenCenter ≤
          dist (entireXiPullbackZeroOccurrenceLoc i.1) 0 +
            dist 0 entireXiPullbackJensenCenter :=
        dist_triangle _ _ _
      _ ≤ (2 : Real) ^ n + 1 := by
        have hc : dist (0 : ℂ) entireXiPullbackJensenCenter ≤ 1 := by
          unfold entireXiPullbackJensenCenter
          rw [dist_eq_norm]
          norm_num
        have hi : dist (entireXiPullbackZeroOccurrenceLoc i.1) 0 ≤
            (2 : Real) ^ n := by
          simpa [dist_eq_norm] using i.2
        linarith
      _ = r := rfl
  have hD_eq_nat (z : D.support) :
      D z.1 = (analyticOrderNatAt EntireXiPullback z.1 : Int) := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn
      (D.supportWithinDomain z.2)]
    rw [← Nat.cast_analyticOrderNatAt
      (entireXiPullback_analyticOrderAt_ne_top z.1)]
    simp
  have hsupp (i : Source) :
      entireXiPullbackZeroOccurrenceLoc i.1 ∈ D.support := by
    rw [Function.mem_support]
    rw [show D (entireXiPullbackZeroOccurrenceLoc i.1) =
        (analyticOrderNatAt EntireXiPullback
          (entireXiPullbackZeroOccurrenceLoc i.1) : Int) by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn (hmem i)]
      rw [← Nat.cast_analyticOrderNatAt
        (entireXiPullback_analyticOrderAt_ne_top
          (entireXiPullbackZeroOccurrenceLoc i.1))]
      simp]
    exact_mod_cast Nat.ne_of_gt
      (entireXiPullbackNonzeroZero_analyticOrderNatAt_pos i.1.1)
  let e : Source → Target := fun i =>
    ⟨⟨entireXiPullbackZeroOccurrenceLoc i.1, hsupp i⟩, i.1.2⟩
  have he : Function.Injective e := by
    intro i j hij
    have hz : entireXiPullbackZeroOccurrenceLoc i.1 =
        entireXiPullbackZeroOccurrenceLoc j.1 :=
      congrArg (fun x : Target => (x.1.1 : ℂ)) hij
    have hk : i.1.2.val = j.1.2.val :=
      congrArg (fun x : Target => x.2.val) hij
    apply Subtype.ext
    have hbase : i.1.1 = j.1.1 := Subtype.ext hz
    exact Sigma.ext hbase ((Fin.heq_ext_iff (by rw [hbase])).mpr hk)
  have hcard : Nat.card Source ≤ Nat.card Target :=
    Nat.card_le_card_of_injective e he
  have htarget : (Nat.card Target : Int) = ∑ᶠ z, D z := by
    rw [Nat.card_sigma]
    simp only [Nat.card_fin]
    push_cast
    rw [← finsum_eq_sum_of_fintype]
    simp_rw [← hD_eq_nat]
    rw [finsum_set_coe_eq_finsum_mem]
    exact finsum_mem_support D
  change (Nat.card Source : Int) ≤ ∑ᶠ z, D z
  rw [← htarget]
  exact_mod_cast hcard

/-- Real-cast form of the occurrence/divisor comparison, matching the output
type of `AnalyticOnNhd.sum_divisor_le`. -/
theorem entireXiPullbackZeroOccurrence_dyadicBallCard_le_divisor_real
    (n : Nat) :
    (hadamardZeroDyadicBallCard
        entireXiPullbackZeroOccurrenceLoc n : Real) ≤
      ((∑ᶠ z, MeromorphicOn.divisor EntireXiPullback
        (closedBall entireXiPullbackJensenCenter
          (entireXiPullbackJensenInnerRadius n)) z : Int) : Real) := by
  exact_mod_cast
    entireXiPullbackZeroOccurrence_dyadicBallCard_le_divisor n

/-! ## A generic strictly subquadratic geometric count -/

private lemma geometric_mul_inv_sq_pow_two_pred_eq
    (base : Real) (n : Nat) (hn : 1 ≤ n) :
    base ^ n * ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) =
      4 * (base / 4) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hfour : (4 : Real) ^ k = 2 ^ (k * 2) := by
    calc
      (4 : Real) ^ k = ((2 : Real) ^ 2) ^ k := by norm_num
      _ = 2 ^ (2 * k) := by rw [pow_mul]
      _ = 2 ^ (k * 2) := by rw [Nat.mul_comm]
  norm_num [pow_succ, div_pow]
  field_simp
  rw [hfour]
  ring

private lemma inv_sq_pow_two_pred_eq_geometric
    (n : Nat) (hn : 1 ≤ n) :
    ((((2 : Real) ^ (n - 1)) ^ 2)⁻¹) =
      4 * (1 / 4 : Real) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hfour : (4 : Real) ^ k = 2 ^ (k * 2) := by
    calc
      (4 : Real) ^ k = ((2 : Real) ^ 2) ^ k := by norm_num
      _ = 2 ^ (2 * k) := by rw [pow_mul]
      _ = 2 ^ (k * 2) := by rw [Nat.mul_comm]
  norm_num [pow_succ, div_pow]
  field_simp
  rw [hfour]
  ring

/-- A cumulative dyadic count with geometric base strictly below `4`.
At radius `R = 2^n`, a bound `C * base^n + C₀` with `base < 4`
is a fixed-power bound `O(R^α)` for `α < 2`.  This is the precise geometric
meaning of "strictly subquadratic" used here. -/
structure HadamardZeroDyadicGeometricCumulativeCountData
    {ι : Type*} (zeroLoc : ι → ℂ) : Type where
  zero_ne : ∀ i, zeroLoc i ≠ 0
  normProper : HadamardZeroNormProper zeroLoc
  lower : Nat
  base : Real
  C : Real
  C₀ : Real
  base_nonneg : 0 ≤ base
  base_lt_four : base < 4
  C_nonneg : 0 ≤ C
  C₀_nonneg : 0 ≤ C₀
  count_le : ∀ n : Nat, lower ≤ n →
    (hadamardZeroDyadicBallCard zeroLoc n : Real) ≤
      C * base ^ n + C₀

/-- The inverse-square shell majorant associated to a geometric cumulative
count. -/
noncomputable def hadamardZeroDyadicGeometricInvSqMajorant
    (C C₀ base : Real) (n : Nat) : Real :=
  4 * C * (base / 4) ^ n + 4 * C₀ * (1 / 4 : Real) ^ n

/-- The geometric shell majorant is summable exactly because `base / 4 < 1`. -/
theorem hadamardZeroDyadicGeometricInvSqMajorant_summable
    {C C₀ base : Real} (hbase0 : 0 ≤ base) (hbase4 : base < 4) :
    Summable (hadamardZeroDyadicGeometricInvSqMajorant C C₀ base) := by
  have hbase : Summable (fun n : Nat ↦ (base / 4) ^ n) :=
    summable_geometric_of_lt_one (div_nonneg hbase0 (by norm_num))
      ((div_lt_one (by norm_num : (0 : Real) < 4)).mpr hbase4)
  have hquarter : Summable (fun n : Nat ↦ (1 / 4 : Real) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  refine
    ((hbase.mul_left (4 * C)).add
      (hquarter.mul_left (4 * C₀))).congr ?_
  intro n
  simp [hadamardZeroDyadicGeometricInvSqMajorant]

/-- A strictly subquadratic geometric cumulative count makes the sequence of
dyadic inverse-square shell masses summable. -/
theorem HadamardZeroDyadicGeometricCumulativeCountData.shellInvSqMass_summable
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicGeometricCumulativeCountData zeroLoc) :
    Summable (hadamardZeroDyadicShellInvSqMass zeroLoc) := by
  let shift := H.lower + 1
  refine (summable_nat_add_iff shift).mp ?_
  refine Summable.of_nonneg_of_le
    (f := fun n ↦ hadamardZeroDyadicGeometricInvSqMajorant
      H.C H.C₀ H.base (n + shift))
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
      _ ≤ (H.C * H.base ^ (n + shift) + H.C₀) *
              ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right hcount hinv_nonneg
      _ = hadamardZeroDyadicGeometricInvSqMajorant
            H.C H.C₀ H.base (n + shift) := by
        calc
          (H.C * H.base ^ (n + shift) + H.C₀) *
                ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) =
              H.C * (H.base ^ (n + shift) *
                ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹)) +
              H.C₀ * ((((2 : Real) ^ (n + shift - 1)) ^ 2)⁻¹) := by
            ring
          _ = H.C * (4 * (H.base / 4) ^ (n + shift)) +
                H.C₀ * (4 * (1 / 4 : Real) ^ (n + shift)) := by
            rw [geometric_mul_inv_sq_pow_two_pred_eq
              H.base (n + shift) hm_one,
              inv_sq_pow_two_pred_eq_geometric (n + shift) hm_one]
          _ = hadamardZeroDyadicGeometricInvSqMajorant
                H.C H.C₀ H.base (n + shift) := by
            unfold hadamardZeroDyadicGeometricInvSqMajorant
            ring
  · exact
      (hadamardZeroDyadicGeometricInvSqMajorant_summable
        H.base_nonneg H.base_lt_four).comp_injective
          (fun _ _ h ↦ Nat.add_right_cancel h)

/-- A strictly subquadratic geometric cumulative count implies
inverse-square summability of all zero occurrences. -/
theorem HadamardZeroDyadicGeometricCumulativeCountData.invSq_summable
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicGeometricCumulativeCountData zeroLoc) :
    Summable fun i : ι ↦ (‖zeroLoc i‖ ^ 2)⁻¹ := by
  refine summable_of_nonneg_fiber_tsum_le
    (hadamardZeroDyadicBin zeroLoc) (fun _ ↦ by positivity)
    (hadamardZeroDyadicBin_finite H.normProper)
    H.shellInvSqMass_summable ?_
  intro n
  exact le_rfl

/-- The full generic Hadamard zero-summability package supplied by a strictly
subquadratic geometric count. -/
theorem
    HadamardZeroDyadicGeometricCumulativeCountData.toHadamardZeroInvSqSummability
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroDyadicGeometricCumulativeCountData zeroLoc) :
    HadamardZeroInvSqSummability zeroLoc :=
  HadamardZeroInvSqSummability.of_invSqSummable_normProper
    H.zero_ne H.invSq_summable H.normProper

/-! ## Boundary growth to cumulative dyadic count -/

/-- A dyadic order-one boundary-growth estimate for the actual xi pullback.
This is the natural output expected from the Mellin/theta representation.

It is deliberately a growth interface, not a zero-count interface: the
conversion to a multiplicity-weighted zero count is proved below by Jensen's
inequality. -/
structure EntireXiPullbackDyadicBoundaryGrowthData : Type where
  lower : Nat
  A : Real
  A₀ : Real
  A_nonneg : 0 ≤ A
  A₀_nonneg : 0 ≤ A₀
  boundary_norm_le : ∀ n : Nat, lower ≤ n →
    ∀ z ∈ sphere entireXiPullbackJensenCenter
      (entireXiPullbackJensenOuterRadius n),
      ‖EntireXiPullback z‖ ≤
        Real.exp (A * ((n + 1 : Nat) : Real) * (2 : Real) ^ n + A₀)

/-- Mathlib's Jensen inequality converts dyadic order-one boundary growth of
the actual xi pullback into the exact cumulative count structure used by the
canonical divisor.

The constants are explicit: `C = A / log 2` and
`C₀ = A₀ / log 2 + 1`.  The final `1` is the contribution of the exact center
value `‖EntireXiPullback (I / 2)‖ = 1 / 2`. -/
noncomputable def EntireXiPullbackDyadicBoundaryGrowthData.toDyadicCumulativeCountData
    (H : EntireXiPullbackDyadicBoundaryGrowthData) :
    EntireXiPullbackDyadicCumulativeCountData where
  lower := H.lower
  C := H.A / Real.log 2
  C₀ := H.A₀ / Real.log 2 + 1
  C_nonneg := div_nonneg H.A_nonneg (Real.log_nonneg (by norm_num))
  C₀_nonneg := add_nonneg
    (div_nonneg H.A₀_nonneg (Real.log_nonneg (by norm_num))) (by norm_num)
  count_le := by
    intro n hn
    let r : Real := entireXiPullbackJensenInnerRadius n
    let q : Real := H.A * ((n + 1 : Nat) : Real) * (2 : Real) ^ n + H.A₀
    have hr : 0 < r := by
      dsimp [r, entireXiPullbackJensenInnerRadius]
      positivity
    have hq : 0 ≤ q := by
      dsimp [q]
      exact add_nonneg
        (mul_nonneg (mul_nonneg H.A_nonneg (by positivity)) (by positivity))
        H.A₀_nonneg
    have houter : 0 < 2 * r := mul_pos (by norm_num) hr
    have hJraw := AnalyticOnNhd.sum_divisor_le
      (f := EntireXiPullback) (c := entireXiPullbackJensenCenter)
      (r := r) (R := 2 * r) (M := Real.exp q)
      (by simpa [abs_of_pos hr])
      (by rw [abs_of_pos hr, abs_of_pos houter]; linarith)
      (Real.one_le_exp hq)
      (analyticOnNhd_entireXiPullback _)
      entireXiPullback_jensenCenter_ne_zero
      (by
        intro z hz
        apply H.boundary_norm_le n hn z
        change z ∈ sphere entireXiPullbackJensenCenter (2 * r)
        rw [← abs_of_pos houter]
        exact hz)
    have hJ :
        (((∑ᶠ z, MeromorphicOn.divisor EntireXiPullback
          (closedBall entireXiPullbackJensenCenter r) z : Int) : Real)) ≤
          Real.log
              (Real.exp q / ‖EntireXiPullback entireXiPullbackJensenCenter‖) /
            Real.log ((2 * r) / r) := by
      rw [abs_of_pos hr] at hJraw
      exact hJraw
    have hocc :=
      entireXiPullbackZeroOccurrence_dyadicBallCard_le_divisor_real n
    change (hadamardZeroDyadicBallCard
      entireXiPullbackZeroOccurrenceLoc n : Real) ≤ _
    refine hocc.trans (hJ.trans ?_)
    have hnormcenter : ‖EntireXiPullback entireXiPullbackJensenCenter‖ =
        (1 / 2 : Real) := by
      rw [entireXiPullback_jensenCenter_value]
      norm_num
    have hratio : (2 * r) / r = (2 : Real) := by
      field_simp
    rw [hnormcenter, hratio]
    have hlogtwo : Real.log 2 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num))
    dsimp [q]
    rw [Real.log_div (Real.exp_pos _).ne'
      (by norm_num : (1 / 2 : Real) ≠ 0), Real.log_exp]
    rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
    field_simp
    ring_nf
    exact le_rfl

/-- Dyadic boundary growth therefore supplies inverse-square summability of
the exact multiplicity-bearing canonical xi divisor. -/
theorem EntireXiPullbackDyadicBoundaryGrowthData.toCanonicalZeroDistribution
    (H : EntireXiPullbackDyadicBoundaryGrowthData) :
    EntireXiPullbackCanonicalZeroDistribution :=
  H.toDyadicCumulativeCountData.toCanonicalZeroDistribution

/-- Fully generic Hadamard summability package obtained from the same actual-xi
boundary growth estimate. -/
theorem EntireXiPullbackDyadicBoundaryGrowthData.toHadamardZeroInvSqSummability
    (H : EntireXiPullbackDyadicBoundaryGrowthData) :
    HadamardZeroInvSqSummability entireXiPullbackZeroOccurrenceLoc :=
  H.toDyadicCumulativeCountData.toGeneric.toHadamardZeroInvSqSummability

/-! ## A broader strictly subquadratic logarithmic boundary envelope -/

/-- A fixed-rate strictly subquadratic bound on the boundary logarithm of the
actual xi pullback.  On dyadic radius `R = 2^n`, the bound is geometric with
base `base < 4`; equivalently it has a fixed power exponent strictly below
`2`.

This hypothesis is intentionally stronger than the bare little-oh statement
`log M(R) = o(R^2)`.  The latter alone does not force inverse-square divisor
summability: its dyadic shell majorant need not be summable. -/
structure EntireXiPullbackDyadicSubquadraticLogGrowthData : Type where
  lower : Nat
  base : Real
  A : Real
  A₀ : Real
  base_nonneg : 0 ≤ base
  base_lt_four : base < 4
  A_nonneg : 0 ≤ A
  A₀_nonneg : 0 ≤ A₀
  boundary_log_norm_le : ∀ n : Nat, lower ≤ n →
    ∀ z ∈ sphere entireXiPullbackJensenCenter
      (entireXiPullbackJensenOuterRadius n),
      Real.log ‖EntireXiPullback z‖ ≤ A * base ^ n + A₀

/-- Jensen converts a fixed-rate strictly subquadratic logarithmic boundary
bound into a geometric cumulative zero count with the same base. -/
noncomputable def
    EntireXiPullbackDyadicSubquadraticLogGrowthData.toGeometricCumulativeCountData
    (H : EntireXiPullbackDyadicSubquadraticLogGrowthData) :
    HadamardZeroDyadicGeometricCumulativeCountData
      entireXiPullbackZeroOccurrenceLoc where
  zero_ne := entireXiPullbackZeroOccurrenceLoc_ne_zero
  normProper := entireXiPullbackZeroOccurrenceNormProper
  lower := H.lower
  base := H.base
  C := H.A / Real.log 2
  C₀ := H.A₀ / Real.log 2 + 1
  base_nonneg := H.base_nonneg
  base_lt_four := H.base_lt_four
  C_nonneg := div_nonneg H.A_nonneg (Real.log_nonneg (by norm_num))
  C₀_nonneg := add_nonneg
    (div_nonneg H.A₀_nonneg (Real.log_nonneg (by norm_num))) (by norm_num)
  count_le := by
    intro n hn
    let r : Real := entireXiPullbackJensenInnerRadius n
    let q : Real := H.A * H.base ^ n + H.A₀
    have hr : 0 < r := by
      dsimp [r, entireXiPullbackJensenInnerRadius]
      positivity
    have hq : 0 ≤ q := by
      dsimp [q]
      exact add_nonneg
        (mul_nonneg H.A_nonneg (pow_nonneg H.base_nonneg n)) H.A₀_nonneg
    have houter : 0 < 2 * r := mul_pos (by norm_num) hr
    have hboundary : ∀ z ∈ sphere entireXiPullbackJensenCenter |2 * r|,
        ‖EntireXiPullback z‖ ≤ Real.exp q := by
      intro z hz
      have hzmem : z ∈ sphere entireXiPullbackJensenCenter
          (entireXiPullbackJensenOuterRadius n) := by
        change z ∈ sphere entireXiPullbackJensenCenter (2 * r)
        rw [← abs_of_pos houter]
        exact hz
      by_cases hzero : EntireXiPullback z = 0
      · simp [hzero, Real.exp_pos q |>.le]
      · have hnormpos : 0 < ‖EntireXiPullback z‖ := norm_pos_iff.mpr hzero
        calc
          ‖EntireXiPullback z‖ =
              Real.exp (Real.log ‖EntireXiPullback z‖) :=
            (Real.exp_log hnormpos).symm
          _ ≤ Real.exp q := Real.exp_le_exp.mpr
            (H.boundary_log_norm_le n hn z hzmem)
    have hJraw := AnalyticOnNhd.sum_divisor_le
      (f := EntireXiPullback) (c := entireXiPullbackJensenCenter)
      (r := r) (R := 2 * r) (M := Real.exp q)
      (by simpa [abs_of_pos hr])
      (by rw [abs_of_pos hr, abs_of_pos houter]; linarith)
      (Real.one_le_exp hq)
      (analyticOnNhd_entireXiPullback _)
      entireXiPullback_jensenCenter_ne_zero
      hboundary
    have hJ :
        (((∑ᶠ z, MeromorphicOn.divisor EntireXiPullback
          (closedBall entireXiPullbackJensenCenter r) z : Int) : Real)) ≤
          Real.log
              (Real.exp q / ‖EntireXiPullback entireXiPullbackJensenCenter‖) /
            Real.log ((2 * r) / r) := by
      rw [abs_of_pos hr] at hJraw
      exact hJraw
    have hocc :=
      entireXiPullbackZeroOccurrence_dyadicBallCard_le_divisor_real n
    refine hocc.trans (hJ.trans ?_)
    have hnormcenter : ‖EntireXiPullback entireXiPullbackJensenCenter‖ =
        (1 / 2 : Real) := by
      rw [entireXiPullback_jensenCenter_value]
      norm_num
    have hratio : (2 * r) / r = (2 : Real) := by
      field_simp
    rw [hnormcenter, hratio]
    have hlogtwo : Real.log 2 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num))
    dsimp [q]
    rw [Real.log_div (Real.exp_pos _).ne'
      (by norm_num : (1 / 2 : Real) ≠ 0), Real.log_exp]
    rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
    field_simp
    ring_nf
    exact le_rfl

/-- A fixed-rate strictly subquadratic logarithmic boundary bound on actual xi
supplies the canonical inverse-square zero distribution directly. -/
theorem
    EntireXiPullbackDyadicSubquadraticLogGrowthData.toCanonicalZeroDistribution
    (H : EntireXiPullbackDyadicSubquadraticLogGrowthData) :
    EntireXiPullbackCanonicalZeroDistribution :=
  ⟨H.toGeometricCumulativeCountData.invSq_summable⟩

/-- Generic Hadamard summability from the same actual-xi logarithmic boundary
estimate. -/
theorem
    EntireXiPullbackDyadicSubquadraticLogGrowthData.toHadamardZeroInvSqSummability
    (H : EntireXiPullbackDyadicSubquadraticLogGrowthData) :
    HadamardZeroInvSqSummability entireXiPullbackZeroOccurrenceLoc :=
  H.toGeometricCumulativeCountData.toHadamardZeroInvSqSummability

/-! ## Direct RH--Lagarias capstones -/

/-- Jensen boundary-growth capstone.  This removes the zero-count package from
the public hypotheses of the criterion: boundary growth of the actual xi
pullback supplies it internally by Jensen.  The only further input is
subquadratic growth of the automatically constructed quotient logarithm. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_jensenBoundaryGrowth_and_quotientLogGrowth
    (H : EntireXiPullbackDyadicBoundaryGrowthData)
    (hgrowth : HasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog
        H.toDyadicCumulativeCountData.toCanonicalZeroDistribution)) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_dyadicCount_and_quotientLogGrowth
    H.toDyadicCumulativeCountData hgrowth

/-- Witness-oriented Jensen boundary-growth capstone, accepting an explicit
entire logarithm of the canonical quotient. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_jensenBoundaryGrowth_explicitLogGrowth
    (H : EntireXiPullbackDyadicBoundaryGrowthData)
    (h : ℂ → ℂ) (hdiff : Differentiable ℂ h)
    (hexp : ∀ z : ℂ,
      Complex.exp (h z) = entireXiPullbackCanonicalQuotient z)
    (hgrowth : HasSubquadraticNormGrowth h) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_dyadicCount_explicitLogGrowth
    H.toDyadicCumulativeCountData h hdiff hexp hgrowth

/-- Strictly subquadratic actual-xi boundary-log capstone.  The boundary
estimate supplies divisor summability through Jensen; the displayed
quotient-log estimate is the remaining independent analytic input. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_subquadraticBoundaryLog
    (H : EntireXiPullbackDyadicSubquadraticLogGrowthData)
    (hgrowth : HasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog
        H.toCanonicalZeroDistribution)) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientGrowthData
    { zeroDistribution := H.toCanonicalZeroDistribution
      quotientLog_subquadratic := hgrowth }

/-- Witness-oriented form of the strictly subquadratic actual-xi boundary-log
capstone. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_subquadraticBoundaryLog_explicit
    (H : EntireXiPullbackDyadicSubquadraticLogGrowthData)
    (h : ℂ → ℂ) (hdiff : Differentiable ℂ h)
    (hexp : ∀ z : ℂ,
      Complex.exp (h z) = entireXiPullbackCanonicalQuotient z)
    (hgrowth : HasSubquadraticNormGrowth h) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_explicitCanonicalQuotientLogGrowthData
    { zeroDistribution := H.toCanonicalZeroDistribution
      quotientLog := h
      quotientLog_differentiable := hdiff
      exp_quotientLog_eq := hexp
      quotientLog_subquadratic := hgrowth }

end OverflowResidueRH
