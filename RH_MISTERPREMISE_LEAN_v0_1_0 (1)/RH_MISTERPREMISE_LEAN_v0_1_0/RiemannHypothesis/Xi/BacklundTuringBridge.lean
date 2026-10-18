/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.Xi.CanonicalDivisor

/-!
# Backlund--Turing zero counts and the canonical xi divisor

This file is the multiplicity-aware handoff from a Backlund--Turing or
Riemann--von Mangoldt zero-counting theorem to the inverse-square summability
required by the canonical logarithmic-derivative criterion.

The input is an eventual logarithmic bound for the number of canonical
occurrences in each norm-ceiling shell.  Occurrences, rather than distinct
zeros, are counted, so analytic multiplicity is preserved exactly.  The proof
then bounds the inverse-square mass of shell `n` by its cardinality times
`(n - 1)⁻²` and sums the resulting `log n / n²` majorant.

This bridge does not assert a concrete Backlund--Turing theorem.  It identifies
the exact output that the zero-counting layer must provide; in particular, it
does not address the separate punctured logarithmic-derivative expansion.
-/

namespace OverflowResidueRH

/-- The number of multiplicity-bearing nonzero pullback-zero occurrences in
the norm-ceiling shell `Nat.ceil ‖ρ‖ = n`. -/
noncomputable def entireXiPullbackCanonicalShellCard (n : Nat) : Nat :=
  Nat.card {i : EntireXiPullbackZeroOccurrence //
    Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n}

/-- The inverse-square mass in the multiplicity-bearing norm-ceiling shell
`Nat.ceil ‖ρ‖ = n`. -/
noncomputable def entireXiPullbackCanonicalShellInvSqMass (n : Nat) : Real :=
  ∑' i : {i : EntireXiPullbackZeroOccurrence //
      Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n},
    (‖entireXiPullbackZeroOccurrenceLoc i‖ ^ 2)⁻¹

/-- Every norm-ceiling shell of canonical occurrences is finite. -/
theorem entireXiPullbackCanonicalNormCeilFiberFinite (n : Nat) :
    {i : EntireXiPullbackZeroOccurrence |
      Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n}.Finite := by
  exact
    (entireXiPullbackZeroOccurrenceNormProper.finite_norm_le (n : Real)).subset (by
      intro i hi
      have hceil :
          Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ ≤ n := by
        rw [hi]
      exact Nat.le_of_ceil_le hceil)

/-- A canonical occurrence in shell `n` has norm strictly larger than the
previous integer radius. -/
theorem entireXiPullbackCanonicalNormCeilFiber_pred_lt_norm
    {i : EntireXiPullbackZeroOccurrence} {n : Nat}
    (hn : 1 ≤ n)
    (hi : Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n) :
    (((n - 1 : Nat) : Real) < ‖entireXiPullbackZeroOccurrenceLoc i‖) := by
  have hpred_lt_ceil :
      n - 1 < Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ := by
    rw [hi]
    omega
  exact Nat.lt_ceil.mp hpred_lt_ceil

/-- In shell `n ≥ 2`, each inverse-square contribution is at most
`(n - 1)⁻²`. -/
theorem entireXiPullbackCanonicalNormCeilFiber_invSq_le_pred
    {i : EntireXiPullbackZeroOccurrence} {n : Nat}
    (hn : 2 ≤ n)
    (hi : Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n) :
    (‖entireXiPullbackZeroOccurrenceLoc i‖ ^ 2)⁻¹
      ≤ ((((n - 1 : Nat) : Real) ^ 2)⁻¹) := by
  have hpred_lt_norm :
      ((n - 1 : Nat) : Real) < ‖entireXiPullbackZeroOccurrenceLoc i‖ :=
    entireXiPullbackCanonicalNormCeilFiber_pred_lt_norm
      (le_trans (by norm_num : 1 ≤ 2) hn) hi
  have hpred_pos : 0 < ((n - 1 : Nat) : Real) := by
    have h1n : 1 < n := lt_of_lt_of_le (by norm_num : 1 < 2) hn
    exact_mod_cast Nat.sub_pos_of_lt h1n
  have hnorm_pos : 0 < ‖entireXiPullbackZeroOccurrenceLoc i‖ :=
    lt_trans hpred_pos hpred_lt_norm
  have hsquares :
      ((n - 1 : Nat) : Real) ^ 2
        ≤ ‖entireXiPullbackZeroOccurrenceLoc i‖ ^ 2 := by
    nlinarith [hpred_lt_norm, hpred_pos]
  exact
    (inv_le_inv₀
      (sq_pos_of_pos hnorm_pos)
      (sq_pos_of_pos hpred_pos)).mpr hsquares

/-- Canonical shell inverse-square mass is nonnegative. -/
theorem entireXiPullbackCanonicalShellInvSqMass_nonneg (n : Nat) :
    0 ≤ entireXiPullbackCanonicalShellInvSqMass n :=
  tsum_nonneg fun _ => by positivity

/-- Shell inverse-square mass is bounded by shell cardinality times the
inverse square of its inner integer radius. -/
theorem entireXiPullbackCanonicalShellInvSqMass_le_card_mul
    (n : Nat) (hn : 2 ≤ n) :
    entireXiPullbackCanonicalShellInvSqMass n
      ≤ (entireXiPullbackCanonicalShellCard n : Real) *
          ((((n - 1 : Nat) : Real) ^ 2)⁻¹) := by
  classical
  unfold entireXiPullbackCanonicalShellInvSqMass
    entireXiPullbackCanonicalShellCard
  haveI : Fintype {i : EntireXiPullbackZeroOccurrence //
      Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n} :=
    (entireXiPullbackCanonicalNormCeilFiberFinite n).fintype
  rw [tsum_fintype, Nat.card_eq_fintype_card]
  calc
    ∑ i : {i : EntireXiPullbackZeroOccurrence //
        Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n},
        (‖entireXiPullbackZeroOccurrenceLoc i‖ ^ 2)⁻¹
      ≤ ∑ _i : {i : EntireXiPullbackZeroOccurrence //
          Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n},
          ((((n - 1 : Nat) : Real) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact entireXiPullbackCanonicalNormCeilFiber_invSq_le_pred hn i.2
    _ = (Fintype.card {i : EntireXiPullbackZeroOccurrence //
          Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n} : Real) *
            ((((n - 1 : Nat) : Real) ^ 2)⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- An eventual logarithmic annular occurrence-count bound makes the shell
inverse-square masses summable.  The finitely many shells below `lower` are
absorbed by `summable_nat_add_iff`. -/
theorem
    entireXiPullbackCanonicalShellInvSqMass_summable_of_eventual_shellCard_log_bound
    (lower : Nat) (hlower : 2 ≤ lower) (C C₀ : Real)
    (hcount : ∀ n : Nat, lower ≤ n →
      (entireXiPullbackCanonicalShellCard n : Real) ≤
        C * Real.log n + C₀) :
    Summable entireXiPullbackCanonicalShellInvSqMass := by
  refine (summable_nat_add_iff lower).mp ?_
  have hb : Summable (fun n : Nat => ((((n - 1 : Nat) : Real) ^ 2)⁻¹)) := by
    have hp : Summable (fun n : Nat => (((n : Real) ^ 2)⁻¹)) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    refine (summable_nat_add_iff 1).mp (hp.congr ?_)
    intro n
    norm_num
  have hbig :
      Summable (fun n : Nat =>
        C * (Real.log n * ((((n - 1 : Nat) : Real) ^ 2)⁻¹)) +
          C₀ * ((((n - 1 : Nat) : Real) ^ 2)⁻¹)) :=
    (summable_log_natCast_mul_pred_sq_inv.mul_left C).add (hb.mul_left C₀)
  have hbig_shift := (summable_nat_add_iff lower).mpr hbig
  refine Summable.of_nonneg_of_le
    (fun n => entireXiPullbackCanonicalShellInvSqMass_nonneg _) ?_ hbig_shift
  intro n
  have hn_lower : lower ≤ n + lower := by omega
  have hn_two : 2 ≤ n + lower := le_trans hlower hn_lower
  have hmassle :=
    entireXiPullbackCanonicalShellInvSqMass_le_card_mul
      (n + lower) hn_two
  have hcard := hcount (n + lower) hn_lower
  have hinv_nonneg :
      (0 : Real) ≤ ((((n + lower - 1 : Nat) : Real) ^ 2)⁻¹) := by
    positivity
  calc
    entireXiPullbackCanonicalShellInvSqMass (n + lower)
        ≤ (entireXiPullbackCanonicalShellCard (n + lower) : Real) *
            ((((n + lower - 1 : Nat) : Real) ^ 2)⁻¹) := hmassle
    _ ≤ (C * Real.log (↑(n + lower) : Real) + C₀) *
          ((((n + lower - 1 : Nat) : Real) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right hcard hinv_nonneg
    _ = C * (Real.log (↑(n + lower) : Real) *
          ((((n + lower - 1 : Nat) : Real) ^ 2)⁻¹)) +
        C₀ * ((((n + lower - 1 : Nat) : Real) ^ 2)⁻¹) := by
      ring

/-- Summability of the norm-ceiling shell masses yields inverse-square
summability of all multiplicity-bearing canonical occurrences. -/
theorem entireXiPullbackCanonical_invSqSummable_of_shellMass_summable
    (H : Summable entireXiPullbackCanonicalShellInvSqMass) :
    Summable fun i : EntireXiPullbackZeroOccurrence =>
      (‖entireXiPullbackZeroOccurrenceLoc i‖ ^ 2)⁻¹ := by
  refine
    summable_of_nonneg_fiber_tsum_le
      (fun i : EntireXiPullbackZeroOccurrence =>
        Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖)
      (fun _ => by positivity)
      entireXiPullbackCanonicalNormCeilFiberFinite
      H
      ?_
  intro n
  exact le_rfl

/-- The exact multiplicity-aware annular count output expected from a
Backlund--Turing/Riemann--von Mangoldt theorem. -/
structure EntireXiPullbackBacklundTuringShellBound : Type where
  lower : Nat
  lower_ge_two : 2 ≤ lower
  C : Real
  C₀ : Real
  shellCard_log_bound :
    ∀ n : Nat, lower ≤ n →
      (entireXiPullbackCanonicalShellCard n : Real) ≤
        C * Real.log n + C₀

/-- A multiplicity-aware Backlund--Turing shell bound discharges the complete
canonical inverse-square zero-distribution input. -/
theorem EntireXiPullbackBacklundTuringShellBound.toCanonicalZeroDistribution
    (H : EntireXiPullbackBacklundTuringShellBound) :
    EntireXiPullbackCanonicalZeroDistribution := by
  refine ⟨entireXiPullbackCanonical_invSqSummable_of_shellMass_summable ?_⟩
  exact
    entireXiPullbackCanonicalShellInvSqMass_summable_of_eventual_shellCard_log_bound
      H.lower H.lower_ge_two H.C H.C₀ H.shellCard_log_bound

end OverflowResidueRH
