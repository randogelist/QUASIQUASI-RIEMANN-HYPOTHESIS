/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.NumberTheory.LSeries.ZetaZeros
import RiemannHypothesis.Xi.RiemannHypothesisBridge

/-!
# The exact multiplicity-weighted nontrivial-zeta zero count

This file defines the classical positive-height zero count directly from
Mathlib's `riemannZeta`, rather than through an xi-specific counting datum.
The underlying set consists of the nontrivial zeros `s` with
`0 < s.im <= T`.  Each distinct zero contributes
`analyticOrderNatAt riemannZeta s` occurrences.

Mathlib proves that the zeta-zero set is discrete and hence has finite
intersection with compact sets.  Together with the unconditional critical
strip theorem from `Xi.RiemannHypothesisBridge`, this proves finiteness of the
count at every real height.  No zero table, Riemann--von Mangoldt estimate, or
argument-principle theorem is assumed here.
-/

open Metric Set

namespace OverflowResidueRH

/-- The distinct Mathlib-nontrivial zeta zeros with positive imaginary part
at most `T`.  This is the conventional half-open height range `0 < gamma <= T`.
-/
def zetaNontrivialZerosUpToHeightSet (T : Real) : Set Complex :=
  {s | IsMathlibNontrivialZetaZero s ∧ 0 < s.im ∧ s.im ≤ T}

/-- Every bounded positive-height nontrivial-zeta zero set is finite.

The proof uses Mathlib's compact-intersection finiteness theorem for the
actual zeta-zero set.  The critical-strip bound places the real part in
`(0, 1)`, while the height inequalities place the imaginary part in
`(0, T]`, so the counted set lies in a fixed closed ball. -/
theorem zetaNontrivialZerosUpToHeightSet_finite (T : Real) :
    (zetaNontrivialZerosUpToHeightSet T).Finite := by
  have hcompact :
      IsCompact (closedBall (0 : Complex) (1 + |T|)) :=
    ProperSpace.isCompact_closedBall (0 : Complex) (1 + |T|)
  apply hcompact.inter_riemannZetaZeros_finite.subset
  intro s hs
  have hxi : entireRiemannXi s = 0 :=
    entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr hs.1
  have hstrip : s.re ∈ Set.Ioo (0 : Real) 1 :=
    entireRiemannXi_zero_re_mem_Ioo hxi
  refine ⟨?_, hs.1.1⟩
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ = s.re + s.im := by
      rw [abs_of_pos hstrip.1, abs_of_pos hs.2.1]
    _ ≤ 1 + |T| := by
      have him_le_abs : s.im ≤ |T| := hs.2.2.trans (le_abs_self T)
      linarith [hstrip.2, him_le_abs]

/-- The finite type of distinct nontrivial zeta zeros counted up to height
`T`. -/
def ZetaNontrivialZeroUpToHeight (T : Real) : Type :=
  {s : Complex // s ∈ zetaNontrivialZerosUpToHeightSet T}

/-- The distinct counted zeta-zero subtype inherits finiteness from the
compact-intersection theorem above. -/
noncomputable instance zetaNontrivialZeroUpToHeight_fintype (T : Real) :
    Fintype (ZetaNontrivialZeroUpToHeight T) :=
  (zetaNontrivialZerosUpToHeightSet_finite T).fintype

/-- One occurrence for each unit of analytic multiplicity of each counted
zeta zero. -/
noncomputable def ZetaZeroOccurrenceUpToHeight (T : Real) : Type :=
  Sigma fun s : ZetaNontrivialZeroUpToHeight T =>
    Fin (analyticOrderNatAt riemannZeta s.1)

/-- The occurrence type defining the weighted count is finite. -/
theorem zetaZeroOccurrenceUpToHeight_finite (T : Real) :
    Finite (ZetaZeroOccurrenceUpToHeight T) := by
  unfold ZetaZeroOccurrenceUpToHeight
  infer_instance

/-- The exact multiplicity-weighted number of nontrivial zeta zeros with
`0 < Im(s) <= T`. -/
noncomputable def zetaWeightedZeroCountUpToHeight (T : Real) : Nat :=
  Nat.card (ZetaZeroOccurrenceUpToHeight T)

/-- The occurrence-cardinality definition is the usual finite sum of
analytic multiplicities over the distinct counted zeros. -/
theorem zetaWeightedZeroCountUpToHeight_eq_sum (T : Real) :
    zetaWeightedZeroCountUpToHeight T =
      ∑ s : ZetaNontrivialZeroUpToHeight T,
        analyticOrderNatAt riemannZeta s.1 := by
  letI : Finite (ZetaZeroOccurrenceUpToHeight T) :=
    zetaZeroOccurrenceUpToHeight_finite T
  unfold zetaWeightedZeroCountUpToHeight ZetaZeroOccurrenceUpToHeight
  rw [Nat.card_sigma]
  simp

/-- Inclusion of height intervals induces an embedding of exact
multiplicity occurrences. -/
noncomputable def zetaZeroOccurrenceUpToHeightEmbedding
    {A B : Real} (hAB : A ≤ B) :
    ZetaZeroOccurrenceUpToHeight A ↪
      ZetaZeroOccurrenceUpToHeight B where
  toFun i := ⟨⟨i.fst.val, by
    refine ⟨i.fst.property.1, i.fst.property.2.1, ?_⟩
    exact i.fst.property.2.2.trans hAB⟩, i.snd⟩
  inj' := by
    intro i j hij
    have hcomponents := Sigma.ext_iff.mp hij
    have hbase : i.fst = j.fst := by
      apply Subtype.ext
      exact congrArg
        (fun s : ZetaNontrivialZeroUpToHeight B => s.val)
        hcomponents.1
    exact Sigma.ext hbase hcomponents.2

/-- The exact multiplicity-weighted zeta-zero count is monotone in height. -/
theorem zetaWeightedZeroCountUpToHeight_mono
    {A B : Real} (hAB : A ≤ B) :
    zetaWeightedZeroCountUpToHeight A ≤
      zetaWeightedZeroCountUpToHeight B := by
  letI : Finite (ZetaZeroOccurrenceUpToHeight A) :=
    zetaZeroOccurrenceUpToHeight_finite A
  letI : Finite (ZetaZeroOccurrenceUpToHeight B) :=
    zetaZeroOccurrenceUpToHeight_finite B
  unfold zetaWeightedZeroCountUpToHeight
  exact Nat.card_le_card_of_injective
    (zetaZeroOccurrenceUpToHeightEmbedding hAB)
    (zetaZeroOccurrenceUpToHeightEmbedding hAB).injective

/-- The weighted zeta count is zero at nonpositive height. -/
theorem zetaWeightedZeroCountUpToHeight_eq_zero_of_nonpos
    {T : Real} (hT : T ≤ 0) :
    zetaWeightedZeroCountUpToHeight T = 0 := by
  have hempty : IsEmpty (ZetaNontrivialZeroUpToHeight T) := by
    refine ⟨?_⟩
    intro s
    exact (not_lt_of_ge hT) (lt_of_lt_of_le s.2.2.1 s.2.2.2)
  letI : IsEmpty (ZetaNontrivialZeroUpToHeight T) := hempty
  unfold zetaWeightedZeroCountUpToHeight ZetaZeroOccurrenceUpToHeight
  simp

end OverflowResidueRH
