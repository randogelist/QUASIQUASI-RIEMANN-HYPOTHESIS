/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import RiemannHypothesis.Xi.BacklundTuringBridge
import RiemannHypothesis.Xi.RiemannHypothesisBridge
import RiemannHypothesis.Xi.ZetaMultiplicityBridge
import RiemannHypothesis.ZeroCounting.SmoothMainTerm
import RiemannHypothesis.ZeroCounting.ZetaZeros

/-!
# Backlund--Turing height counts to the canonical xi divisor

This reduction-layer module converts the familiar ingredients of a
Backlund--Turing/Riemann--von Mangoldt theorem into the multiplicity-aware
norm-shell bound consumed by `Xi.BacklundTuringBridge`.

The general adapter keeps `shell_to_height_slab` explicit.  For the actual
canonical occurrence divisor, however, this module derives a width-two
comparison from the critical-strip bound and the exact multiplicity-preserving
negation equivalence.  The resulting canonical adapter has no geometric
assumption field.  What remains external is the genuine quantitative
Riemann--von Mangoldt/Turing estimate for the exact canonical count; no
numerical table or zero-count theorem is fabricated here.
-/

namespace OverflowResidueRH

/-- Over an interval in the monotone-density tail, the increase of the smooth
Riemann--von Mangoldt main term is at most interval width times the density at
the right endpoint. -/
theorem smoothZeroCountingN0_sub_le_width_mul_density
    {a b : Real} (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) :
    smoothZeroCountingN0 b - smoothZeroCountingN0 a ≤
      (b - a) * zeroDensityRho b := by
  have ha_pos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hdiff : DifferentiableOn Real smoothZeroCountingN0 (Set.Icc a b) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    exact (hasDerivAt_smoothZeroCountingN0 hx_pos).differentiableAt.differentiableWithinAt
  have hderiv :
      ∀ x ∈ interior (Set.Icc a b),
        deriv smoothZeroCountingN0 x ≤ zeroDensityRho b := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := interior_subset hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hxIcc.1
    rw [deriv_smoothZeroCountingN0 hx_pos]
    exact zeroDensityRho_mono_on_tail
      (le_trans ha hxIcc.1) (le_trans ha hab) hxIcc.2
  have h := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuousOn
    (hdiff.mono interior_subset)
    hderiv
    a (Set.left_mem_Icc.mpr hab)
    b (Set.right_mem_Icc.mpr hab)
    hab
  simpa [mul_comm] using h

/-! ## Exact geometry of the canonical multiplicity count -/

/-- Multiplicity-bearing pullback-zero occurrences with positive height at
most `T`.  Under `s = 1 / 2 + I * z`, the pullback coordinate `z.re` is the
usual zeta-zero height. -/
def canonicalPositiveHeightOccurrenceSet (T : Real) :
    Set EntireXiPullbackZeroOccurrence :=
  {i | 0 < (entireXiPullbackZeroOccurrenceLoc i).re ∧
    (entireXiPullbackZeroOccurrenceLoc i).re ≤ T}

/-- Multiplicity-bearing positive-height occurrences in the half-open slab
`(A, B]`. -/
def canonicalPositiveHeightOccurrenceSlab (A B : Real) :
    Set EntireXiPullbackZeroOccurrence :=
  {i | 0 < (entireXiPullbackZeroOccurrenceLoc i).re ∧
    A < (entireXiPullbackZeroOccurrenceLoc i).re ∧
    (entireXiPullbackZeroOccurrenceLoc i).re ≤ B}

/-- The canonical positive-height occurrence set is finite at every height. -/
theorem canonicalPositiveHeightOccurrenceSet_finite (T : Real) :
    (canonicalPositiveHeightOccurrenceSet T).Finite := by
  apply
    (entireXiPullbackZeroOccurrenceNormProper.finite_norm_le (|T| + 1)).subset
  intro i hi
  have him : |(entireXiPullbackZeroOccurrenceLoc i).im| < (1 / 2 : Real) :=
    entireXiPullback_zero_im_abs_lt_half
      (entireXiPullbackZeroOccurrenceLoc_is_zero i)
  have hre : |(entireXiPullbackZeroOccurrenceLoc i).re| ≤ |T| := by
    rw [abs_of_pos hi.1]
    exact hi.2.trans (le_abs_self T)
  calc
    ‖entireXiPullbackZeroOccurrenceLoc i‖
        ≤ |(entireXiPullbackZeroOccurrenceLoc i).re| +
            |(entireXiPullbackZeroOccurrenceLoc i).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |T| + 1 := by linarith

/-- Every bounded positive-height slab of canonical occurrences is finite. -/
theorem canonicalPositiveHeightOccurrenceSlab_finite (A B : Real) :
    (canonicalPositiveHeightOccurrenceSlab A B).Finite := by
  exact (canonicalPositiveHeightOccurrenceSet_finite B).subset (by
    intro i hi
    exact ⟨hi.1, hi.2.2⟩)

/-- The exact, multiplicity-bearing positive-height counting function for the
centered xi pullback. -/
noncomputable def canonicalPositiveHeightOccurrenceCount (T : Real) : Nat :=
  (canonicalPositiveHeightOccurrenceSet T).ncard

/-- The exact number of multiplicity-bearing occurrences in `(A, B]`. -/
noncomputable def canonicalPositiveHeightOccurrenceSlabCard
    (A B : Real) : Nat :=
  (canonicalPositiveHeightOccurrenceSlab A B).ncard

/-! ## Exact identification with the classical zeta count -/

/-- The distinct nonzero pullback zeros whose pullback height lies in
`(0, T]`.  This is the base of the canonical occurrence subtype before the
analytic-multiplicity fiber is attached. -/
def EntireXiPullbackPositiveHeightZeroUpToHeight (T : Real) : Type :=
  {z : EntireXiPullbackNonzeroZero //
    0 < z.val.re ∧ z.val.re ≤ T}

private noncomputable def zetaCoordinateOfPullback (z : Complex) : Complex :=
  (1 / 2 : Complex) + Complex.I * z

private noncomputable def pullbackCoordinateOfZeta (s : Complex) : Complex :=
  -Complex.I * (s - (1 / 2 : Complex))

@[simp] private theorem
    pullbackCoordinateOfZeta_zetaCoordinateOfPullback (z : Complex) :
    pullbackCoordinateOfZeta (zetaCoordinateOfPullback z) = z := by
  unfold pullbackCoordinateOfZeta zetaCoordinateOfPullback
  calc
    -Complex.I *
          ((1 / 2 : Complex) + Complex.I * z - (1 / 2 : Complex)) =
        -Complex.I * (Complex.I * z) := by ring
    _ = z := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I]
      simp

@[simp] private theorem
    zetaCoordinateOfPullback_pullbackCoordinateOfZeta (s : Complex) :
    zetaCoordinateOfPullback (pullbackCoordinateOfZeta s) = s := by
  unfold zetaCoordinateOfPullback pullbackCoordinateOfZeta
  rw [show Complex.I * (-Complex.I * (s - (1 / 2 : Complex))) =
      s - (1 / 2 : Complex) by
    rw [← mul_assoc]
    norm_num [Complex.I_mul_I]]
  ring

private theorem zetaCoordinateOfPullback_im (z : Complex) :
    (zetaCoordinateOfPullback z).im = z.re := by
  simp [zetaCoordinateOfPullback, Complex.mul_im]

private theorem pullbackCoordinateOfZeta_re (s : Complex) :
    (pullbackCoordinateOfZeta s).re = s.im := by
  simp [pullbackCoordinateOfZeta, Complex.mul_re]

/-- The affine change of variables `s = 1/2 + I*z` is an exact equivalence
between positive-height pullback zeros and the actual Mathlib-nontrivial zeta
zeros counted in `(0, T]`. -/
noncomputable def
    entireXiPullbackPositiveHeightZeroEquivZetaZeroUpToHeight (T : Real) :
    EntireXiPullbackPositiveHeightZeroUpToHeight T ≃
      ZetaNontrivialZeroUpToHeight T where
  toFun z := ⟨zetaCoordinateOfPullback z.val.val, by
    refine ⟨?_, ?_, ?_⟩
    · exact
        entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mp
          z.val.property.1
    · simpa [zetaCoordinateOfPullback_im] using z.property.1
    · simpa [zetaCoordinateOfPullback_im] using z.property.2⟩
  invFun s := by
    let z := pullbackCoordinateOfZeta s.val
    have hzeta : zetaCoordinateOfPullback z = s.val := by
      simp [z]
    have hzero : EntireXiPullback z = 0 := by
      unfold EntireXiPullback
      change entireRiemannXi (zetaCoordinateOfPullback z) = 0
      rw [hzeta]
      exact
        entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr
          s.property.1
    have hre : z.re = s.val.im := by
      simpa [z] using pullbackCoordinateOfZeta_re s.val
    have hne : z ≠ 0 := by
      intro hz
      rw [hz] at hre
      norm_num at hre
      linarith [s.property.2.1]
    exact ⟨⟨z, hzero, hne⟩, by
      constructor
      · simpa [hre] using s.property.2.1
      · simpa [hre] using s.property.2.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact pullbackCoordinateOfZeta_zetaCoordinateOfPullback z.val.val
  right_inv s := by
    apply Subtype.ext
    exact zetaCoordinateOfPullback_pullbackCoordinateOfZeta s.val

/-- Reassociate a height-restricted canonical occurrence subtype as a sigma
type over height-restricted distinct pullback zeros. -/
noncomputable def canonicalPositiveHeightOccurrenceSigmaEquiv (T : Real) :
    {i : EntireXiPullbackZeroOccurrence //
        i ∈ canonicalPositiveHeightOccurrenceSet T} ≃
      Sigma fun z : EntireXiPullbackPositiveHeightZeroUpToHeight T =>
        Fin (analyticOrderNatAt EntireXiPullback z.val.val) where
  toFun i := ⟨⟨i.val.fst, i.property⟩, i.val.snd⟩
  invFun i := ⟨⟨i.fst.val, i.snd⟩, i.fst.property⟩
  left_inv i := by
    rcases i with ⟨⟨z, k⟩, hi⟩
    rfl
  right_inv i := by
    rcases i with ⟨⟨z, hz⟩, k⟩
    rfl

/-- Exact multiplicity-preserving equivalence between canonical positive
height xi occurrences and actual nontrivial-zeta occurrences.  The fiber
equivalence is `Fin`-transport along the proved equality of analytic orders.
-/
noncomputable def canonicalPositiveHeightOccurrenceEquivZetaOccurrence
    (T : Real) :
    {i : EntireXiPullbackZeroOccurrence //
        i ∈ canonicalPositiveHeightOccurrenceSet T} ≃
      ZetaZeroOccurrenceUpToHeight T :=
  (canonicalPositiveHeightOccurrenceSigmaEquiv T).trans
    (Equiv.sigmaCongr
      (entireXiPullbackPositiveHeightZeroEquivZetaZeroUpToHeight T)
      (fun z => finCongr (by
        change analyticOrderNatAt EntireXiPullback z.val.val =
          analyticOrderNatAt riemannZeta ((1 / 2 : ℂ) + Complex.I * z.val.val)
        exact entireXiPullback_analyticOrderNatAt_eq_riemannZeta_of_zero
          z.val.property.1)))

/-- The canonical positive-height occurrence count is definitionally tied to
the classical multiplicity-weighted zeta-zero count, with no xi-specific
count-identification assumption. -/
theorem canonicalPositiveHeightOccurrenceCount_eq_zetaWeightedZeroCount
    (T : Real) :
    canonicalPositiveHeightOccurrenceCount T =
      zetaWeightedZeroCountUpToHeight T := by
  unfold canonicalPositiveHeightOccurrenceCount
    zetaWeightedZeroCountUpToHeight
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    (canonicalPositiveHeightOccurrenceEquivZetaOccurrence T)

theorem canonicalPositiveHeightOccurrenceSet_mono
    {A B : Real} (hAB : A ≤ B) :
    canonicalPositiveHeightOccurrenceSet A ⊆
      canonicalPositiveHeightOccurrenceSet B := by
  intro i hi
  exact ⟨hi.1, hi.2.trans hAB⟩

theorem canonicalPositiveHeightOccurrenceCount_mono
    {A B : Real} (hAB : A ≤ B) :
    canonicalPositiveHeightOccurrenceCount A ≤
      canonicalPositiveHeightOccurrenceCount B := by
  letI : Fintype (canonicalPositiveHeightOccurrenceSet B) :=
    (canonicalPositiveHeightOccurrenceSet_finite B).fintype
  unfold canonicalPositiveHeightOccurrenceCount
  exact Set.ncard_le_ncard (canonicalPositiveHeightOccurrenceSet_mono hAB)

theorem canonicalPositiveHeightOccurrenceSlab_eq_sdiff
    {A B : Real} (_hAB : A ≤ B) :
    canonicalPositiveHeightOccurrenceSlab A B =
      canonicalPositiveHeightOccurrenceSet B \
        canonicalPositiveHeightOccurrenceSet A := by
  ext i
  simp only [canonicalPositiveHeightOccurrenceSlab,
    canonicalPositiveHeightOccurrenceSet, Set.mem_setOf_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨hpos, hA, hB⟩
    exact ⟨⟨hpos, hB⟩, fun h => (not_le_of_gt hA) h.2⟩
  · rintro ⟨⟨hpos, hB⟩, hnotA⟩
    exact ⟨hpos, lt_of_not_ge (fun h => hnotA ⟨hpos, h⟩), hB⟩

/-- Slab cardinality is the increment of the canonical cumulative count. -/
theorem canonicalPositiveHeightOccurrenceSlabCard_eq_sub
    {A B : Real} (hAB : A ≤ B) :
    canonicalPositiveHeightOccurrenceSlabCard A B =
      canonicalPositiveHeightOccurrenceCount B -
        canonicalPositiveHeightOccurrenceCount A := by
  unfold canonicalPositiveHeightOccurrenceSlabCard
    canonicalPositiveHeightOccurrenceCount
  rw [canonicalPositiveHeightOccurrenceSlab_eq_sdiff hAB]
  rw [Set.ncard_sdiff
    (canonicalPositiveHeightOccurrenceSet_mono hAB)
    (canonicalPositiveHeightOccurrenceSet_finite A)]

/-- A norm-ceiling shell `n` lies, in absolute pullback height, in the window
`(n - 2, n]`.  The width two comes from the unconditional critical-strip
bound `|z.im| < 1 / 2`. -/
theorem canonicalNormCeilShell_abs_re_bounds
    {i : EntireXiPullbackZeroOccurrence} {n : Nat}
    (hn : 2 ≤ n)
    (hi : Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n) :
    ((n - 2 : Nat) : Real) <
        |(entireXiPullbackZeroOccurrenceLoc i).re| ∧
      |(entireXiPullbackZeroOccurrenceLoc i).re| ≤ (n : Real) := by
  have hinner :=
    entireXiPullbackCanonicalNormCeilFiber_pred_lt_norm
      (le_trans (by norm_num : 1 ≤ 2) hn) hi
  have houter :
      ‖entireXiPullbackZeroOccurrenceLoc i‖ ≤ (n : Real) := by
    exact Nat.le_of_ceil_le (by rw [hi])
  have him : |(entireXiPullbackZeroOccurrenceLoc i).im| < (1 / 2 : Real) :=
    entireXiPullback_zero_im_abs_lt_half
      (entireXiPullbackZeroOccurrenceLoc_is_zero i)
  have hnorm_le :=
    Complex.norm_le_abs_re_add_abs_im
      (entireXiPullbackZeroOccurrenceLoc i)
  have hcast_pred : (((n - 1 : Nat) : Real)) = (n : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hcast_two : (((n - 2 : Nat) : Real)) = (n : Real) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  constructor
  · rw [hcast_two]
    rw [hcast_pred] at hinner
    linarith
  · exact (Complex.abs_re_le_norm _).trans houter

private abbrev canonicalNormCeilShellType (n : Nat) :=
  {i : EntireXiPullbackZeroOccurrence //
    Nat.ceil ‖entireXiPullbackZeroOccurrenceLoc i‖ = n}

private abbrev canonicalPositiveHeightOccurrenceSlabType (A B : Real) :=
  {i : EntireXiPullbackZeroOccurrence //
    i ∈ canonicalPositiveHeightOccurrenceSlab A B}

/-- Send a shell occurrence to the positive-height slab itself when its height
is positive, and to the negated occurrence otherwise.  The sum tag records
which side of the symmetric pair it came from. -/
private noncomputable def canonicalNormCeilShellToSignedHeightSlab
    (n : Nat) (hn : 2 ≤ n) :
    canonicalNormCeilShellType n →
      canonicalPositiveHeightOccurrenceSlabType ((n - 2 : Nat) : Real) n ⊕
        canonicalPositiveHeightOccurrenceSlabType ((n - 2 : Nat) : Real) n :=
  fun i =>
    if hpos : 0 < (entireXiPullbackZeroOccurrenceLoc i.1).re then
      Sum.inl ⟨i.1, by
        have hb := canonicalNormCeilShell_abs_re_bounds hn i.2
        exact ⟨hpos, by simpa [abs_of_pos hpos] using hb.1,
          by simpa [abs_of_pos hpos] using hb.2⟩⟩
    else
      Sum.inr ⟨entireXiPullbackZeroOccurrenceNegEquiv i.1, by
        have hb := canonicalNormCeilShell_abs_re_bounds hn i.2
        have habs_pos :
            0 < |(entireXiPullbackZeroOccurrenceLoc i.1).re| :=
          lt_of_le_of_lt (Nat.cast_nonneg _) hb.1
        have hre_ne : (entireXiPullbackZeroOccurrenceLoc i.1).re ≠ 0 :=
          abs_pos.mp habs_pos
        have hre_le : (entireXiPullbackZeroOccurrenceLoc i.1).re ≤ 0 :=
          le_of_not_gt hpos
        have hre_neg : (entireXiPullbackZeroOccurrenceLoc i.1).re < 0 :=
          lt_of_le_of_ne hre_le hre_ne
        change
          0 < (entireXiPullbackZeroOccurrenceLoc
              (entireXiPullbackZeroOccurrenceNegEquiv i.1)).re ∧
            ((n - 2 : Nat) : Real) <
                (entireXiPullbackZeroOccurrenceLoc
                  (entireXiPullbackZeroOccurrenceNegEquiv i.1)).re ∧
              (entireXiPullbackZeroOccurrenceLoc
                  (entireXiPullbackZeroOccurrenceNegEquiv i.1)).re ≤ (n : Real)
        rw [entireXiPullbackZeroOccurrenceNegEquiv_loc]
        change
          0 < -(entireXiPullbackZeroOccurrenceLoc i.1).re ∧
            ((n - 2 : Nat) : Real) <
                -(entireXiPullbackZeroOccurrenceLoc i.1).re ∧
              -(entireXiPullbackZeroOccurrenceLoc i.1).re ≤ (n : Real)
        exact ⟨by linarith, by simpa [abs_of_neg hre_neg] using hb.1,
          by simpa [abs_of_neg hre_neg] using hb.2⟩⟩

private theorem canonicalNormCeilShellToSignedHeightSlab_injective
    (n : Nat) (hn : 2 ≤ n) :
    Function.Injective (canonicalNormCeilShellToSignedHeightSlab n hn) := by
  intro i j hij
  by_cases hi : 0 < (entireXiPullbackZeroOccurrenceLoc i.1).re
  · by_cases hj : 0 < (entireXiPullbackZeroOccurrenceLoc j.1).re
    · simp only [canonicalNormCeilShellToSignedHeightSlab, hi, hj,
        dite_true, Sum.inl.injEq] at hij
      exact Subtype.ext (congrArg
        (fun u : canonicalPositiveHeightOccurrenceSlabType ((n - 2 : Nat) : Real) n =>
          u.val) hij)
    · simp only [canonicalNormCeilShellToSignedHeightSlab, hi, hj,
        dite_true, dite_false] at hij
      cases hij
  · by_cases hj : 0 < (entireXiPullbackZeroOccurrenceLoc j.1).re
    · simp only [canonicalNormCeilShellToSignedHeightSlab, hi, hj,
        dite_true, dite_false] at hij
      cases hij
    · simp only [canonicalNormCeilShellToSignedHeightSlab, hi, hj,
        dite_false, Sum.inr.injEq, Subtype.mk.injEq] at hij
      apply Subtype.ext
      exact entireXiPullbackZeroOccurrenceNegEquiv.injective hij

/-- Exact shell geometry: a multiplicity-bearing norm shell injects into two
copies of the positive-height occurrence slab `(n - 2, n]`. -/
theorem entireXiPullbackCanonicalShellCard_le_two_mul_heightSlabCard
    (n : Nat) (hn : 2 ≤ n) :
    entireXiPullbackCanonicalShellCard n ≤
      2 * canonicalPositiveHeightOccurrenceSlabCard
        ((n - 2 : Nat) : Real) n := by
  letI : Fintype
      (canonicalPositiveHeightOccurrenceSlabType ((n - 2 : Nat) : Real) n) :=
    (canonicalPositiveHeightOccurrenceSlab_finite ((n - 2 : Nat) : Real) n).fintype
  unfold entireXiPullbackCanonicalShellCard
  calc
    Nat.card (canonicalNormCeilShellType n) ≤
        Nat.card
          (canonicalPositiveHeightOccurrenceSlabType ((n - 2 : Nat) : Real) n ⊕
            canonicalPositiveHeightOccurrenceSlabType ((n - 2 : Nat) : Real) n) :=
      Nat.card_le_card_of_injective
        (canonicalNormCeilShellToSignedHeightSlab n hn)
        (canonicalNormCeilShellToSignedHeightSlab_injective n hn)
    _ = 2 * canonicalPositiveHeightOccurrenceSlabCard
        ((n - 2 : Nat) : Real) n := by
      rw [Nat.card_sum]
      simp only [canonicalPositiveHeightOccurrenceSlabCard,
        Nat.card_coe_set_eq]
      omega

/-- Real-valued form of the shell/slab bound, expressed directly as an
increment of the canonical positive-height count. -/
theorem entireXiPullbackCanonicalShellCard_cast_le_heightCount_sub
    (n : Nat) (hn : 2 ≤ n) :
    (entireXiPullbackCanonicalShellCard n : Real) ≤
      2 * ((canonicalPositiveHeightOccurrenceCount n : Real) -
        (canonicalPositiveHeightOccurrenceCount ((n - 2 : Nat) : Real) : Real)) := by
  have hgeom :=
    entireXiPullbackCanonicalShellCard_le_two_mul_heightSlabCard n hn
  rw [canonicalPositiveHeightOccurrenceSlabCard_eq_sub (by
    exact_mod_cast Nat.sub_le n 2)] at hgeom
  have hmono := canonicalPositiveHeightOccurrenceCount_mono (by
    exact_mod_cast Nat.sub_le n 2 : ((n - 2 : Nat) : Real) ≤ (n : Real))
  exact_mod_cast hgeom

/-- Active, dependency-clean interface for the output of a multiplicity-aware
Backlund--Turing height-count argument.

`N = N₀ + S` and the Turing envelope control adjacent height slabs.  The last
field transfers a pullback norm shell to a symmetric pair of zeta-height
slabs; it is where critical-strip geometry and equality of analytic
multiplicities enter. -/
structure EntireXiPullbackBacklundTuringHeightCountData : Type where
  N : Real → Real
  S : Real → Real
  threshold : Nat
  window : Nat
  threshold_ge_two_pi : 2 * Real.pi ≤ (threshold : Real)
  window_pos : 0 < window
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  count_eq :
    ∀ T : Real, (threshold : Real) ≤ T →
      N T = smoothZeroCountingN0 T + S T
  turing_bound :
    ∀ T : Real, (threshold : Real) ≤ T →
      |S T| ≤ C * Real.log T + D
  shell_to_height_slab :
    ∀ n : Nat, threshold + window ≤ n →
      (entireXiPullbackCanonicalShellCard n : Real) ≤
        2 * (N (n : Real) - N ((n - window : Nat) : Real))

/-- Riemann--von Mangoldt decomposition plus a Turing bound and the exact
multiplicity-aware shell/slab comparison yield the eventual logarithmic shell
bound required for canonical inverse-square summability. -/
noncomputable def
    EntireXiPullbackBacklundTuringHeightCountData.toShellBound
    (H : EntireXiPullbackBacklundTuringHeightCountData) :
    EntireXiPullbackBacklundTuringShellBound where
  lower := H.threshold + H.window
  lower_ge_two := by
    have hthreshold_pos : 0 < H.threshold := by
      have : (0 : Real) < H.threshold :=
        lt_of_lt_of_le (by positivity) H.threshold_ge_two_pi
      exact_mod_cast this
    have hwindow_pos : 0 < H.window := H.window_pos
    omega
  C := 2 * ((H.window : Real) * (1 / (2 * Real.pi)) + 2 * H.C)
  C₀ := 4 * H.D
  shellCard_log_bound := by
    intro n hn
    have hwindow_le_n : H.window ≤ n := by omega
    have hthreshold_le_pred : H.threshold ≤ n - H.window := by omega
    have hthreshold_le_n : H.threshold ≤ n := by omega
    have hpred_le_n : n - H.window ≤ n := Nat.sub_le n H.window
    have hthreshold_real_pred :
        (H.threshold : Real) ≤ ((n - H.window : Nat) : Real) := by
      exact_mod_cast hthreshold_le_pred
    have hthreshold_real_n : (H.threshold : Real) ≤ (n : Real) := by
      exact_mod_cast hthreshold_le_n
    have hpred_real_le_n : ((n - H.window : Nat) : Real) ≤ (n : Real) := by
      exact_mod_cast hpred_le_n
    have hpred_ge_two_pi :
        2 * Real.pi ≤ ((n - H.window : Nat) : Real) :=
      le_trans H.threshold_ge_two_pi hthreshold_real_pred
    have hn_ge_two_pi : 2 * Real.pi ≤ (n : Real) :=
      le_trans hpred_ge_two_pi hpred_real_le_n
    have hwidth :
        (n : Real) - ((n - H.window : Nat) : Real) = (H.window : Real) := by
      rw [Nat.cast_sub hwindow_le_n]
      ring
    have hmain := smoothZeroCountingN0_sub_le_width_mul_density
      hpred_ge_two_pi hpred_real_le_n
    have hrho_abs :=
      zeroDensityRho_abs_le_log_div_two_pi_of_ge_two_pi hn_ge_two_pi
    have hrho :
        zeroDensityRho (n : Real) ≤
          (1 / (2 * Real.pi)) * Real.log (n : Real) :=
      le_trans (le_abs_self _) hrho_abs
    have hwindow_nonneg : (0 : Real) ≤ H.window := by positivity
    have hmain_log :
        smoothZeroCountingN0 (n : Real) -
            smoothZeroCountingN0 ((n - H.window : Nat) : Real)
          ≤ (H.window : Real) *
              ((1 / (2 * Real.pi)) * Real.log (n : Real)) := by
      rw [hwidth] at hmain
      exact le_trans hmain (mul_le_mul_of_nonneg_left hrho hwindow_nonneg)
    have hpred_pos : 0 < ((n - H.window : Nat) : Real) :=
      lt_of_lt_of_le (by positivity) hpred_ge_two_pi
    have hlog_pred_le_n :
        Real.log ((n - H.window : Nat) : Real) ≤ Real.log (n : Real) :=
      Real.log_le_log hpred_pos hpred_real_le_n
    have hS_n := H.turing_bound (n : Real) hthreshold_real_n
    have hS_pred := H.turing_bound
      ((n - H.window : Nat) : Real) hthreshold_real_pred
    have hS_pred_log :
        |H.S ((n - H.window : Nat) : Real)| ≤
          H.C * Real.log (n : Real) + H.D := by
      exact le_trans hS_pred (by
        simpa [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left hlog_pred_le_n H.C_nonneg) H.D)
    have hS_diff :
        H.S (n : Real) - H.S ((n - H.window : Nat) : Real) ≤
          2 * H.C * Real.log (n : Real) + 2 * H.D := by
      calc
        H.S (n : Real) - H.S ((n - H.window : Nat) : Real)
            ≤ |H.S (n : Real)| +
                |H.S ((n - H.window : Nat) : Real)| := by
              linarith [le_abs_self (H.S (n : Real)),
                neg_le_abs (H.S ((n - H.window : Nat) : Real))]
        _ ≤ (H.C * Real.log (n : Real) + H.D) +
              (H.C * Real.log (n : Real) + H.D) :=
            add_le_add hS_n hS_pred_log
        _ = 2 * H.C * Real.log (n : Real) + 2 * H.D := by ring
    have hN_eq :
        H.N (n : Real) - H.N ((n - H.window : Nat) : Real) =
          (smoothZeroCountingN0 (n : Real) -
            smoothZeroCountingN0 ((n - H.window : Nat) : Real)) +
          (H.S (n : Real) - H.S ((n - H.window : Nat) : Real)) := by
      rw [H.count_eq (n : Real) hthreshold_real_n,
        H.count_eq ((n - H.window : Nat) : Real) hthreshold_real_pred]
      ring
    have hN_log :
        H.N (n : Real) - H.N ((n - H.window : Nat) : Real) ≤
          ((H.window : Real) * (1 / (2 * Real.pi)) + 2 * H.C) *
              Real.log (n : Real) + 2 * H.D := by
      rw [hN_eq]
      calc
        (smoothZeroCountingN0 (n : Real) -
              smoothZeroCountingN0 ((n - H.window : Nat) : Real)) +
            (H.S (n : Real) - H.S ((n - H.window : Nat) : Real))
          ≤ (H.window : Real) *
                ((1 / (2 * Real.pi)) * Real.log (n : Real)) +
              (2 * H.C * Real.log (n : Real) + 2 * H.D) :=
            add_le_add hmain_log hS_diff
        _ = ((H.window : Real) * (1 / (2 * Real.pi)) + 2 * H.C) *
              Real.log (n : Real) + 2 * H.D := by ring
    have hshell := H.shell_to_height_slab n hn
    calc
      (entireXiPullbackCanonicalShellCard n : Real)
          ≤ 2 * (H.N (n : Real) -
            H.N ((n - H.window : Nat) : Real)) := hshell
      _ ≤ 2 *
          (((H.window : Real) * (1 / (2 * Real.pi)) + 2 * H.C) *
              Real.log (n : Real) + 2 * H.D) :=
        mul_le_mul_of_nonneg_left hN_log (by norm_num)
      _ = 2 * ((H.window : Real) * (1 / (2 * Real.pi)) + 2 * H.C) *
            Real.log (n : Real) + 4 * H.D := by ring

/-- The height-count package therefore supplies the canonical inverse-square
zero-distribution input used by the strict logarithmic-derivative criterion. -/
theorem
    EntireXiPullbackBacklundTuringHeightCountData.toCanonicalZeroDistribution
    (H : EntireXiPullbackBacklundTuringHeightCountData) :
    EntireXiPullbackCanonicalZeroDistribution :=
  H.toShellBound.toCanonicalZeroDistribution

/-! ## Canonical specialization with geometry derived -/

/-- A Backlund--Turing package stated directly for the exact canonical
multiplicity count.  Unlike the more general interface above, this structure
has no shell-to-height field: the width-two shell comparison is a theorem.

The substantive analytic input is the logarithmic `turing_bound` for the
remainder `S`; `count_eq` records which remainder is being bounded (and could
be made definitional by choosing `S := N - N₀`).  In particular, identifying
this canonical count with a classical multiplicity-weighted zeta-zero count,
or importing a classical theorem that supplies the envelope, is not asserted
by the present module. -/
structure EntireXiPullbackCanonicalBacklundTuringHeightCountData : Type where
  S : Real → Real
  threshold : Nat
  threshold_ge_two_pi : 2 * Real.pi ≤ (threshold : Real)
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  count_eq :
    ∀ T : Real, (threshold : Real) ≤ T →
      (canonicalPositiveHeightOccurrenceCount T : Real) =
        smoothZeroCountingN0 T + S T
  turing_bound :
    ∀ T : Real, (threshold : Real) ≤ T →
      |S T| ≤ C * Real.log T + D

/-- Forget the fact that the count is canonical and expose the general
height-count interface.  The shell field is discharged by the exact
width-two geometry theorem above. -/
noncomputable def
    EntireXiPullbackCanonicalBacklundTuringHeightCountData.toHeightCountData
    (H : EntireXiPullbackCanonicalBacklundTuringHeightCountData) :
    EntireXiPullbackBacklundTuringHeightCountData where
  N := fun T => canonicalPositiveHeightOccurrenceCount T
  S := H.S
  threshold := H.threshold
  window := 2
  threshold_ge_two_pi := H.threshold_ge_two_pi
  window_pos := by norm_num
  C := H.C
  D := H.D
  C_nonneg := H.C_nonneg
  D_nonneg := H.D_nonneg
  count_eq := H.count_eq
  turing_bound := H.turing_bound
  shell_to_height_slab := by
    intro n hn
    have hn_two : 2 ≤ n := by omega
    simpa using
      entireXiPullbackCanonicalShellCard_cast_le_heightCount_sub n hn_two

/-- The canonical Backlund--Turing package supplies the eventual logarithmic
norm-shell bound, with the geometric comparison derived rather than assumed. -/
noncomputable def
    EntireXiPullbackCanonicalBacklundTuringHeightCountData.toShellBound
    (H : EntireXiPullbackCanonicalBacklundTuringHeightCountData) :
    EntireXiPullbackBacklundTuringShellBound :=
  H.toHeightCountData.toShellBound

/-- The canonical Backlund--Turing package therefore supplies the exact
inverse-square zero-distribution input used by the strict criterion. -/
theorem
    EntireXiPullbackCanonicalBacklundTuringHeightCountData.toCanonicalZeroDistribution
    (H : EntireXiPullbackCanonicalBacklundTuringHeightCountData) :
    EntireXiPullbackCanonicalZeroDistribution :=
  H.toShellBound.toCanonicalZeroDistribution

/-! ## Classical zeta-count specialization -/

/-- The concrete remainder in the Riemann--von Mangoldt decomposition for
the actual multiplicity-weighted nontrivial-zeta count.

This definition fixes both the counted divisor and the endpoint convention:
zeros with `0 < Im(s) ≤ T` are counted with `analyticOrderNatAt riemannZeta`.
Thus there is no abstract count function and no separate count-identification
field in the classical interface below. -/
noncomputable def zetaZeroCountingRemainder (T : Real) : Real :=
  (zetaWeightedZeroCountUpToHeight T : Real) - smoothZeroCountingN0 T

/-- The exact remaining classical Backlund--Turing input, stated solely for
Mathlib's `riemannZeta` and its analytic multiplicities.

An inhabitant is a genuine quantitative number-theory theorem: an eventual
logarithmic bound for the concrete Riemann--von Mangoldt remainder.  All
transport to the canonical xi divisor, including equality of counts and
multiplicities, is proved rather than carried as xi-specific data.

Mathlib's Jensen inequality can bound the *uncentred* cumulative divisor by
`O(T log T)` from a maximum-modulus estimate.  That does not inhabit this
structure: the stronger `O(log T)` remainder requires the classical
argument-principle identification and cancellation of the smooth main term.
-/
structure ZetaBacklundTuringRemainderBound : Type where
  threshold : Nat
  threshold_ge_two_pi : 2 * Real.pi ≤ (threshold : Real)
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  remainder_bound :
    ∀ T : Real, (threshold : Real) ≤ T →
      |zetaZeroCountingRemainder T| ≤ C * Real.log T + D

/-- The concrete zeta Backlund--Turing remainder bound supplies the canonical
height-count package.  The count equality is discharged by the exact
multiplicity-preserving occurrence equivalence above. -/
noncomputable def
    ZetaBacklundTuringRemainderBound.toCanonicalHeightCountData
    (H : ZetaBacklundTuringRemainderBound) :
    EntireXiPullbackCanonicalBacklundTuringHeightCountData where
  S := zetaZeroCountingRemainder
  threshold := H.threshold
  threshold_ge_two_pi := H.threshold_ge_two_pi
  C := H.C
  D := H.D
  C_nonneg := H.C_nonneg
  D_nonneg := H.D_nonneg
  count_eq := by
    intro T _hT
    rw [canonicalPositiveHeightOccurrenceCount_eq_zetaWeightedZeroCount]
    unfold zetaZeroCountingRemainder
    ring
  turing_bound := H.remainder_bound

/-- A classical zeta Backlund--Turing remainder estimate therefore yields the
eventual logarithmic canonical norm-shell bound. -/
noncomputable def ZetaBacklundTuringRemainderBound.toShellBound
    (H : ZetaBacklundTuringRemainderBound) :
    EntireXiPullbackBacklundTuringShellBound :=
  H.toCanonicalHeightCountData.toShellBound

/-- A classical zeta Backlund--Turing remainder estimate discharges the
complete inverse-square distribution input for the canonical xi divisor. -/
theorem ZetaBacklundTuringRemainderBound.toCanonicalZeroDistribution
    (H : ZetaBacklundTuringRemainderBound) :
    EntireXiPullbackCanonicalZeroDistribution :=
  H.toShellBound.toCanonicalZeroDistribution

end OverflowResidueRH
