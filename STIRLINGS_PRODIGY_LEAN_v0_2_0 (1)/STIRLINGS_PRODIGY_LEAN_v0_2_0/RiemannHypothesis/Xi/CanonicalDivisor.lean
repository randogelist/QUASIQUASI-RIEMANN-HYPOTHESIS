/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Compactness.Lindelof
import RiemannHypothesis.HadamardProduct.LogDerivative
import RiemannHypothesis.Xi.SignTargets

/-!
# The canonical divisor of the entire xi pullback

This file constructs the unconditional, multiplicity-bearing zero index of
`EntireXiPullback`.  The zero at the origin is recorded by its analytic order.
Every nonzero zero `rho` contributes the finite fiber
`Fin (analyticOrderNatAt EntireXiPullback rho)`, so repeated occurrences encode
the exact analytic multiplicity without assuming that xi has only simple zeros.

The divisor is locally finite and countable.  The only genuinely global
analytic input left open is inverse-square summability of the occurrences;
`EntireXiPullbackCanonicalZeroDistribution` names precisely that input and
converts it to the generic Hadamard summability interface.
-/

open Filter Metric Set Topology

namespace OverflowResidueRH

/-- The critical-line pullback is even, by the functional equation
`xi(1 - s) = xi(s)`. -/
theorem entireXiPullback_neg (z : Complex) :
    EntireXiPullback (-z) = EntireXiPullback z := by
  unfold EntireXiPullback
  rw [show (1 / 2 : Complex) + Complex.I * (-z) =
      1 - ((1 / 2 : Complex) + Complex.I * z) by ring]
  exact entireRiemannXi_one_sub _

/-- The affine coordinate change `z ↦ 1/2 + I*z` preserves analytic order,
because its derivative is the nonzero constant `I`.  This is the local
multiplicity bridge needed to compare the canonical pullback divisor with a
multiplicity-weighted xi or zeta zero count. -/
theorem entireXiPullback_analyticOrderAt_eq_entireRiemannXi (z : Complex) :
    analyticOrderAt EntireXiPullback z =
      analyticOrderAt entireRiemannXi
        ((1 / 2 : Complex) + Complex.I * z) := by
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := entireRiemannXi)
    (g := fun w : Complex => (1 / 2 : Complex) + Complex.I * w)
    (z₀ := z)
    (by fun_prop)
    (by simp)
  have hfun :
      entireRiemannXi ∘
          (fun w : Complex => (1 / 2 : Complex) + Complex.I * w) =
        EntireXiPullback := by
    funext w
    rfl
  rw [hfun] at hcomp
  exact hcomp

/-- The pullback cannot vanish identically on a neighborhood of any point. -/
theorem EntireXiPullback_not_eventuallyEq_zero (p : Complex) :
    ¬ (EntireXiPullback =ᶠ[nhds p] 0) := by
  intro hlocal
  have h_on : AnalyticOnNhd Complex EntireXiPullback Set.univ :=
    fun z _hz => EntireXiPullback_differentiable.analyticAt z
  have heq : Set.EqOn EntireXiPullback 0 Set.univ :=
    h_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ
      (Set.mem_univ p)
      hlocal
  obtain ⟨z, hz⟩ := EntireXiPullback_nontrivial_holds
  exact hz (heq (Set.mem_univ z))

/-- The analytic order of the entire xi pullback is finite at every point. -/
theorem entireXiPullback_analyticOrderAt_ne_top (z : Complex) :
    analyticOrderAt EntireXiPullback z ≠ ⊤ := by
  intro htop
  exact
    EntireXiPullback_not_eventuallyEq_zero z
      (analyticOrderAt_eq_top.mp htop)

/-- Negation preserves the analytic order of the even pullback. -/
theorem entireXiPullback_analyticOrderAt_neg (z : Complex) :
    analyticOrderAt EntireXiPullback (-z) =
      analyticOrderAt EntireXiPullback z := by
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := EntireXiPullback) (g := fun w : Complex => -w) (z₀ := z)
    (by fun_prop) (by simp)
  have hfun : EntireXiPullback ∘ (fun w : Complex => -w) =
      EntireXiPullback := by
    funext w
    exact entireXiPullback_neg w
  rw [hfun] at hcomp
  exact hcomp.symm

/-- Negation also preserves the natural-valued analytic multiplicity. -/
theorem entireXiPullback_analyticOrderNatAt_neg (z : Complex) :
    analyticOrderNatAt EntireXiPullback (-z) =
      analyticOrderNatAt EntireXiPullback z := by
  unfold analyticOrderNatAt
  rw [entireXiPullback_analyticOrderAt_neg]

/-- The multiplicity of a possible zero at the pullback origin. -/
noncomputable def entireXiPullbackOriginMultiplicity : Nat :=
  analyticOrderNatAt EntireXiPullback 0

/-- The origin multiplicity is exactly the analytic order at the origin. -/
theorem entireXiPullback_analyticOrderAt_zero :
    analyticOrderAt EntireXiPullback 0 =
      (entireXiPullbackOriginMultiplicity : ENat) := by
  exact
    (Nat.cast_analyticOrderNatAt
      (entireXiPullback_analyticOrderAt_ne_top 0)).symm

/-- The origin multiplicity is nonzero exactly when the pullback vanishes at
the origin. -/
theorem entireXiPullbackOriginMultiplicity_ne_zero_iff :
    entireXiPullbackOriginMultiplicity ≠ 0 ↔
      EntireXiPullback 0 = 0 := by
  constructor
  · intro hm
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
  · intro hz hm
    have horder : analyticOrderAt EntireXiPullback 0 ≠ 0 :=
      (EntireXiPullback_analyticAt 0).analyticOrderAt_ne_zero.mpr hz
    apply horder
    rw [entireXiPullback_analyticOrderAt_zero, hm]
    simp

/-- The subtype of distinct nonzero zeros of the entire xi pullback. -/
def EntireXiPullbackNonzeroZero : Type :=
  {z : Complex // EntireXiPullback z = 0 ∧ z ≠ 0}

/-- Negation acts on the distinct nonzero pullback zeros. -/
def entireXiPullbackNonzeroZeroNeg
    (z : EntireXiPullbackNonzeroZero) :
    EntireXiPullbackNonzeroZero :=
  ⟨-z.1, entireXiPullback_neg z.1 ▸ z.2.1, neg_ne_zero.mpr z.2.2⟩

@[simp] theorem entireXiPullbackNonzeroZeroNeg_val
    (z : EntireXiPullbackNonzeroZero) :
    (entireXiPullbackNonzeroZeroNeg z).1 = -z.1 :=
  rfl

/-- Negation is an involutive equivalence of the distinct nonzero zeros. -/
def entireXiPullbackNonzeroZeroNegEquiv :
    EntireXiPullbackNonzeroZero ≃ EntireXiPullbackNonzeroZero where
  toFun := entireXiPullbackNonzeroZeroNeg
  invFun := entireXiPullbackNonzeroZeroNeg
  left_inv z := by
    apply Subtype.ext
    simp [entireXiPullbackNonzeroZeroNeg]
  right_inv z := by
    apply Subtype.ext
    simp [entireXiPullbackNonzeroZeroNeg]

/-- Every nonzero pullback zero has strictly positive natural analytic order. -/
theorem entireXiPullbackNonzeroZero_analyticOrderNatAt_pos
    (z : EntireXiPullbackNonzeroZero) :
    0 < analyticOrderNatAt EntireXiPullback z.1 := by
  apply Nat.pos_of_ne_zero
  intro horderNat
  have horder : analyticOrderAt EntireXiPullback z.1 ≠ 0 :=
    (EntireXiPullback_analyticAt z.1).analyticOrderAt_ne_zero.mpr z.2.1
  apply horder
  rw [← Nat.cast_analyticOrderNatAt
    (entireXiPullback_analyticOrderAt_ne_top z.1), horderNat]
  simp

/-- One occurrence for each unit of analytic multiplicity at every nonzero
pullback zero. -/
noncomputable def EntireXiPullbackZeroOccurrence : Type :=
  Sigma fun z : EntireXiPullbackNonzeroZero =>
    Fin (analyticOrderNatAt EntireXiPullback z.1)

/-- The occurrence fiber above a distinct nonzero zero is exactly a finite
type with cardinality equal to that zero's analytic order. -/
noncomputable def entireXiPullbackZeroOccurrenceFiberEquiv
    (z : EntireXiPullbackNonzeroZero) :
    {i : EntireXiPullbackZeroOccurrence // i.1 = z} ≃
      Fin (analyticOrderNatAt EntireXiPullback z.1) where
  toFun i := i.2 ▸ i.1.2
  invFun k := ⟨⟨z, k⟩, rfl⟩
  left_inv i := by
    rcases i with ⟨⟨z', k⟩, hz'⟩
    change z' = z at hz'
    subst z'
    rfl
  right_inv k := rfl

/-- The number of canonical occurrences above a nonzero zero is its exact
analytic multiplicity. -/
theorem entireXiPullbackZeroOccurrence_fiber_natCard
    (z : EntireXiPullbackNonzeroZero) :
    Nat.card {i : EntireXiPullbackZeroOccurrence // i.1 = z} =
      analyticOrderNatAt EntireXiPullback z.1 := by
  calc
    Nat.card {i : EntireXiPullbackZeroOccurrence // i.1 = z} =
        Nat.card (Fin (analyticOrderNatAt EntireXiPullback z.1)) :=
      Nat.card_congr (entireXiPullbackZeroOccurrenceFiberEquiv z)
    _ = analyticOrderNatAt EntireXiPullback z.1 := Nat.card_fin _

/-- The location of a multiplicity-bearing nonzero-zero occurrence. -/
def entireXiPullbackZeroOccurrenceLoc
    (i : EntireXiPullbackZeroOccurrence) : Complex :=
  i.1.1

/-- Negation lifts from distinct zeros to the exact multiplicity-bearing
occurrence index. -/
noncomputable def entireXiPullbackZeroOccurrenceNegEquiv :
    EntireXiPullbackZeroOccurrence ≃ EntireXiPullbackZeroOccurrence :=
  Equiv.sigmaCongr entireXiPullbackNonzeroZeroNegEquiv fun z =>
    finCongr (entireXiPullback_analyticOrderNatAt_neg z.1).symm

/-- The lifted occurrence equivalence negates its zero location. -/
@[simp] theorem entireXiPullbackZeroOccurrenceNegEquiv_loc
    (i : EntireXiPullbackZeroOccurrence) :
    entireXiPullbackZeroOccurrenceLoc
        (entireXiPullbackZeroOccurrenceNegEquiv i) =
      -entireXiPullbackZeroOccurrenceLoc i := by
  rfl

/-- The canonical genus-one regularized logarithmic-derivative series is odd.
The regularizing constants cancel under the exact negation pairing of the
divisor occurrences. -/
theorem entireXiPullbackCanonicalRegularizedSeries_neg (z : Complex) :
    hadamardRegularizedLogDerivSeries
        entireXiPullbackZeroOccurrenceLoc (-z) =
      -hadamardRegularizedLogDerivSeries
        entireXiPullbackZeroOccurrenceLoc z := by
  unfold hadamardRegularizedLogDerivSeries
  rw [← entireXiPullbackZeroOccurrenceNegEquiv.tsum_eq]
  rw [← tsum_neg]
  apply tsum_congr
  intro i
  rw [entireXiPullbackZeroOccurrenceNegEquiv_loc]
  have hsub : -z - -entireXiPullbackZeroOccurrenceLoc i =
      -(z - entireXiPullbackZeroOccurrenceLoc i) := by
    ring
  rw [hsub]
  simp only [one_div, inv_neg]
  ring

/-- Every canonical occurrence is located away from the origin. -/
theorem entireXiPullbackZeroOccurrenceLoc_ne_zero
    (i : EntireXiPullbackZeroOccurrence) :
    entireXiPullbackZeroOccurrenceLoc i ≠ 0 :=
  i.1.2.2

/-- Every canonical occurrence is located at a zero of the pullback. -/
theorem entireXiPullbackZeroOccurrenceLoc_is_zero
    (i : EntireXiPullbackZeroOccurrence) :
    EntireXiPullback (entireXiPullbackZeroOccurrenceLoc i) = 0 :=
  i.1.2.1

/-- Every nonzero pullback zero occurs in the canonical multiplicity index. -/
theorem entireXiPullbackZeroOccurrenceLoc_exhaustive
    {z : Complex}
    (hz : EntireXiPullback z = 0) (hz0 : z ≠ 0) :
    ∃ i : EntireXiPullbackZeroOccurrence,
      entireXiPullbackZeroOccurrenceLoc i = z := by
  let rho : EntireXiPullbackNonzeroZero := ⟨z, hz, hz0⟩
  have hpos : 0 < analyticOrderNatAt EntireXiPullback rho.1 :=
    entireXiPullbackNonzeroZero_analyticOrderNatAt_pos rho
  exact ⟨⟨rho, ⟨0, hpos⟩⟩, rfl⟩

/-- Set-level characterization of the canonical occurrence locations. -/
theorem exists_entireXiPullbackZeroOccurrenceLoc_iff (z : Complex) :
    (∃ i : EntireXiPullbackZeroOccurrence,
      entireXiPullbackZeroOccurrenceLoc i = z) ↔
      EntireXiPullback z = 0 ∧ z ≠ 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    exact
      ⟨entireXiPullbackZeroOccurrenceLoc_is_zero i,
        entireXiPullbackZeroOccurrenceLoc_ne_zero i⟩
  · rintro ⟨hz, hz0⟩
    exact entireXiPullbackZeroOccurrenceLoc_exhaustive hz hz0

/-- Zeros of the entire xi pullback are locally finite. -/
theorem entireXiPullback_zeroSet_locallyFinite (p : Complex) :
    ∃ U ∈ nhds p,
      (U ∩ {z : Complex | EntireXiPullback z = 0}).Finite := by
  by_cases hp : EntireXiPullback p = 0
  · have hAn : AnalyticAt Complex EntireXiPullback p :=
      EntireXiPullback_analyticAt p
    rcases hAn.eventually_eq_zero_or_eventually_ne_zero with hlocal | hpunct
    · exact absurd hlocal (EntireXiPullback_not_eventuallyEq_zero p)
    · rw [eventually_nhdsWithin_iff] at hpunct
      refine
        ⟨{z : Complex | z ∈ ({p}ᶜ : Set Complex) → EntireXiPullback z ≠ 0},
          hpunct, ?_⟩
      apply Set.Finite.subset (Set.finite_singleton p)
      rintro z ⟨hzU, hzzero⟩
      by_cases hzp : z = p
      · simp [hzp]
      · have hzmem : z ∈ ({p}ᶜ : Set Complex) := hzp
        exact absurd hzzero (hzU hzmem)
  · have hcont : ContinuousAt EntireXiPullback p :=
      (EntireXiPullback_analyticAt p).continuousAt
    have hEventually_ne :
        ∀ᶠ z in nhds p, EntireXiPullback z ≠ 0 :=
      hcont.eventually_ne hp
    refine ⟨{z : Complex | EntireXiPullback z ≠ 0}, hEventually_ne, ?_⟩
    have hempty :
        {z : Complex | EntireXiPullback z ≠ 0} ∩
            {z : Complex | EntireXiPullback z = 0} =
          ∅ := by
      ext z
      constructor
      · rintro ⟨hz_ne, hz_zero⟩
        exact (hz_ne hz_zero).elim
      · intro hz
        exact absurd hz (Set.notMem_empty z)
    rw [hempty]
    exact Set.finite_empty

/-- Only finitely many distinct pullback zeros lie in any closed norm ball. -/
theorem entireXiPullback_zeroSet_finite_in_closedBall (R : Real) :
    {z : Complex |
      z ∈ Metric.closedBall (0 : Complex) R ∧ EntireXiPullback z = 0}.Finite := by
  classical
  let Z : Set Complex :=
    {z : Complex |
      z ∈ Metric.closedBall (0 : Complex) R ∧ EntireXiPullback z = 0}
  let K : Set Complex := Metric.closedBall (0 : Complex) R
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : Complex) R
  have hZK : Z ⊆ K := by
    intro z hz
    exact hz.1
  have hlocal :
      ∀ p ∈ K, ∃ U ∈ nhds p, (U ∩ Z).Finite := by
    intro p _hp
    obtain ⟨U, hU, hfin⟩ := entireXiPullback_zeroSet_locallyFinite p
    refine ⟨U, hU, ?_⟩
    exact hfin.subset (by
      rintro z ⟨hzU, hz⟩
      exact ⟨hzU, hz.2⟩)
  choose! V hV_nhds hV_finite using hlocal
  obtain ⟨t, ht_sub, ht_cover⟩ := hK.elim_nhds_subcover V hV_nhds
  have hZsubset : Z ⊆ ⋃ p ∈ t, V p ∩ Z := by
    intro z hz
    have hzK : z ∈ K := hZK hz
    obtain ⟨p, hpt, hzVp⟩ := Set.mem_iUnion₂.mp (ht_cover hzK)
    exact Set.mem_iUnion₂.mpr ⟨p, hpt, hzVp, hz⟩
  have hZfinite : Z.Finite := by
    refine Set.Finite.subset ?_ hZsubset
    refine Set.Finite.biUnion t.finite_toSet ?_
    intro p hp
    exact hV_finite p (ht_sub p hp)
  simpa [Z] using hZfinite

/-- The distinct nonzero pullback zeros in a fixed norm ball form a finite
subtype set. -/
private theorem entireXiPullbackNonzeroZero_norm_le_finite (R : Real) :
    {z : EntireXiPullbackNonzeroZero | (norm (z.1) : Real) ≤ R}.Finite := by
  let Z : Set Complex :=
    {z : Complex |
      z ∈ Metric.closedBall (0 : Complex) R ∧ EntireXiPullback z = 0}
  have hZ : Z.Finite := entireXiPullback_zeroSet_finite_in_closedBall R
  apply Set.Finite.of_finite_image
    (s := {z : EntireXiPullbackNonzeroZero | (norm (z.1) : Real) ≤ R})
    (f := fun z : EntireXiPullbackNonzeroZero => z.1)
  · exact hZ.subset (by
      rintro z ⟨rho, hrho, rfl⟩
      refine ⟨?_, rho.2.1⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hrho)
  · exact Subtype.val_injective.injOn

/-- The multiplicity-bearing pullback occurrence locations are norm-proper. -/
theorem entireXiPullbackZeroOccurrenceNormProper :
    HadamardZeroNormProper entireXiPullbackZeroOccurrenceLoc := by
  refine ⟨?_⟩
  intro R
  let S : Set EntireXiPullbackZeroOccurrence :=
    {i : EntireXiPullbackZeroOccurrence |
      norm (entireXiPullbackZeroOccurrenceLoc i) ≤ R}
  have hbase :
      ((fun i : EntireXiPullbackZeroOccurrence => i.1) '' S).Finite := by
    apply (entireXiPullbackNonzeroZero_norm_le_finite R).subset
    rintro rho ⟨i, hi, rfl⟩
    exact hi
  have hfiber :
      ∀ rho ∈
        (fun i : EntireXiPullbackZeroOccurrence => i.1) '' S,
        (S ∩
          (fun i : EntireXiPullbackZeroOccurrence => i.1) ⁻¹' {rho}).Finite := by
    intro rho _hrho
    apply (Set.finite_range
      (fun k : Fin (analyticOrderNatAt EntireXiPullback rho.1) =>
        Sigma.mk rho k)).subset
    intro i hi
    have hirho : i.1 = rho := hi.2
    subst rho
    exact ⟨i.2, rfl⟩
  exact Set.Finite.of_finite_fibers
    (fun i : EntireXiPullbackZeroOccurrence => i.1) hbase hfiber

/-- The zero set of the entire xi pullback is countable. -/
theorem entireXiPullback_zeroSet_countable :
    {z : Complex | EntireXiPullback z = 0}.Countable := by
  let D := MeromorphicOn.divisor EntireXiPullback (Set.univ : Set Complex)
  have hAn : AnalyticOnNhd Complex EntireXiPullback Set.univ :=
    fun z _hz => EntireXiPullback_analyticAt z
  have hfinite :
      ∀ z : (Set.univ : Set Complex),
        meromorphicOrderAt EntireXiPullback z.1 ≠ ⊤ := by
    intro z
    rw [(hAn z.1 z.2).meromorphicOrderAt_eq]
    simpa using entireXiPullback_analyticOrderAt_ne_top z.1
  have hsupport :
      {z : Complex | EntireXiPullback z = 0} = D.support := by
    have hzero := hAn.meromorphicNFOn.zero_set_eq_divisor_support hfinite
    ext z
    have hz := Set.ext_iff.mp hzero z
    simpa [D] using hz
  rw [hsupport]
  exact
    (HereditarilyLindelofSpace.isLindelof D.support).countable_of_isDiscrete
      D.discreteSupport

/-- The subtype of distinct nonzero pullback zeros is countable. -/
noncomputable instance entireXiPullbackNonzeroZero_countable :
    Countable EntireXiPullbackNonzeroZero := by
  exact
    (entireXiPullback_zeroSet_countable.mono (by
      intro z hz
      exact hz.1)).to_subtype

/-- The exact multiplicity-bearing occurrence type is countable. -/
noncomputable instance entireXiPullbackZeroOccurrence_countable :
    Countable EntireXiPullbackZeroOccurrence := by
  unfold EntireXiPullbackZeroOccurrence
  infer_instance

/-- Proposition form of countability for downstream interfaces. -/
theorem entireXiPullbackZeroOccurrence_countable_holds :
    Countable EntireXiPullbackZeroOccurrence := by
  infer_instance

/-- The sole global zero-distribution input not supplied by local analytic
divisor theory: inverse-square summability with exact multiplicities. -/
structure EntireXiPullbackCanonicalZeroDistribution : Prop where
  inv_sq_summable :
    Summable fun i : EntireXiPullbackZeroOccurrence =>
      (norm (entireXiPullbackZeroOccurrenceLoc i) ^ 2)⁻¹

/-- Canonical inverse-square distribution data supplies the complete generic
Hadamard zero summability package; eventual escape follows from norm
properness. -/
theorem EntireXiPullbackCanonicalZeroDistribution.toHadamardZeroInvSqSummability
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    HadamardZeroInvSqSummability entireXiPullbackZeroOccurrenceLoc :=
  HadamardZeroInvSqSummability.of_invSqSummable_normProper
    entireXiPullbackZeroOccurrenceLoc_ne_zero
    H.inv_sq_summable
    entireXiPullbackZeroOccurrenceNormProper

end OverflowResidueRH
