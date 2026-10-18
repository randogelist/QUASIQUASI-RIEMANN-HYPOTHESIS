/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import RiemannHypothesis.HadamardProduct.CanonicalProductDyadicGrowth
import RiemannHypothesis.HadamardProduct.PairedGenusOne

/-!
# Dyadic growth after exact negation pairing

An exact fixed-point-free involution `ρ ↦ -ρ` cancels the exponential
regularizers in opposite genus-one factors:

`E₁(z/ρ) E₁(z/(-ρ)) = 1 - (z/ρ)^2`.

Unlike a separate linear estimate for every factor, the quadratic paired
factor can exploit a cumulative `O(R log R)` divisor count without paying a
second logarithm.  The final theorem below gives an explicit
`O(r (K+1))` exponent on the dyadic annulus `2^(K-1) ≤ r ≤ 2^K`.

The annular lower bound is essential to this formulation: a shell estimate
independent of `z` cannot be absorbed into `r` uniformly all the way down to
`r = 0`.  Pointwise radial packages choose the dyadic annulus containing the
given nonzero `z`.
-/

open Filter Metric Real Set Topology
open scoped Real

namespace OverflowResidueRH

universe u

/-! ## A reusable exact pairing interface -/

/-- One representative from every orbit of a fixed-point-free involution,
using an arbitrary linear order. -/
def involutionHalf {ι : Type u} [LinearOrder ι] (e : ι ≃ ι) : Type u :=
  {i : ι // i < e i}

/-- A fixed-point-free involution decomposes its index type into one
representative and one opposite representative per Boolean fiber. -/
def involutionPairEquiv {ι : Type u} [LinearOrder ι]
    (e : ι ≃ ι) (hinv : Function.Involutive e) (hfree : ∀ i, e i ≠ i) :
    involutionHalf e × Bool ≃ ι where
  toFun p := if p.2 then e p.1.1 else p.1.1
  invFun i := if hi : i < e i then (⟨i, hi⟩, false)
    else (⟨e i, by
      have hle : e i ≤ i := le_of_not_gt hi
      have hne : e i ≠ i := hfree i
      have hlt : e i < i := lt_of_le_of_ne hle hne
      simpa [hinv i] using hlt⟩, true)
  left_inv p := by
    rcases p with ⟨⟨i, hi⟩, b⟩
    cases b with
    | false => simp [hi]
    | true =>
        have hnot : ¬ e i < i := not_lt_of_ge hi.le
        simp [hnot, hinv i]
  right_inv i := by
    by_cases hi : i < e i
    · simp [hi]
    · have hle : e i ≤ i := le_of_not_gt hi
      have hne : e i ≠ i := hfree i
      have hlt : e i < i := lt_of_le_of_ne hle hne
      simp [hi, hinv i]

/-- Exact divisor data for choosing one representative from each
`ρ, -ρ` pair. -/
structure HadamardNegationPairingData
    {ι : Type u} (zeroLoc : ι → ℂ) where
  half : Type u
  pairEquiv : half × Bool ≃ ι
  loc_true : ∀ j, zeroLoc (pairEquiv (j, true)) =
    -zeroLoc (pairEquiv (j, false))

/-- The selected location in one negation orbit. -/
def HadamardNegationPairingData.repLoc
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardNegationPairingData zeroLoc) (j : H.half) : ℂ :=
  zeroLoc (H.pairEquiv (j, false))

/-- Construct exact pairing data from a fixed-point-free location-negating
involution.  The choice of half is noncanonical but the reconstructed full
product is not. -/
noncomputable def HadamardNegationPairingData.ofInvolution
    {ι : Type*} (zeroLoc : ι → ℂ)
    (e : ι ≃ ι) (hinv : Function.Involutive e) (hfree : ∀ i, e i ≠ i)
    (hloc : ∀ i, zeroLoc (e i) = -zeroLoc i) :
    HadamardNegationPairingData zeroLoc := by
  classical
  letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  exact
    { half := involutionHalf e
      pairEquiv := involutionPairEquiv e hinv hfree
      loc_true := by
        intro j
        simpa [involutionPairEquiv] using hloc j.1 }

/-- The quadratic canonical product over one representative from each
opposite pair. -/
noncomputable def pairedQuadraticProduct
    {κ : Type*} (repLoc : κ → ℂ) (z : ℂ) : ℂ :=
  ∏' j : κ, (1 - (z / repLoc j) ^ 2)

private theorem tprod_reindex_bool_pairs
    {ι κ : Type*} (f : ι → ℂ) (e : κ × Bool ≃ ι)
    (hf : Multipliable f) :
    (∏' i : ι, f i) =
      ∏' j : κ, (f (e (j, false)) * f (e (j, true))) := by
  let g : κ × Bool → ℂ := fun p ↦ f (e p)
  have hg : Multipliable g := (e.multipliable_iff).2 hf
  have hgb : ∀ j : κ, Multipliable (fun b : Bool ↦ g (j, b)) := by
    intro j
    exact Multipliable.of_finite
  calc
    (∏' i : ι, f i) = ∏' p : κ × Bool, g p :=
      (e.tprod_eq f).symm
    _ = ∏' j : κ, ∏' b : Bool, g (j, b) := hg.tprod_prod' hgb
    _ = ∏' j : κ, (f (e (j, false)) * f (e (j, true))) := by
      simp only [tprod_bool, g]

/-- Exact reindexing of the full genus-one product as a quadratic paired
product.  Multipliability is used explicitly, so no regrouping of a
nonconvergent totalized product is hidden. -/
theorem HadamardNegationPairingData.infiniteHadamardProduct_eq_paired
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardNegationPairingData zeroLoc)
    (Hinv : HadamardZeroInvSqSummability zeroLoc) (z : ℂ) :
    infiniteHadamardProduct zeroLoc z =
      pairedQuadraticProduct H.repLoc z := by
  unfold infiniteHadamardProduct pairedQuadraticProduct
  rw [tprod_reindex_bool_pairs
    (fun i ↦ hadamardGenus1Factor (zeroLoc i) z) H.pairEquiv
    (Hinv.product_multipliable z)]
  apply tprod_congr
  intro j
  dsimp [HadamardNegationPairingData.repLoc]
  rw [H.loc_true]
  exact hadamardGenus1Factor_mul_neg_location
    (Hinv.zero_ne (H.pairEquiv (j, false)))

/-! ## Pair representatives inherit the full count -/

/-- The representative system is norm-proper because it injects into the
full divisor with exactly the same locations. -/
theorem HadamardNegationPairingData.repLoc_normProper
    {ι : Type*} {zeroLoc : ι → ℂ}
    (P : HadamardNegationPairingData zeroLoc)
    (H : HadamardZeroNormProper zeroLoc) :
    HadamardZeroNormProper P.repLoc := by
  refine ⟨?_⟩
  intro R
  let e : P.half → ι := fun j ↦ P.pairEquiv (j, false)
  have he : Function.Injective e := by
    intro j k hjk
    have hp : (j, false) = (k, false) := P.pairEquiv.injective hjk
    exact congrArg Prod.fst hp
  exact (H.finite_norm_le R).preimage he.injOn

/-- The representative system inherits inverse-square summability. -/
theorem HadamardNegationPairingData.repLoc_invSqSummability
    {ι : Type*} {zeroLoc : ι → ℂ}
    (P : HadamardNegationPairingData zeroLoc)
    (H : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) :
    HadamardZeroInvSqSummability P.repLoc where
  zero_ne j := H.zero_ne (P.pairEquiv (j, false))
  inv_sq_summable := by
    let e : P.half → ι := fun j ↦ P.pairEquiv (j, false)
    have he : Function.Injective e := by
      intro j k hjk
      have hp : (j, false) = (k, false) := P.pairEquiv.injective hjk
      exact congrArg Prod.fst hp
    simpa [HadamardNegationPairingData.repLoc, Function.comp_def] using
      H.inv_sq_summable.comp_injective he
  eventually_large := (P.repLoc_normProper Hproper).eventually_large

/-- A ball of pair representatives has cardinality at most the corresponding
ball of the full occurrence divisor. -/
theorem HadamardNegationPairingData.repLoc_dyadicBallCard_le
    {ι : Type*} {zeroLoc : ι → ℂ}
    (P : HadamardNegationPairingData zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) (n : ℕ) :
    hadamardZeroDyadicBallCard P.repLoc n ≤
      hadamardZeroDyadicBallCard zeroLoc n := by
  let f : {j : P.half // ‖P.repLoc j‖ ≤ (2 : ℝ) ^ n} →
      {i : ι // ‖zeroLoc i‖ ≤ (2 : ℝ) ^ n} :=
    fun j ↦ ⟨P.pairEquiv (j.1, false), j.2⟩
  letI : Finite {i : ι // ‖zeroLoc i‖ ≤ (2 : ℝ) ^ n} :=
    Hproper.finite_norm_le ((2 : ℝ) ^ n)
  unfold hadamardZeroDyadicBallCard
  exact Nat.card_le_card_of_injective f (by
    intro j k hjk
    apply Subtype.ext
    have hp : (j.1, false) = (k.1, false) :=
      P.pairEquiv.injective (congrArg Subtype.val hjk)
    exact congrArg Prod.fst hp)

/-- Restricting the exact pair equivalence to a norm ball identifies the
full multiplicity-bearing ball with two copies of the representative ball.
The statement uses the occurrence type, so repeated zeros remain repeated
on both sides. -/
noncomputable def HadamardNegationPairingData.repLocBallProdBoolEquiv
    {ι : Type*} {zeroLoc : ι → ℂ}
    (P : HadamardNegationPairingData zeroLoc) (R : ℝ) :
    {j : P.half // ‖P.repLoc j‖ ≤ R} × Bool ≃
      {i : ι // ‖zeroLoc i‖ ≤ R} := by
  let hpred : ∀ p : P.half × Bool,
      ‖P.repLoc p.1‖ ≤ R ↔ ‖zeroLoc (P.pairEquiv p)‖ ≤ R := by
    intro p
    rcases p with ⟨j, b⟩
    cases b with
    | false => rfl
    | true =>
        change ‖zeroLoc (P.pairEquiv (j, false))‖ ≤ R ↔
          ‖zeroLoc (P.pairEquiv (j, true))‖ ≤ R
        rw [P.loc_true]
        simp
  exact Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
    (P.pairEquiv.subtypeEquiv hpred)

/-- Exact negation pairing halves every radial occurrence count. -/
theorem HadamardNegationPairingData.dyadicBallCard_eq_two_mul_repLoc
    {ι : Type*} {zeroLoc : ι → ℂ}
    (P : HadamardNegationPairingData zeroLoc) (n : ℕ) :
    hadamardZeroDyadicBallCard zeroLoc n =
      2 * hadamardZeroDyadicBallCard P.repLoc n := by
  unfold hadamardZeroDyadicBallCard
  calc
    Nat.card {i : ι // ‖zeroLoc i‖ ≤ (2 : ℝ) ^ n} =
        Nat.card ({j : P.half // ‖P.repLoc j‖ ≤ (2 : ℝ) ^ n} × Bool) :=
      Nat.card_congr (P.repLocBallProdBoolEquiv ((2 : ℝ) ^ n)).symm
    _ = Nat.card {j : P.half // ‖P.repLoc j‖ ≤ (2 : ℝ) ^ n} *
        Nat.card Bool := Nat.card_prod _ _
    _ = 2 * Nat.card {j : P.half // ‖P.repLoc j‖ ≤ (2 : ℝ) ^ n} := by
      simp [Nat.mul_comm]

/-- An eventual cumulative count for the full divisor transfers, with the
same constants, to one representative from each opposite pair. -/
noncomputable def
    HadamardNegationPairingData.repLocDyadicCumulativeCountData
    {ι : Type*} {zeroLoc : ι → ℂ}
    (P : HadamardNegationPairingData zeroLoc)
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc) :
    HadamardZeroDyadicCumulativeCountData P.repLoc where
  zero_ne j := H.zero_ne (P.pairEquiv (j, false))
  normProper := P.repLoc_normProper H.normProper
  lower := H.lower
  C := H.C
  C₀ := H.C₀
  C_nonneg := H.C_nonneg
  C₀_nonneg := H.C₀_nonneg
  count_le n hn := by
    have hcard :
        (hadamardZeroDyadicBallCard P.repLoc n : ℝ) ≤
          (hadamardZeroDyadicBallCard zeroLoc n : ℝ) := by
      exact_mod_cast P.repLoc_dyadicBallCard_le H.normProper n
    exact hcard.trans (H.count_le n hn)

/-- The quantitatively sharp transfer of a cumulative count to one
representative per opposite pair.  Exact radial pairing divides both visible
count constants by two; the previous same-constant construction is retained
as a convenient monotone compatibility wrapper. -/
noncomputable def
    HadamardNegationPairingData.repLocDyadicCumulativeCountDataHalved
    {ι : Type*} {zeroLoc : ι → ℂ}
    (P : HadamardNegationPairingData zeroLoc)
    (H : HadamardZeroDyadicCumulativeCountData zeroLoc) :
    HadamardZeroDyadicCumulativeCountData P.repLoc where
  zero_ne j := H.zero_ne (P.pairEquiv (j, false))
  normProper := P.repLoc_normProper H.normProper
  lower := H.lower
  C := H.C / 2
  C₀ := H.C₀ / 2
  C_nonneg := div_nonneg H.C_nonneg (by norm_num)
  C₀_nonneg := div_nonneg H.C₀_nonneg (by norm_num)
  count_le n hn := by
    have hfull := H.count_le n hn
    have hcardNat := P.dyadicBallCard_eq_two_mul_repLoc n
    have hcard :
        (hadamardZeroDyadicBallCard zeroLoc n : ℝ) =
          2 * (hadamardZeroDyadicBallCard P.repLoc n : ℝ) := by
      exact_mod_cast hcardNat
    rw [hcard] at hfull
    nlinarith

/-! ## Elementary paired-factor bounds -/

/-- A paired quadratic factor retains the global linear bound obtained by
multiplying the two genus-one bounds.  This estimate is used only for the
fixed finite collection of very small representatives. -/
theorem norm_pairedQuadraticFactor_le_exp_linear
    {ρ z : ℂ} (hρ : ρ ≠ 0) :
    ‖1 - (z / ρ) ^ 2‖ ≤ Real.exp (4 * ‖z‖ / ‖ρ‖) := by
  have hid := hadamardGenus1Factor_mul_neg_location (ρ := ρ) (z := z) hρ
  rw [← hid, norm_mul]
  have hpos : 0 ≤ Real.exp (2 * ‖z‖ / ‖ρ‖) := (Real.exp_pos _).le
  calc
    ‖hadamardGenus1Factor ρ z‖ * ‖hadamardGenus1Factor (-ρ) z‖ ≤
        Real.exp (2 * ‖z‖ / ‖ρ‖) *
          Real.exp (2 * ‖z‖ / ‖-ρ‖) := by
      exact mul_le_mul
        (norm_hadamardGenus1Factor_le_exp_linear ρ z)
        (norm_hadamardGenus1Factor_le_exp_linear (-ρ) z)
        (norm_nonneg _) hpos
    _ = Real.exp (4 * ‖z‖ / ‖ρ‖) := by
      rw [norm_neg, ← Real.exp_add]
      congr 1
      ring

/-- The cancellation-improved global quadratic bound for one paired
factor, with coefficient `1` rather than the genus-one Taylor constant. -/
theorem norm_pairedQuadraticFactor_le_exp_quadratic
    (ρ z : ℂ) :
    ‖1 - (z / ρ) ^ 2‖ ≤
      Real.exp (‖z‖ ^ 2 * (‖ρ‖ ^ 2)⁻¹) := by
  have htriangle : ‖1 - (z / ρ) ^ 2‖ ≤ 1 + ‖z / ρ‖ ^ 2 := by
    calc
      ‖1 - (z / ρ) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖(z / ρ) ^ 2‖ := norm_sub_le _ _
      _ = 1 + ‖z / ρ‖ ^ 2 := by rw [norm_pow]; norm_num
  have hshape : ‖z / ρ‖ ^ 2 = ‖z‖ ^ 2 * (‖ρ‖ ^ 2)⁻¹ := by
    rw [norm_div, div_pow, div_eq_mul_inv]
  rw [hshape] at htriangle
  exact htriangle.trans (by
    simpa [add_comm] using
      Real.add_one_le_exp (‖z‖ ^ 2 * (‖ρ‖ ^ 2)⁻¹))

/-- Inverse-square summability makes the quadratic paired factors
multipliable directly. -/
theorem multipliable_pairedQuadraticFactor
    {κ : Type*} {repLoc : κ → ℂ}
    (H : HadamardZeroInvSqSummability repLoc) (z : ℂ) :
    Multipliable (fun j : κ ↦ 1 - (z / repLoc j) ^ 2) := by
  let a : κ → ℂ := fun j ↦ -(z / repLoc j) ^ 2
  have hnorm : Summable (fun j : κ ↦ ‖a j‖) := by
    have h := H.inv_sq_summable.mul_left (‖z‖ ^ 2)
    apply h.congr
    intro j
    dsimp [a]
    rw [norm_neg, norm_pow, norm_div, div_pow, div_eq_mul_inv]
  have ha : Summable a := Summable.of_norm hnorm
  have hm := Complex.multipliable_one_add_of_summable ha
  simpa [a, sub_eq_add_neg] using hm

/-! ## A dyadic inner-shell factor estimate -/

private theorem pow_two_le_exp_nat (m : ℕ) :
    (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
  calc
    (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := by
      exact pow_le_pow_left₀ (by positivity) Real.exp_one_gt_two.le m
    _ = Real.exp (m : ℝ) := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- On dyadic shell `n ≤ K`, the paired factor costs only linearly in the
shell distance `K-n`, rather than linearly in `2^(K-n)`. -/
theorem norm_pairedQuadraticFactor_le_exp_dyadicShell
    {κ : Type*} {repLoc : κ → ℂ} (j : κ) (z : ℂ)
    (K n : ℕ) (hn_one : 1 ≤ n) (hnK : n ≤ K)
    (hbin : hadamardZeroDyadicBin repLoc j = n)
    (hz : ‖z‖ ≤ (2 : ℝ) ^ K) :
    ‖1 - (z / repLoc j) ^ 2‖ ≤
      Real.exp (3 * (((K - n + 1 : ℕ) : ℝ))) := by
  let d : ℕ := K - n
  have hKd : n + d = K := by omega
  have hlower :=
    pow_two_pred_lt_norm_of_hadamardZeroDyadicBin_eq hn_one hbin
  have hρpos : 0 < ‖repLoc j‖ := (by positivity : 0 < (2 : ℝ) ^ (n - 1)).trans hlower
  have hratio : ‖z / repLoc j‖ ≤ (2 : ℝ) ^ (d + 1) := by
    rw [norm_div, div_le_iff₀ hρpos]
    calc
      ‖z‖ ≤ (2 : ℝ) ^ K := hz
      _ = (2 : ℝ) ^ (d + 1) * (2 : ℝ) ^ (n - 1) := by
        rw [← pow_add]
        congr 2
        omega
      _ ≤ (2 : ℝ) ^ (d + 1) * ‖repLoc j‖ := by
        exact mul_le_mul_of_nonneg_left hlower.le (by positivity)
  have htriangle : ‖1 - (z / repLoc j) ^ 2‖ ≤
      1 + ((2 : ℝ) ^ (d + 1)) ^ 2 := by
    calc
      ‖1 - (z / repLoc j) ^ 2‖ ≤
          ‖(1 : ℂ)‖ + ‖(z / repLoc j) ^ 2‖ := norm_sub_le _ _
      _ = 1 + ‖z / repLoc j‖ ^ 2 := by rw [norm_pow]; norm_num
      _ ≤ 1 + ((2 : ℝ) ^ (d + 1)) ^ 2 := by gcongr
  have hpow :
      1 + ((2 : ℝ) ^ (d + 1)) ^ 2 ≤
        (2 : ℝ) ^ (2 * (d + 1) + 1) := by
    have heq : ((2 : ℝ) ^ (d + 1)) ^ 2 =
        (2 : ℝ) ^ (2 * (d + 1)) := by
      have hd : (d + 1) + (d + 1) = 2 * (d + 1) := by omega
      rw [pow_two, ← pow_add, hd]
    rw [heq]
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * (d + 1)) :=
      one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  have hexp : (2 : ℝ) ^ (2 * (d + 1) + 1) ≤
      Real.exp (3 * ((d + 1 : ℕ) : ℝ)) := by
    calc
      (2 : ℝ) ^ (2 * (d + 1) + 1) ≤
          Real.exp ((2 * (d + 1) + 1 : ℕ) : ℝ) :=
        pow_two_le_exp_nat _
      _ ≤ Real.exp (3 * ((d + 1 : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact_mod_cast (show 2 * (d + 1) + 1 ≤ 3 * (d + 1) by omega)
  change ‖1 - (z / repLoc j) ^ 2‖ ≤
    Real.exp (3 * (((d + 1 : ℕ) : ℝ)))
  exact htriangle.trans (hpow.trans hexp)

/-! ## The weighted dyadic summation -/

private lemma hasSum_succ_mul_half :
    HasSum (fun d : ℕ ↦ ((d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ d) 4 := by
  have hnat := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (r := (1 / 2 : ℝ)) (by norm_num)
  have hgeom :=
    hasSum_geometric_of_norm_lt_one (K := ℝ) (ξ := (1 / 2 : ℝ))
      (by norm_num)
  have hadd := hnat.add hgeom
  norm_num at hadd
  simpa [Nat.cast_add, add_mul] using hadd

private lemma pow_two_sub_eq_mul_half
    (K d : ℕ) (hd : d ≤ K) :
    (2 : ℝ) ^ (K - d) = (2 : ℝ) ^ K * (1 / 2 : ℝ) ^ d := by
  rw [pow_sub₀ (2 : ℝ) (by norm_num) hd, ← inv_pow]
  norm_num

/-- The exact weighted convolution responsible for removing the second
logarithm is bounded by the full first moment of the half-geometric series.
-/
theorem sum_dyadicPairedShellWeight_le (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
        (((K - n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ n)) ≤
      4 * ((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K := by
  let f : ℕ → ℝ := fun n ↦
    ((K - n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n
  rw [← Finset.sum_range_reflect f (K + 1)]
  have hterm : ∀ d ∈ Finset.range (K + 1),
      f (K + 1 - 1 - d) ≤
        (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K) *
          (((d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ d) := by
    intro d hdmem
    have hd : d ≤ K := by simpa [Finset.mem_range] using hdmem
    have hback : K - (K - d) = d := Nat.sub_sub_self hd
    have hindex : ((K - d + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le K d) 1
    dsimp [f]
    rw [hback, pow_two_sub_eq_mul_half K d hd]
    calc
      ((d + 1 : ℕ) : ℝ) * ((K - d + 1 : ℕ) : ℝ) *
          ((2 : ℝ) ^ K * (1 / 2 : ℝ) ^ d) =
          ((K - d + 1 : ℕ) : ℝ) *
            ((2 : ℝ) ^ K * (((d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ d)) := by
        ring
      _ ≤ ((K + 1 : ℕ) : ℝ) *
            ((2 : ℝ) ^ K * (((d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ d)) :=
        mul_le_mul_of_nonneg_right hindex (by positivity)
      _ = (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K) *
            (((d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ d) := by ring
  calc
    (∑ d ∈ Finset.range (K + 1), f (K + 1 - 1 - d)) ≤
        ∑ d ∈ Finset.range (K + 1),
          (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K) *
            (((d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ d) := by
      exact Finset.sum_le_sum hterm
    _ = (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K) *
        ∑ d ∈ Finset.range (K + 1),
          (((d + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ d) := by
      rw [Finset.mul_sum]
    _ ≤ (((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K) * 4 := by
      apply mul_le_mul_of_nonneg_left
      · exact (hasSum_succ_mul_half.summable.sum_le_tsum _
          (fun _ _ ↦ by positivity)).trans_eq hasSum_succ_mul_half.tsum_eq
      · positivity
    _ = 4 * ((K + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K := by ring

/-- The additive constant in a cumulative count contributes only a finite
quadratic polynomial in the dyadic index. -/
theorem sum_dyadicPairedShellDistance_le (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1), ((K - n + 1 : ℕ) : ℝ)) ≤
      (((K + 1 : ℕ) : ℝ) ^ 2) := by
  calc
    (∑ n ∈ Finset.range (K + 1), ((K - n + 1 : ℕ) : ℝ)) ≤
        ∑ _n ∈ Finset.range (K + 1), ((K + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le K n) 1
    _ = (((K + 1 : ℕ) : ℝ) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-! ## Weighted heads under a cumulative count -/

/-- Cardinality of one exact dyadic shell. -/
noncomputable def hadamardZeroDyadicShellCard
    {κ : Type*} (repLoc : κ → ℂ) (n : ℕ) : ℕ :=
  Nat.card {j : κ // hadamardZeroDyadicBin repLoc j = n}

/-- An exact shell injects into its enclosing dyadic ball. -/
theorem hadamardZeroDyadicShellCard_le_ballCard
    {κ : Type*} {repLoc : κ → ℂ}
    (Hproper : HadamardZeroNormProper repLoc) (n : ℕ) :
    hadamardZeroDyadicShellCard repLoc n ≤
      hadamardZeroDyadicBallCard repLoc n := by
  let f : {j : κ // hadamardZeroDyadicBin repLoc j = n} →
      {j : κ // ‖repLoc j‖ ≤ (2 : ℝ) ^ n} :=
    fun j ↦ ⟨j.1, by
      simpa [j.2] using hadamardZero_norm_le_pow_two_dyadicBin repLoc j.1⟩
  letI : Finite {j : κ // ‖repLoc j‖ ≤ (2 : ℝ) ^ n} :=
    Hproper.finite_norm_le ((2 : ℝ) ^ n)
  unfold hadamardZeroDyadicShellCard hadamardZeroDyadicBallCard
  exact Nat.card_le_card_of_injective f (by
    intro j k hjk
    exact Subtype.ext (congrArg
      (fun x : {j : κ // ‖repLoc j‖ ≤ (2 : ℝ) ^ n} ↦ x.1) hjk))

/-- Regroup an arbitrary finite dyadic-head weight by exact shells. -/
theorem sum_hadamardZeroDyadicHead_weight_eq_shellCard
    {κ : Type*} {repLoc : κ → ℂ}
    (Hproper : HadamardZeroNormProper repLoc) (K : ℕ) (w : ℕ → ℝ) :
    (∑ j ∈ hadamardZeroDyadicHeadFinset Hproper K,
        w (hadamardZeroDyadicBin repLoc j)) =
      ∑ n ∈ Finset.range (K + 1),
        (hadamardZeroDyadicShellCard repLoc n : ℝ) * w n := by
  classical
  let F := hadamardZeroDyadicHeadFinset Hproper K
  have hmaps : ∀ j ∈ F,
      hadamardZeroDyadicBin repLoc j ∈ Finset.range (K + 1) := by
    intro j hj
    rw [Finset.mem_range]
    have hj' : hadamardZeroDyadicBin repLoc j ≤ K := by
      simpa [F] using hj
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro n hn
  have hnK : n ≤ K := by
    rw [Finset.mem_range] at hn
    omega
  haveI : Fintype {j : κ // hadamardZeroDyadicBin repLoc j = n} :=
    (hadamardZeroDyadicBin_finite Hproper n).fintype
  unfold hadamardZeroDyadicShellCard
  rw [Nat.card_eq_fintype_card]
  change (∑ j ∈ F with hadamardZeroDyadicBin repLoc j = n,
      w (hadamardZeroDyadicBin repLoc j)) =
    (Fintype.card {j : κ // hadamardZeroDyadicBin repLoc j = n} : ℝ) * w n
  calc
    (∑ j ∈ F with hadamardZeroDyadicBin repLoc j = n,
        w (hadamardZeroDyadicBin repLoc j)) =
        ∑ _j : {j : κ // hadamardZeroDyadicBin repLoc j = n}, w n := by
      refine Finset.sum_bij
        (fun j hj ↦
          (⟨j, (Finset.mem_filter.1 hj).2⟩ :
            {j : κ // hadamardZeroDyadicBin repLoc j = n})) ?_ ?_ ?_ ?_
      · intro j hj
        simp
      · intro j₁ hj₁ j₂ hj₂ heq
        exact congrArg Subtype.val heq
      · intro j hj
        refine ⟨j.1, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨?_, j.2⟩
          rw [mem_hadamardZeroDyadicHeadFinset]
          simpa [j.2] using hnK
        · exact Subtype.ext (by rfl)
      · intro j hj
        rw [(Finset.mem_filter.1 hj).2]
    _ = (Fintype.card {j : κ // hadamardZeroDyadicBin repLoc j = n} : ℝ) *
        w n := by simp

/-- The high part of a paired dyadic head has an explicit `O(2^K K)`
bound.  Bins below `L = max 1 lower` carry weight zero and are handled by
their exact finite reciprocal mass. -/
theorem HadamardZeroDyadicCumulativeCountData.sum_pairedHighWeight_le
    {κ : Type*} {repLoc : κ → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData repLoc)
    (K : ℕ) :
    (∑ j ∈ hadamardZeroDyadicHeadFinset H.normProper K,
        if max 1 H.lower ≤ hadamardZeroDyadicBin repLoc j then
          3 * (((K - hadamardZeroDyadicBin repLoc j + 1 : ℕ) : ℝ))
        else 0) ≤
      12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K +
        3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2) := by
  classical
  let L := max 1 H.lower
  let w : ℕ → ℝ := fun n ↦
    if L ≤ n then 3 * (((K - n + 1 : ℕ) : ℝ)) else 0
  rw [show (∑ j ∈ hadamardZeroDyadicHeadFinset H.normProper K,
      if max 1 H.lower ≤ hadamardZeroDyadicBin repLoc j then
        3 * (((K - hadamardZeroDyadicBin repLoc j + 1 : ℕ) : ℝ)) else 0) =
      ∑ j ∈ hadamardZeroDyadicHeadFinset H.normProper K,
        w (hadamardZeroDyadicBin repLoc j) by rfl]
  rw [sum_hadamardZeroDyadicHead_weight_eq_shellCard H.normProper K w]
  have hpoint : ∀ n ∈ Finset.range (K + 1),
      (hadamardZeroDyadicShellCard repLoc n : ℝ) * w n ≤
        3 * (((K - n + 1 : ℕ) : ℝ)) *
          (H.C * (((n + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ n + H.C₀) := by
    intro n hn
    have hnK : n ≤ K := by simpa [Finset.mem_range] using hn
    by_cases hnL : L ≤ n
    · have hshellNat := hadamardZeroDyadicShellCard_le_ballCard H.normProper n
      have hshell : (hadamardZeroDyadicShellCard repLoc n : ℝ) ≤
          (hadamardZeroDyadicBallCard repLoc n : ℝ) := by exact_mod_cast hshellNat
      have hcount := H.count_le n ((le_max_right 1 H.lower).trans hnL)
      have hcard := hshell.trans hcount
      dsimp [w]
      rw [if_pos hnL]
      have hw0 : 0 ≤ 3 * (((K - n + 1 : ℕ) : ℝ)) :=
        mul_nonneg (by norm_num) (Nat.cast_nonneg _)
      have hmul := mul_le_mul_of_nonneg_right hcard hw0
      simpa [mul_comm] using hmul
    · dsimp [w]
      rw [if_neg hnL]
      have hright : 0 ≤
          3 * (((K - n + 1 : ℕ) : ℝ)) *
            (H.C * (((n + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ n + H.C₀) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (add_nonneg
            (mul_nonneg
              (mul_nonneg H.C_nonneg (Nat.cast_nonneg _)) (by positivity))
            H.C₀_nonneg)
      simpa using hright
  calc
    (∑ n ∈ Finset.range (K + 1),
        (hadamardZeroDyadicShellCard repLoc n : ℝ) * w n) ≤
        ∑ n ∈ Finset.range (K + 1),
          3 * (((K - n + 1 : ℕ) : ℝ)) *
            (H.C * (((n + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ n + H.C₀) :=
      Finset.sum_le_sum hpoint
    _ = ∑ n ∈ Finset.range (K + 1),
          (3 * H.C *
            (((K - n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ n) +
          3 * H.C₀ * ((K - n + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = 3 * H.C *
          (∑ n ∈ Finset.range (K + 1),
            (((K - n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ n)) +
        3 * H.C₀ *
          (∑ n ∈ Finset.range (K + 1),
            ((K - n + 1 : ℕ) : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 3 * H.C *
          (4 * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K) +
        3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sum_dyadicPairedShellWeight_le K)
          (mul_nonneg (by norm_num) H.C_nonneg))
        (mul_le_mul_of_nonneg_left (sum_dyadicPairedShellDistance_le K)
          (mul_nonneg (by norm_num) H.C₀_nonneg))
    _ = 12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K +
        3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2) := by ring

/-- The low-bin indicator inside any larger head sums to the exact low
reciprocal mass. -/
theorem sum_dyadicHead_lowInv_eq_lowInvMass
    {κ : Type*} {repLoc : κ → ℂ}
    (Hproper : HadamardZeroNormProper repLoc)
    (L K : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) :
    (∑ j ∈ hadamardZeroDyadicHeadFinset Hproper K,
        if hadamardZeroDyadicBin repLoc j < L then ‖repLoc j‖⁻¹ else 0) =
      hadamardZeroDyadicLowInvMass repLoc L := by
  classical
  let FK := hadamardZeroDyadicHeadFinset Hproper K
  let FL := hadamardZeroDyadicHeadFinset Hproper (L - 1)
  have hLm : L - 1 < L := by omega
  have hsub : FL ⊆ FK := by
    intro j hj
    rw [mem_hadamardZeroDyadicHeadFinset] at hj ⊢
    exact hj.trans (hLm.le.trans hLK)
  have hzero : ∀ j ∈ FK, j ∉ FL →
      (if hadamardZeroDyadicBin repLoc j < L then ‖repLoc j‖⁻¹ else 0) = 0 := by
    intro j hjK hjnot
    rw [mem_hadamardZeroDyadicHeadFinset] at hjnot
    have hnotlt : ¬ hadamardZeroDyadicBin repLoc j < L := by
      intro hlt
      exact hjnot (Nat.le_sub_one_of_lt hlt)
    rw [if_neg hnotlt]
  calc
    (∑ j ∈ FK,
        if hadamardZeroDyadicBin repLoc j < L then ‖repLoc j‖⁻¹ else 0) =
        ∑ j ∈ FL,
          (if hadamardZeroDyadicBin repLoc j < L then ‖repLoc j‖⁻¹ else 0) :=
      (Finset.sum_subset hsub hzero).symm
    _ = ∑ j ∈ FL, ‖repLoc j‖⁻¹ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mem_hadamardZeroDyadicHeadFinset] at hj
      rw [if_pos (lt_of_le_of_lt hj hLm)]
    _ = ∑ n ∈ Finset.range ((L - 1) + 1),
        hadamardZeroDyadicShellInvMass repLoc n :=
      sum_hadamardZeroDyadicHead_inv_eq_sum_shellInvMass Hproper (L - 1)
    _ = hadamardZeroDyadicLowInvMass repLoc L := by
      unfold hadamardZeroDyadicLowInvMass
      rw [Nat.sub_add_cancel hL]

/-- The inverse-square sum over the complement of the dyadic head is exactly
the sum over bins strictly above `K`. -/
theorem tsum_compl_dyadicHead_invSq_eq_tail
    {κ : Type*} {repLoc : κ → ℂ}
    (Hproper : HadamardZeroNormProper repLoc) (K : ℕ) :
    (∑' j : {j : κ // j ∉ hadamardZeroDyadicHeadFinset Hproper K},
        (‖repLoc j.1‖ ^ 2)⁻¹) =
      ∑' j : {j : κ // K < hadamardZeroDyadicBin repLoc j},
        (‖repLoc j.1‖ ^ 2)⁻¹ := by
  let e : {j : κ // j ∉ hadamardZeroDyadicHeadFinset Hproper K} ≃
      {j : κ // K < hadamardZeroDyadicBin repLoc j} := {
    toFun j := ⟨j.1, by
      rw [← Nat.not_le]
      simpa using j.2⟩
    invFun j := ⟨j.1, by
      rw [mem_hadamardZeroDyadicHeadFinset]
      exact Nat.not_le_of_lt j.2⟩
    left_inv j := Subtype.ext rfl
    right_inv j := Subtype.ext rfl }
  simpa [e] using
    (e.tsum_eq
      (fun j : {j : κ // K < hadamardZeroDyadicBin repLoc j} ↦
        (‖repLoc j.1‖ ^ 2)⁻¹))

/-! ## Explicit paired-product bounds -/

/-- The unsimplified paired head--tail bound.  It exposes separately the
exact finite low mass, the `O(2^K K)` weighted middle shells, and the exact
inverse-square tail forced by the cumulative count. -/
theorem HadamardZeroDyadicCumulativeCountData.norm_pairedQuadraticProduct_le_exp_raw
    {κ : Type*} {repLoc : κ → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData repLoc)
    (K : ℕ) (hK : max 1 H.lower ≤ K)
    (z : ℂ) (hz : ‖z‖ ≤ (2 : ℝ) ^ K) :
    ‖pairedQuadraticProduct repLoc z‖ ≤
      Real.exp
        (4 * ‖z‖ * hadamardZeroDyadicLowInvMass repLoc (max 1 H.lower) +
          (12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K +
            3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2)) +
          ‖z‖ ^ 2 *
            (4 * H.C * (((K + 3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ K) +
              4 * H.C₀ * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ K))) := by
  classical
  let L := max 1 H.lower
  let F := hadamardZeroDyadicHeadFinset H.normProper K
  let b : κ → ℝ := fun j ↦
    if hadamardZeroDyadicBin repLoc j < L then 4 * ‖z‖ / ‖repLoc j‖
    else if hadamardZeroDyadicBin repLoc j ≤ K then
      3 * (((K - hadamardZeroDyadicBin repLoc j + 1 : ℕ) : ℝ))
    else ‖z‖ ^ 2 * (‖repLoc j‖ ^ 2)⁻¹
  have hmul : Multipliable (fun j : κ ↦ 1 - (z / repLoc j) ^ 2) :=
    multipliable_pairedQuadraticFactor H.toHadamardZeroInvSqSummability z
  have hb : Summable b := by
    apply Summable.add_compl (s := F) Summable.of_finite
    have htail := (H.invSq_summable.subtype (fun j ↦ j ∉ F)).mul_left (‖z‖ ^ 2)
    apply htail.congr
    intro j
    have hjK : ¬ hadamardZeroDyadicBin repLoc j.1 ≤ K := by
      simpa [F, mem_hadamardZeroDyadicHeadFinset] using j.2
    have hjL : ¬ hadamardZeroDyadicBin repLoc j.1 < L := by
      intro hjlt
      exact hjK ((Nat.le_of_lt hjlt).trans hK)
    simp [b, hjL, hjK]
  have hb_nonneg : ∀ j, 0 ≤ b j := by
    intro j
    dsimp [b]
    split_ifs <;> positivity
  have hfactor : ∀ j,
      ‖1 - (z / repLoc j) ^ 2‖ ≤ Real.exp (b j) := by
    intro j
    by_cases hjL : hadamardZeroDyadicBin repLoc j < L
    · simp only [b, if_pos hjL]
      exact norm_pairedQuadraticFactor_le_exp_linear (H.zero_ne j)
    · have hjL' : L ≤ hadamardZeroDyadicBin repLoc j := Nat.le_of_not_gt hjL
      by_cases hjK : hadamardZeroDyadicBin repLoc j ≤ K
      · simp only [b, if_neg hjL, if_pos hjK]
        exact norm_pairedQuadraticFactor_le_exp_dyadicShell j z K
          (hadamardZeroDyadicBin repLoc j)
          ((le_max_left 1 H.lower).trans hjL') hjK rfl hz
      · simp only [b, if_neg hjL, if_neg hjK]
        exact norm_pairedQuadraticFactor_le_exp_quadratic (repLoc j) z
  have hmajor := norm_tprod_le_exp_tsum hmul hb hb_nonneg hfactor
  have hhead_eq :
      (∑ j ∈ F, b j) =
        4 * ‖z‖ *
          (∑ j ∈ F,
            if hadamardZeroDyadicBin repLoc j < L then ‖repLoc j‖⁻¹ else 0) +
        ∑ j ∈ F,
          (if L ≤ hadamardZeroDyadicBin repLoc j then
            3 * (((K - hadamardZeroDyadicBin repLoc j + 1 : ℕ) : ℝ))
          else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjK : hadamardZeroDyadicBin repLoc j ≤ K := by
      simpa [F] using hj
    by_cases hjL : hadamardZeroDyadicBin repLoc j < L
    · have hnL : ¬ L ≤ hadamardZeroDyadicBin repLoc j := Nat.not_le_of_lt hjL
      simp [b, hjL, hnL, div_eq_mul_inv]
    · have hLj : L ≤ hadamardZeroDyadicBin repLoc j := Nat.le_of_not_gt hjL
      simp [b, hjL, hLj, hjK]
  have hlow_eq :
      (∑ j ∈ F,
        if hadamardZeroDyadicBin repLoc j < L then ‖repLoc j‖⁻¹ else 0) =
        hadamardZeroDyadicLowInvMass repLoc L := by
    simpa [F, L] using sum_dyadicHead_lowInv_eq_lowInvMass
      H.normProper L K (le_max_left 1 H.lower) hK
  have hhigh :
      (∑ j ∈ F,
          (if L ≤ hadamardZeroDyadicBin repLoc j then
            3 * (((K - hadamardZeroDyadicBin repLoc j + 1 : ℕ) : ℝ))
          else 0)) ≤
        12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K +
          3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2) := by
    simpa [F, L] using H.sum_pairedHighWeight_le K
  have hhead :
      (∑ j ∈ F, b j) ≤
        4 * ‖z‖ * hadamardZeroDyadicLowInvMass repLoc L +
          (12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K +
            3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [hhead_eq, hlow_eq]
    linarith
  have htail_eq :
      (∑' j : {j : κ // j ∉ F}, b j.1) =
        ‖z‖ ^ 2 *
          ∑' j : {j : κ // K < hadamardZeroDyadicBin repLoc j},
            (‖repLoc j.1‖ ^ 2)⁻¹ := by
    calc
      (∑' j : {j : κ // j ∉ F}, b j.1) =
          ∑' j : {j : κ // j ∉ F},
            ‖z‖ ^ 2 * (‖repLoc j.1‖ ^ 2)⁻¹ := by
        apply tsum_congr
        intro j
        have hjK : ¬ hadamardZeroDyadicBin repLoc j.1 ≤ K := by
          simpa [F, mem_hadamardZeroDyadicHeadFinset] using j.2
        have hjL : ¬ hadamardZeroDyadicBin repLoc j.1 < L := by
          intro hjlt
          exact hjK ((Nat.le_of_lt hjlt).trans hK)
        simp [b, hjL, hjK]
      _ = ‖z‖ ^ 2 *
          ∑' j : {j : κ // j ∉ F}, (‖repLoc j.1‖ ^ 2)⁻¹ := by
        rw [tsum_mul_left]
      _ = ‖z‖ ^ 2 *
          ∑' j : {j : κ // K < hadamardZeroDyadicBin repLoc j},
            (‖repLoc j.1‖ ^ 2)⁻¹ := by
        rw [show F = hadamardZeroDyadicHeadFinset H.normProper K by rfl,
          tsum_compl_dyadicHead_invSq_eq_tail H.normProper K]
  have htailBase := H.tailInvSqMass_le K
    ((le_max_right 1 H.lower).trans hK)
  have htail :
      (∑' j : {j : κ // j ∉ F}, b j.1) ≤
        ‖z‖ ^ 2 *
          (4 * H.C * (((K + 3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ K) +
            4 * H.C₀ * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ K)) := by
    rw [htail_eq]
    exact mul_le_mul_of_nonneg_left htailBase (by positivity)
  have htsum := hb.sum_add_tsum_subtype_compl F
  have hexponent : (∑' j, b j) ≤
      4 * ‖z‖ * hadamardZeroDyadicLowInvMass repLoc L +
        (12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K +
          3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2)) +
        ‖z‖ ^ 2 *
          (4 * H.C * (((K + 3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ K) +
            4 * H.C₀ * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ K)) := by
    rw [← htsum]
    exact add_le_add hhead htail
  change ‖∏' j : κ, (1 - (z / repLoc j) ^ 2)‖ ≤ _
  exact hmajor.trans (Real.exp_le_exp.mpr (by simpa [L] using hexponent))

private lemma paired_sq_mul_half_pow_le_self
    (r : ℝ) (K : ℕ) (hr0 : 0 ≤ r) (hr : r ≤ (2 : ℝ) ^ K) :
    r ^ 2 * (1 / 2 : ℝ) ^ K ≤ r := by
  have hpowpos : 0 < (2 : ℝ) ^ K := by positivity
  have hpow : (1 / 2 : ℝ) ^ K = ((2 : ℝ) ^ K)⁻¹ := by
    rw [div_pow]
    norm_num
  have hratio : r * ((2 : ℝ) ^ K)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hpowpos]
    simpa using hr
  rw [hpow]
  calc
    r ^ 2 * ((2 : ℝ) ^ K)⁻¹ = r * (r * ((2 : ℝ) ^ K)⁻¹) := by ring
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left hratio hr0
    _ = r := mul_one r

private lemma paired_sq_mul_quarter_pow_le_self
    (r : ℝ) (K : ℕ) (hr0 : 0 ≤ r) (hr : r ≤ (2 : ℝ) ^ K) :
    r ^ 2 * (1 / 4 : ℝ) ^ K ≤ r := by
  calc
    r ^ 2 * (1 / 4 : ℝ) ^ K ≤ r ^ 2 * (1 / 2 : ℝ) ^ K := by
      gcongr
      norm_num
    _ ≤ r := paired_sq_mul_half_pow_le_self r K hr0 hr

/-- Exact negation pairing removes the logarithmic-square loss.  Under the
same cumulative `O(2^K K)` count, the quadratic paired product has an
explicit `O(2^K K) = O(r log r)` exponent on each dyadic annulus. -/
theorem HadamardZeroDyadicCumulativeCountData.norm_pairedQuadraticProduct_le_exp_rLogR
    {κ : Type*} {repLoc : κ → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData repLoc)
    (K : ℕ) (hK : max 1 H.lower ≤ K)
    (z : ℂ)
    (hzlow : (2 : ℝ) ^ (K - 1) ≤ ‖z‖)
    (hzup : ‖z‖ ≤ (2 : ℝ) ^ K) :
    ‖pairedQuadraticProduct repLoc z‖ ≤
      Real.exp
        ((4 * hadamardZeroDyadicLowInvMass repLoc (max 1 H.lower) +
            32 * H.C + 8 * H.C₀) *
          ‖z‖ * (((K + 1 : ℕ) : ℝ))) := by
  have hraw := H.norm_pairedQuadraticProduct_le_exp_raw K hK z hzup
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  let r : ℝ := ‖z‖
  let low : ℝ := hadamardZeroDyadicLowInvMass repLoc (max 1 H.lower)
  have hKone : 1 ≤ K := (le_max_left 1 H.lower).trans hK
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (K - 1) := one_le_pow₀ (by norm_num)
    exact this.trans (by simpa [r] using hzlow)
  have hpow2 : (2 : ℝ) ^ K ≤ 2 * r := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hKone)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ] at hzlow ⊢
    nlinarith
  have hkpowNat : K + 1 ≤ 2 ^ K := Nat.succ_le_iff.mpr K.lt_two_pow_self
  have hkpow : (((K + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ K := by
    exact_mod_cast hkpowNat
  have hhalf : r ^ 2 * (1 / 2 : ℝ) ^ K ≤ r :=
    paired_sq_mul_half_pow_le_self r K hr0 (by simpa [r] using hzup)
  have hquarter : r ^ 2 * (1 / 4 : ℝ) ^ K ≤ r :=
    paired_sq_mul_quarter_pow_le_self r K hr0 (by simpa [r] using hzup)
  have hk3 : (((K + 3 : ℕ) : ℝ)) ≤ 2 * (((K + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show K + 3 ≤ 2 * (K + 1) by omega)
  have hhighC :
      12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K ≤
        24 * H.C * r * (((K + 1 : ℕ) : ℝ)) := by
    have hm :
        (12 * H.C * (((K + 1 : ℕ) : ℝ))) * (2 : ℝ) ^ K ≤
          (12 * H.C * (((K + 1 : ℕ) : ℝ))) * (2 * r) :=
      mul_le_mul_of_nonneg_left hpow2
        (mul_nonneg
          (mul_nonneg (by norm_num) H.C_nonneg) (Nat.cast_nonneg _))
    nlinarith
  have hhighC₀ :
      3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2) ≤
        6 * H.C₀ * r * (((K + 1 : ℕ) : ℝ)) := by
    have hkp := hkpow.trans hpow2
    have hm :
        (3 * H.C₀ * (((K + 1 : ℕ) : ℝ))) * (((K + 1 : ℕ) : ℝ)) ≤
          (3 * H.C₀ * (((K + 1 : ℕ) : ℝ))) * (2 * r) :=
      mul_le_mul_of_nonneg_left hkp
        (mul_nonneg
          (mul_nonneg (by norm_num) H.C₀_nonneg) (Nat.cast_nonneg _))
    nlinarith
  have htailC :
      r ^ 2 * (4 * H.C *
        (((K + 3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ K)) ≤
        8 * H.C * r * (((K + 1 : ℕ) : ℝ)) := by
    have hm :
        (4 * H.C * r) * (((K + 3 : ℕ) : ℝ)) ≤
          (4 * H.C * r) * (2 * (((K + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hk3
        (mul_nonneg (mul_nonneg (by norm_num) H.C_nonneg) hr0)
    have ht :
        (4 * H.C * (((K + 3 : ℕ) : ℝ))) *
            (r ^ 2 * (1 / 2 : ℝ) ^ K) ≤
          (4 * H.C * (((K + 3 : ℕ) : ℝ))) * r :=
      mul_le_mul_of_nonneg_left hhalf
        (mul_nonneg
          (mul_nonneg (by norm_num) H.C_nonneg) (Nat.cast_nonneg _))
    nlinarith
  have htailC₀ :
      r ^ 2 * (4 * H.C₀ * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ K)) ≤
        2 * H.C₀ * r * (((K + 1 : ℕ) : ℝ)) := by
    have hkcast : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_pos K)
    have hrk : r ≤ r * (((K + 1 : ℕ) : ℝ)) := by
      nlinarith
    have hm : (4 / 3 : ℝ) * H.C₀ * r ≤
        (4 / 3 : ℝ) * H.C₀ * (r * (((K + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hrk
        (mul_nonneg (by norm_num) H.C₀_nonneg)
    have ht : (4 / 3 : ℝ) * H.C₀ *
        (r ^ 2 * (1 / 4 : ℝ) ^ K) ≤ (4 / 3 : ℝ) * H.C₀ * r :=
      mul_le_mul_of_nonneg_left hquarter
        (mul_nonneg (by norm_num) H.C₀_nonneg)
    nlinarith
  change
    4 * r * low +
        (12 * H.C * (((K + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ K +
          3 * H.C₀ * (((K + 1 : ℕ) : ℝ) ^ 2)) +
        r ^ 2 *
          (4 * H.C * (((K + 3 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ K) +
            4 * H.C₀ * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ K)) ≤
      (4 * low + 32 * H.C + 8 * H.C₀) * r * (((K + 1 : ℕ) : ℝ))
  have hlow0 : 0 ≤ low := hadamardZeroDyadicLowInvMass_nonneg _ _
  have hkcast : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_pos K)
  have hlow : 4 * r * low ≤ 4 * low * r * (((K + 1 : ℕ) : ℝ)) := by
    have hm : 4 * low * r * 1 ≤
        4 * low * r * (((K + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hkcast
        (mul_nonneg (mul_nonneg (by norm_num) hlow0) hr0)
    nlinarith
  nlinarith [hhighC, hhighC₀, htailC, htailC₀]

/-- Logarithmic form of the paired `O(r log r)` bound. -/
theorem HadamardZeroDyadicCumulativeCountData.log_norm_pairedQuadraticProduct_le_rLogR
    {κ : Type*} {repLoc : κ → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData repLoc)
    (K : ℕ) (hK : max 1 H.lower ≤ K)
    (z : ℂ)
    (hzlow : (2 : ℝ) ^ (K - 1) ≤ ‖z‖)
    (hzup : ‖z‖ ≤ (2 : ℝ) ^ K) :
    Real.log ‖pairedQuadraticProduct repLoc z‖ ≤
      (4 * hadamardZeroDyadicLowInvMass repLoc (max 1 H.lower) +
          32 * H.C + 8 * H.C₀) *
        ‖z‖ * (((K + 1 : ℕ) : ℝ)) := by
  by_cases hp : pairedQuadraticProduct repLoc z = 0
  · rw [hp, norm_zero, Real.log_zero]
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg (by norm_num)
              (hadamardZeroDyadicLowInvMass_nonneg repLoc (max 1 H.lower)))
            (mul_nonneg (by norm_num) H.C_nonneg))
          (mul_nonneg (by norm_num) H.C₀_nonneg))
        (norm_nonneg z))
      (Nat.cast_nonneg _)
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hp)).2
      (H.norm_pairedQuadraticProduct_le_exp_rLogR K hK z hzlow hzup)

/-- Reusable annular `O(r log r)` growth data for an exactly paired
quadratic canonical product. -/
structure HadamardPairedCanonicalProductDyadicRLogRGrowthData
    {κ : Type*} (repLoc : κ → ℂ) : Type where
  lower : ℕ
  coefficient : ℝ
  lower_one : 1 ≤ lower
  coefficient_nonneg : 0 ≤ coefficient
  norm_le : ∀ K : ℕ, lower ≤ K → ∀ z : ℂ,
    (2 : ℝ) ^ (K - 1) ≤ ‖z‖ → ‖z‖ ≤ (2 : ℝ) ^ K →
      ‖pairedQuadraticProduct repLoc z‖ ≤
        Real.exp (coefficient * ‖z‖ * (((K + 1 : ℕ) : ℝ)))

/-- A cumulative dyadic count supplies paired `O(r log r)` growth data. -/
noncomputable def
    HadamardZeroDyadicCumulativeCountData.toPairedCanonicalProductDyadicRLogRGrowthData
    {κ : Type*} {repLoc : κ → ℂ}
    (H : HadamardZeroDyadicCumulativeCountData repLoc) :
    HadamardPairedCanonicalProductDyadicRLogRGrowthData repLoc where
  lower := max 1 H.lower
  coefficient :=
    4 * hadamardZeroDyadicLowInvMass repLoc (max 1 H.lower) +
      32 * H.C + 8 * H.C₀
  lower_one := le_max_left 1 H.lower
  coefficient_nonneg := by
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num)
          (hadamardZeroDyadicLowInvMass_nonneg repLoc (max 1 H.lower)))
        (mul_nonneg (by norm_num) H.C_nonneg))
      (mul_nonneg (by norm_num) H.C₀_nonneg)
  norm_le K hK z hzlow hzup :=
    H.norm_pairedQuadraticProduct_le_exp_rLogR K hK z hzlow hzup

end OverflowResidueRH
