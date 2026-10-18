/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.PairedCanonicalProductGrowth
import RiemannHypothesis.Xi.CompletedLFunctionInstance

/-!
# Exact opposite pairing removes the xi product's logarithmic-square loss

The nonzero multiplicity-bearing xi divisor has a fixed-point-free negation
involution.  Selecting one occurrence from each pair, the full genus-one
product is exactly the quadratic product

`∏ (1 - (z/ρ)^2)`.

The generic paired dyadic theorem therefore improves the previously proved
`O(r log^2 r)` exponent to `O(r log r)` on dyadic annuli.  This is a growth
theorem for the canonical product, not a zero-location theorem and not a
proof of RH.
-/

namespace OverflowResidueRH

/-- Negation on the exact xi occurrence divisor is involutive. -/
theorem entireXiPullbackZeroOccurrenceNegEquiv_involutive :
    Function.Involutive entireXiPullbackZeroOccurrenceNegEquiv := by
  intro i
  let j := entireXiPullbackZeroOccurrenceNegEquiv
      (entireXiPullbackZeroOccurrenceNegEquiv i)
  have hfst : j.fst = i.fst := by
    apply Subtype.ext
    change - -i.fst.1 = i.fst.1
    simp
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (by rw [hfst])).2
  rfl

/-- No nonzero xi occurrence is fixed by the negation involution. -/
theorem entireXiPullbackZeroOccurrenceNegEquiv_fixedPointFree
    (i : EntireXiPullbackZeroOccurrence) :
    entireXiPullbackZeroOccurrenceNegEquiv i ≠ i := by
  intro hi
  have hloc := entireXiPullbackZeroOccurrenceNegEquiv_loc i
  rw [hi] at hloc
  have htwo : (2 : ℂ) * entireXiPullbackZeroOccurrenceLoc i = 0 := by
    linear_combination hloc
  have hzero : entireXiPullbackZeroOccurrenceLoc i = 0 := by
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact entireXiPullbackZeroOccurrenceLoc_ne_zero i hzero

/-- A noncanonical choice of one occurrence from every exact `ρ,-ρ` pair
in the nonzero xi divisor. -/
noncomputable def entireXiPullbackZeroOccurrenceNegationPairingData :
    HadamardNegationPairingData entireXiPullbackZeroOccurrenceLoc :=
  HadamardNegationPairingData.ofInvolution
    entireXiPullbackZeroOccurrenceLoc
    entireXiPullbackZeroOccurrenceNegEquiv
    entireXiPullbackZeroOccurrenceNegEquiv_involutive
    entireXiPullbackZeroOccurrenceNegEquiv_fixedPointFree
    entireXiPullbackZeroOccurrenceNegEquiv_loc

/-- The full nonzero xi genus-one product is exactly the paired quadratic
product. -/
theorem entireXiPullbackInfiniteHadamardProduct_eq_pairedQuadraticProduct
    (z : ℂ) :
    infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc z =
      pairedQuadraticProduct
        entireXiPullbackZeroOccurrenceNegationPairingData.repLoc z :=
  entireXiPullbackZeroOccurrenceNegationPairingData
    |>.infiniteHadamardProduct_eq_paired
      entireXiPullbackCompletedLFunctionHadamardData.zeroData z

/-- The selected half-divisor inherits the unconditional xi cumulative
dyadic count. -/
noncomputable def entireXiPullbackPairedRepDyadicCumulativeCountData :
    HadamardZeroDyadicCumulativeCountData
      entireXiPullbackZeroOccurrenceNegationPairingData.repLoc :=
  entireXiPullbackZeroOccurrenceNegationPairingData
    |>.repLocDyadicCumulativeCountDataHalved
      entireXiPullbackCompletedLFunctionHadamardData.dyadicZeros

/-- Unconditional annular `O(r log r)` growth data for the paired nonzero xi
canonical product. -/
noncomputable def entireXiPullbackPairedCanonicalProductDyadicRLogRGrowthData :
    HadamardPairedCanonicalProductDyadicRLogRGrowthData
      entireXiPullbackZeroOccurrenceNegationPairingData.repLoc :=
  entireXiPullbackPairedRepDyadicCumulativeCountData
    |>.toPairedCanonicalProductDyadicRLogRGrowthData

/-- Exact pairing improves the actual full nonzero xi genus-one product to
an explicit annular `O(r log r)` exponent. -/
theorem entireXiPullbackNonzeroCanonicalProduct_norm_le_exp_rLogR
    (K : ℕ)
    (hK : entireXiPullbackPairedCanonicalProductDyadicRLogRGrowthData.lower ≤ K)
    (z : ℂ)
    (hzlow : (2 : ℝ) ^ (K - 1) ≤ ‖z‖)
    (hzup : ‖z‖ ≤ (2 : ℝ) ^ K) :
    ‖infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc z‖ ≤
      Real.exp
        (entireXiPullbackPairedCanonicalProductDyadicRLogRGrowthData.coefficient *
          ‖z‖ * (((K + 1 : ℕ) : ℝ))) := by
  rw [entireXiPullbackInfiniteHadamardProduct_eq_pairedQuadraticProduct]
  exact entireXiPullbackPairedCanonicalProductDyadicRLogRGrowthData.norm_le
    K hK z hzlow hzup

end OverflowResidueRH
