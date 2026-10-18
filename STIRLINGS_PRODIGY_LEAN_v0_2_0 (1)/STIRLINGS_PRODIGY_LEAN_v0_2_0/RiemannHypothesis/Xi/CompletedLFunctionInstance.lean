/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.CompletedLFunction
import RiemannHypothesis.Xi.UnconditionalLagariasEquivalence

/-!
# The Riemann xi pullback as a generic completed L-function

This module instantiates the reusable `CompletedLFunctionHadamardData`
architecture with the actual centered Riemann xi pullback and its
multiplicity-bearing occurrence divisor.  It is an integration theorem: the
generic completed-L-function criterion is not merely an abstract interface;
all of its fields are inhabited by the unconditional theta/Jensen and
quotient-growth construction.
-/

namespace OverflowResidueRH

/-- The actual centered Riemann xi pullback inhabits the generic completed
L-function Hadamard interface with no auxiliary hypothesis. -/
noncomputable def entireXiPullbackCompletedLFunctionHadamardData :
    CompletedLFunctionHadamardData
      EntireXiPullback EntireXiPullbackZeroOccurrence := by
  let Hboundary := entireXiPullbackThetaDyadicBoundaryGrowthData
  let Hcount := Hboundary.toDyadicCumulativeCountData
  let Hgeneric := Hcount.toGeneric
  let Hdist := Hboundary.toCanonicalZeroDistribution
  let Hlog := entireXiPullbackCanonicalHadamardLogDerivativeDataUnconditional
  refine
    { analytic := fun z _hz => EntireXiPullback_analyticAt z
      nontrivial := ⟨Complex.I / 2, ?_⟩
      even := EntireXiPullback_neg
      schwarz := EntireXiPullback_schwarz
        (EntireRiemannXiRegularity_of_schwarz
          EntireXi.schwarzReflection_holds)
      originMultiplicity := entireXiPullbackOriginMultiplicity
      zeroLoc := entireXiPullbackZeroOccurrenceLoc
      dyadicZeros := Hgeneric
      zeroLoc_is_zero := entireXiPullbackZeroOccurrenceLoc_is_zero
      analyticOrderAt_eq := ?_
      b := 0
      b_im := by simp
      logDerivative_expansion := ?_
      support_nonempty := Hlog.support_nonempty }
  · rw [EntireXiPullback_apply_I_div_two]
    norm_num
  · intro z
    rw [← entireXiPullbackCanonicalProduct_analyticOrderAt Hdist z]
    simpa [entireXiPullbackCanonicalProduct, canonicalProductWithOrigin] using
      (canonicalProductWithOrigin_analyticOrderAt
        entireXiPullbackOriginMultiplicity
        Hgeneric.toHadamardZeroInvSqSummability Hgeneric.normProper z)
  · intro z hz0 hzloc
    simpa using
      (entireXiPullback_logDerivative_canonicalExpansion_unconditional
        z hz0 hzloc)

/-- The generic completed-L-function capstone specializes to the actual xi
pullback without introducing a second proof of the criterion. -/
theorem entireXiPullback_onlyRealZeros_iff_strictAntiHerglotz_generic :
    HasOnlyRealZeros EntireXiPullback ↔
      StrictAntiHerglotzUHP (logDerivativeResponse EntireXiPullback) :=
  entireXiPullbackCompletedLFunctionHadamardData
    |>.onlyRealZeros_iff_strictAntiHerglotz

end OverflowResidueRH
