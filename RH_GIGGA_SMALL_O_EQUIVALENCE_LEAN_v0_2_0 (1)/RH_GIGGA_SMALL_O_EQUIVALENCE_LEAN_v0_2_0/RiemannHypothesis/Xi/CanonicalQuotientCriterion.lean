/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.ComplexAnalysis.EntireQuotient
import RiemannHypothesis.HadamardProduct.CanonicalProductMultiplicity
import RiemannHypothesis.Reduction.BacklundCanonicalDivisor
import RiemannHypothesis.Xi.DyadicZeroCountBridge
import RiemannHypothesis.Xi.HadamardLogDerivativeCriterion

/-!
# The canonical xi quotient and the remaining growth input

Once the occurrence-indexed canonical divisor has inverse-square
distribution, its genus-one product has exactly the analytic divisor of the
entire xi pullback.  This file completes their quotient across the common
zeros, proves that the completion is entire and nowhere zero, and constructs
an entire logarithm without choosing pointwise branches.

The final data structure adds only one analytic assertion to the canonical
zero-distribution input: that this automatically constructed logarithm has
subquadratic norm growth.  Cauchy rigidity then makes the logarithm affine
and yields the full punctured logarithmic-derivative expansion used by the
strict Lagarias equivalence.
-/

namespace OverflowResidueRH

/-- The normal-form completion of the quotient of the xi pullback by its
occurrence-indexed canonical genus-one product. -/
noncomputable def entireXiPullbackCanonicalQuotient : ℂ → ℂ :=
  entireQuotientCompletion EntireXiPullback entireXiPullbackCanonicalProduct

/-- Divisor equality makes the canonical completed quotient entire. -/
theorem entireXiPullbackCanonicalQuotient_differentiable
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    Differentiable ℂ entireXiPullbackCanonicalQuotient := by
  exact entireQuotientCompletion_differentiable
    EntireXiPullback_differentiable
    (entireXiPullbackCanonicalProduct_differentiable H)
    (fun z ↦ (entireXiPullbackCanonicalProduct_analyticOrderAt H z).symm)
    entireXiPullback_analyticOrderAt_ne_top

/-- The completed canonical quotient has no zeros. -/
theorem entireXiPullbackCanonicalQuotient_ne_zero
    (H : EntireXiPullbackCanonicalZeroDistribution) (z : ℂ) :
    entireXiPullbackCanonicalQuotient z ≠ 0 := by
  exact entireQuotientCompletion_ne_zero
    EntireXiPullback_differentiable
    (entireXiPullbackCanonicalProduct_differentiable H)
    (fun w ↦ (entireXiPullbackCanonicalProduct_analyticOrderAt H w).symm)
    entireXiPullback_analyticOrderAt_ne_top z

/-- Away from a zero of the canonical product, the completion is the ordinary
quotient. -/
theorem entireXiPullbackCanonicalQuotient_eq_div
    (H : EntireXiPullbackCanonicalZeroDistribution) {z : ℂ}
    (hz : entireXiPullbackCanonicalProduct z ≠ 0) :
    entireXiPullbackCanonicalQuotient z =
      EntireXiPullback z / entireXiPullbackCanonicalProduct z := by
  exact entireQuotientCompletion_eq_div
    EntireXiPullback_differentiable
    (entireXiPullbackCanonicalProduct_differentiable H) hz

/-- The canonical completed quotient admits a global entire logarithm. -/
theorem exists_differentiable_log_entireXiPullbackCanonicalQuotient
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    ∃ h : ℂ → ℂ,
      Differentiable ℂ h ∧
        ∀ z : ℂ, Complex.exp (h z) = entireXiPullbackCanonicalQuotient z :=
  exists_differentiable_log_of_differentiable_ne_zero
    (entireXiPullbackCanonicalQuotient_differentiable H)
    (entireXiPullbackCanonicalQuotient_ne_zero H)

/-- A fixed global entire logarithm of the canonical completed quotient.
Its existence and logarithm identity are theorems; no branch choice is part
of the later growth interface. -/
noncomputable def entireXiPullbackCanonicalQuotientLog
    (H : EntireXiPullbackCanonicalZeroDistribution) : ℂ → ℂ :=
  Classical.choose
    (exists_differentiable_log_entireXiPullbackCanonicalQuotient H)

theorem entireXiPullbackCanonicalQuotientLog_differentiable
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    Differentiable ℂ (entireXiPullbackCanonicalQuotientLog H) :=
  (Classical.choose_spec
    (exists_differentiable_log_entireXiPullbackCanonicalQuotient H)).1

theorem exp_entireXiPullbackCanonicalQuotientLog
    (H : EntireXiPullbackCanonicalZeroDistribution) (z : ℂ) :
    Complex.exp (entireXiPullbackCanonicalQuotientLog H z) =
      entireXiPullbackCanonicalQuotient z :=
  (Classical.choose_spec
    (exists_differentiable_log_entireXiPullbackCanonicalQuotient H)).2 z

/-- Two entire logarithms with the same exponential differ by a constant.
This derivative proof avoids classifying the pointwise fibers of `exp`. -/
theorem differentiable_logs_eq_add_const
    {h k : ℂ → ℂ} (hh : Differentiable ℂ h) (hk : Differentiable ℂ k)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = Complex.exp (k z)) :
    ∃ c : ℂ, ∀ z : ℂ, k z = h z + c := by
  have hfun : (fun z : ℂ ↦ Complex.exp (h z)) =
      fun z : ℂ ↦ Complex.exp (k z) :=
    funext hexp
  have hderiv : ∀ z : ℂ, deriv k z = deriv h z := by
    intro z
    have hd := congrArg (fun f : ℂ → ℂ ↦ deriv f z) hfun
    rw [deriv_cexp (hh z), deriv_cexp (hk z), hexp z] at hd
    exact (mul_left_cancel₀ (Complex.exp_ne_zero (k z)) hd).symm
  have hdiff : Differentiable ℂ (fun z ↦ k z - h z) := hk.sub hh
  have hdiffDeriv : ∀ z : ℂ, deriv (fun w ↦ k w - h w) z = 0 := by
    intro z
    change deriv (k - h) z = 0
    rw [deriv_sub (hk z) (hh z), hderiv z, sub_self]
  let c : ℂ := k 0 - h 0
  refine ⟨c, fun z ↦ ?_⟩
  have hconst : k z - h z = c :=
    is_const_of_deriv_eq_zero hdiff hdiffDeriv z 0
  dsimp [c] at hconst ⊢
  linear_combination hconst

/-- Matched analytic orders transfer a zero of the canonical product to a
zero of the xi pullback. -/
private theorem EntireXiPullback_eq_zero_of_canonicalProduct_eq_zero
    (H : EntireXiPullbackCanonicalZeroDistribution) {z : ℂ}
    (hz : entireXiPullbackCanonicalProduct z = 0) :
    EntireXiPullback z = 0 := by
  by_contra hxi
  have hxiOrder : analyticOrderAt EntireXiPullback z = 0 :=
    (EntireXiPullback_analyticAt z).analyticOrderAt_eq_zero.mpr hxi
  have hproductOrder :
      analyticOrderAt entireXiPullbackCanonicalProduct z = 0 := by
    rw [entireXiPullbackCanonicalProduct_analyticOrderAt H z, hxiOrder]
  have hproductNe : entireXiPullbackCanonicalProduct z ≠ 0 :=
    ((entireXiPullbackCanonicalProduct_differentiable H).analyticAt z)
      |>.analyticOrderAt_eq_zero.mp hproductOrder
  exact hproductNe hz

/-- Any global logarithm of the completed quotient gives a factorization of
the xi pullback, including at the common zeros. -/
theorem EntireXiPullback_eq_exp_mul_canonicalProduct_of_quotientLog
    (H : EntireXiPullbackCanonicalZeroDistribution) {h : ℂ → ℂ}
    (hexp : ∀ w : ℂ,
      Complex.exp (h w) = entireXiPullbackCanonicalQuotient w) (z : ℂ) :
    EntireXiPullback z =
      Complex.exp (h z) * entireXiPullbackCanonicalProduct z := by
  by_cases hz : entireXiPullbackCanonicalProduct z = 0
  · rw [EntireXiPullback_eq_zero_of_canonicalProduct_eq_zero H hz, hz, mul_zero]
  · rw [hexp z,
      entireXiPullbackCanonicalQuotient_eq_div H hz,
      div_mul_cancel₀ _ hz]

/-- The xi pullback is the exponential of the fixed global quotient logarithm
times the canonical product. -/
theorem EntireXiPullback_eq_exp_canonicalQuotientLog_mul_canonicalProduct
    (H : EntireXiPullbackCanonicalZeroDistribution) (z : ℂ) :
    EntireXiPullback z =
      Complex.exp (entireXiPullbackCanonicalQuotientLog H z) *
        entireXiPullbackCanonicalProduct z :=
  EntireXiPullback_eq_exp_mul_canonicalProduct_of_quotientLog H
    (exp_entireXiPullbackCanonicalQuotientLog H) z

/-- The canonical product is nonzero away from the origin and all indexed
nonzero zero occurrences. -/
theorem entireXiPullbackCanonicalProduct_ne_zero_of_away
    (H : EntireXiPullbackCanonicalZeroDistribution) {z : ℂ}
    (hz0 : z ≠ 0)
    (hzloc : ∀ i : EntireXiPullbackZeroOccurrence,
      z ≠ entireXiPullbackZeroOccurrenceLoc i) :
    entireXiPullbackCanonicalProduct z ≠ 0 := by
  exact mul_ne_zero
    (pow_ne_zero entireXiPullbackOriginMultiplicity hz0)
    (H.toHadamardZeroInvSqSummability.infiniteProduct_ne_zero hzloc)

/-- Off the canonical divisor, the logarithmic derivative of the canonical
product is the origin pole plus the regularized occurrence series. -/
theorem logDerivativeResponse_entireXiPullbackCanonicalProduct
    (H : EntireXiPullbackCanonicalZeroDistribution) {z : ℂ}
    (hz0 : z ≠ 0)
    (hzloc : ∀ i : EntireXiPullbackZeroOccurrence,
      z ≠ entireXiPullbackZeroOccurrenceLoc i) :
    logDerivativeResponse entireXiPullbackCanonicalProduct z =
      (entireXiPullbackOriginMultiplicity : ℂ) / z +
        hadamardRegularizedLogDerivSeries
          entireXiPullbackZeroOccurrenceLoc z := by
  have hpowDiff : DifferentiableAt ℂ
      (fun w : ℂ ↦ w ^ entireXiPullbackOriginMultiplicity) z := by
    fun_prop
  have hproductDiff : DifferentiableAt ℂ
      (infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc) z :=
    (infiniteHadamardProduct_differentiable_of_invSq_normProper
      H.toHadamardZeroInvSqSummability
      entireXiPullbackZeroOccurrenceNormProper) z
  have hpowNe : z ^ entireXiPullbackOriginMultiplicity ≠ 0 :=
    pow_ne_zero entireXiPullbackOriginMultiplicity hz0
  have hproductNe :
      infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc z ≠ 0 :=
    H.toHadamardZeroInvSqSummability.infiniteProduct_ne_zero hzloc
  change logDerivativeResponse
      (fun w : ℂ ↦ w ^ entireXiPullbackOriginMultiplicity *
        infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc w) z = _
  rw [logDerivativeResponse_mul_eq_add hpowDiff hproductDiff hpowNe hproductNe,
    logDerivativeResponse_pow_id,
    logDerivativeResponse_infiniteHadamardProduct_eq_tsum_indexed
      H.toHadamardZeroInvSqSummability
      entireXiPullbackZeroOccurrenceNormProper hzloc]

/-- An affine-exponential factorization over the canonical product supplies
the canonical logarithmic-derivative package.  This algebraic endpoint is
shared by both the fixed-log and explicit-log growth interfaces below. -/
noncomputable def
    EntireXiPullbackCanonicalHadamardLogDerivativeData.of_expAffineCanonicalProduct
    (Hdist : EntireXiPullbackCanonicalZeroDistribution) (a b : ℂ)
    (hfactor : ∀ z : ℂ,
      EntireXiPullback z = Complex.exp (a + b * z) *
        entireXiPullbackCanonicalProduct z) :
    EntireXiPullbackCanonicalHadamardLogDerivativeData := by
  refine
    { zeroDistribution := Hdist
      b := b
      logDerivative_expansion := ?_ }
  intro z hz0 hzloc
  have hfun : EntireXiPullback = fun w : ℂ ↦
      Complex.exp (a + b * w) * entireXiPullbackCanonicalProduct w :=
    funext hfactor
  have hprefDiff : DifferentiableAt ℂ
      (fun w : ℂ ↦ Complex.exp (a + b * w)) z := by
    fun_prop
  have hproductDiff : DifferentiableAt ℂ
      entireXiPullbackCanonicalProduct z :=
    (entireXiPullbackCanonicalProduct_differentiable Hdist) z
  have hprefNe : Complex.exp (a + b * z) ≠ 0 := Complex.exp_ne_zero _
  have hproductNe : entireXiPullbackCanonicalProduct z ≠ 0 :=
    entireXiPullbackCanonicalProduct_ne_zero_of_away Hdist hz0 hzloc
  have hprefLog : logDerivativeResponse
      (fun w : ℂ ↦ Complex.exp (a + b * w)) z = b := by
    simpa using
      (logDerivativeResponse_exp_affine_prefactor
        (C := (1 : ℂ)) (a := a) (b := b) (s := z) one_ne_zero)
  rw [hfun,
    logDerivativeResponse_mul_eq_add
      hprefDiff hproductDiff hprefNe hproductNe,
    hprefLog,
    logDerivativeResponse_entireXiPullbackCanonicalProduct Hdist hz0 hzloc]
  ring

/-- The sharpened remaining analytic interface.  The quotient, its global
logarithm, its differentiability, and its exponential identity have already
been constructed.  Beyond canonical zero distribution, the sole field is the
classical subquadratic growth estimate for that logarithm. -/
structure EntireXiPullbackCanonicalQuotientGrowthData : Type where
  zeroDistribution : EntireXiPullbackCanonicalZeroDistribution
  quotientLog_subquadratic :
    HasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog zeroDistribution)

/-- A witness-oriented version of the growth interface.  This is convenient
when an analytic argument naturally constructs a particular primitive or
Hadamard quotient logarithm: the witness can be used directly, without
proving a growth estimate for the opaque fixed `Classical.choose` logarithm.

The differentiability and exponential-identity fields say only that
`quotientLog` is a legitimate entire logarithm of the already constructed
quotient.  The genuinely additional estimate is `quotientLog_subquadratic`.
-/
structure EntireXiPullbackCanonicalExplicitQuotientLogGrowthData : Type where
  zeroDistribution : EntireXiPullbackCanonicalZeroDistribution
  quotientLog : ℂ → ℂ
  quotientLog_differentiable : Differentiable ℂ quotientLog
  exp_quotientLog_eq : ∀ z : ℂ,
    Complex.exp (quotientLog z) = entireXiPullbackCanonicalQuotient z
  quotientLog_subquadratic : HasSubquadraticNormGrowth quotientLog

/-- The fixed-log interface can always be exposed as an explicit witness. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientGrowthData.toExplicitQuotientLogGrowthData
    (H : EntireXiPullbackCanonicalQuotientGrowthData) :
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData where
  zeroDistribution := H.zeroDistribution
  quotientLog := entireXiPullbackCanonicalQuotientLog H.zeroDistribution
  quotientLog_differentiable :=
    entireXiPullbackCanonicalQuotientLog_differentiable H.zeroDistribution
  exp_quotientLog_eq :=
    exp_entireXiPullbackCanonicalQuotientLog H.zeroDistribution
  quotientLog_subquadratic := H.quotientLog_subquadratic

/-- Growth of any explicit entire logarithm transfers to the fixed logarithm:
the two logarithms differ by a constant, and constant shifts preserve
subquadratic growth.  Thus the compact fixed-log interface loses no
generality and does not force a proof about an opaque representative. -/
noncomputable def
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.toQuotientGrowthData
    (H : EntireXiPullbackCanonicalExplicitQuotientLogGrowthData) :
    EntireXiPullbackCanonicalQuotientGrowthData := by
  have hsamelog : ∃ c : ℂ, ∀ z : ℂ,
      entireXiPullbackCanonicalQuotientLog H.zeroDistribution z =
        H.quotientLog z + c := by
    apply differentiable_logs_eq_add_const
      H.quotientLog_differentiable
      (entireXiPullbackCanonicalQuotientLog_differentiable H.zeroDistribution)
    intro z
    rw [H.exp_quotientLog_eq z,
      exp_entireXiPullbackCanonicalQuotientLog H.zeroDistribution z]
  let c : ℂ := Classical.choose hsamelog
  have hc : ∀ z : ℂ,
      entireXiPullbackCanonicalQuotientLog H.zeroDistribution z =
        H.quotientLog z + c := Classical.choose_spec hsamelog
  refine
    { zeroDistribution := H.zeroDistribution
      quotientLog_subquadratic := ?_ }
  have hfun : entireXiPullbackCanonicalQuotientLog H.zeroDistribution =
      fun z ↦ H.quotientLog z + c := funext hc
  rw [hfun]
  exact H.quotientLog_subquadratic.add_const c

/-- A Backlund--Turing count plus any explicitly constructed quotient
logarithm and its visible growth estimate gives the witness-oriented data. -/
def
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.of_backlundTuringHeightCount
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (h : ℂ → ℂ) (hdiff : Differentiable ℂ h)
    (hexp : ∀ z : ℂ,
      Complex.exp (h z) = entireXiPullbackCanonicalQuotient z)
    (hgrowth : HasSubquadraticNormGrowth h) :
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData where
  zeroDistribution := Hcount.toCanonicalZeroDistribution
  quotientLog := h
  quotientLog_differentiable := hdiff
  exp_quotientLog_eq := hexp
  quotientLog_subquadratic := hgrowth

/-- The canonical Backlund--Turing height-count package supplies the divisor
field.  The subquadratic bound on the fixed quotient logarithm remains visible
as the one additional analytic argument. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientGrowthData.of_backlundTuringHeightCount
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (hgrowth : HasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog
        Hcount.toCanonicalZeroDistribution)) :
    EntireXiPullbackCanonicalQuotientGrowthData where
  zeroDistribution := Hcount.toCanonicalZeroDistribution
  quotientLog_subquadratic := hgrowth

/-- A cumulative dyadic `O(R log R)` count supplies the divisor field.  The
subquadratic bound on the fixed quotient logarithm remains the one additional
analytic argument. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientGrowthData.of_dyadicCumulativeCount
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (hgrowth : HasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog
        Hcount.toCanonicalZeroDistribution)) :
    EntireXiPullbackCanonicalQuotientGrowthData where
  zeroDistribution := Hcount.toCanonicalZeroDistribution
  quotientLog_subquadratic := hgrowth

/-- Witness-oriented quotient growth from a cumulative dyadic count. -/
def
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.of_dyadicCumulativeCount
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (h : ℂ → ℂ) (hdiff : Differentiable ℂ h)
    (hexp : ∀ z : ℂ,
      Complex.exp (h z) = entireXiPullbackCanonicalQuotient z)
    (hgrowth : HasSubquadraticNormGrowth h) :
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData where
  zeroDistribution := Hcount.toCanonicalZeroDistribution
  quotientLog := h
  quotientLog_differentiable := hdiff
  exp_quotientLog_eq := hexp
  quotientLog_subquadratic := hgrowth

/-- Subquadratic growth makes the automatically constructed quotient
logarithm affine. -/
theorem EntireXiPullbackCanonicalQuotientGrowthData.quotientLog_eq_affine
    (H : EntireXiPullbackCanonicalQuotientGrowthData) :
    ∃ a b : ℂ, ∀ z : ℂ,
      entireXiPullbackCanonicalQuotientLog H.zeroDistribution z =
        a + b * z :=
  differentiable_eq_affine_of_subquadraticNormGrowth
    (entireXiPullbackCanonicalQuotientLog_differentiable H.zeroDistribution)
    H.quotientLog_subquadratic

/-- The same growth input gives the full affine-exponential canonical
factorization of the xi pullback. -/
theorem EntireXiPullbackCanonicalQuotientGrowthData.exists_factorization
    (H : EntireXiPullbackCanonicalQuotientGrowthData) :
    ∃ a b : ℂ, ∀ z : ℂ,
      EntireXiPullback z = Complex.exp (a + b * z) *
        entireXiPullbackCanonicalProduct z := by
  obtain ⟨a, b, hab⟩ := H.quotientLog_eq_affine
  exact ⟨a, b, fun z ↦ by
    rw [EntireXiPullback_eq_exp_canonicalQuotientLog_mul_canonicalProduct
          H.zeroDistribution,
      hab z]⟩

/-- Subquadratic growth makes an explicit entire quotient logarithm affine. -/
theorem
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.quotientLog_eq_affine
    (H : EntireXiPullbackCanonicalExplicitQuotientLogGrowthData) :
    ∃ a b : ℂ, ∀ z : ℂ, H.quotientLog z = a + b * z :=
  differentiable_eq_affine_of_subquadraticNormGrowth
    H.quotientLog_differentiable H.quotientLog_subquadratic

/-- An explicit quotient logarithm with subquadratic growth gives the same
affine-exponential canonical factorization, independently of the fixed chosen
logarithm. -/
theorem
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.exists_factorization
    (H : EntireXiPullbackCanonicalExplicitQuotientLogGrowthData) :
    ∃ a b : ℂ, ∀ z : ℂ,
      EntireXiPullback z = Complex.exp (a + b * z) *
        entireXiPullbackCanonicalProduct z := by
  obtain ⟨a, b, hab⟩ := H.quotientLog_eq_affine
  exact ⟨a, b, fun z ↦ by
    rw [EntireXiPullback_eq_exp_mul_canonicalProduct_of_quotientLog
          H.zeroDistribution H.exp_quotientLog_eq,
      hab z]⟩

/-- Subquadratic quotient-log growth constructs the exact canonical
logarithmic-derivative package required by the strict Lagarias criterion. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientGrowthData.toCanonicalHadamardLogDerivativeData
    (H : EntireXiPullbackCanonicalQuotientGrowthData) :
    EntireXiPullbackCanonicalHadamardLogDerivativeData := by
  let a : ℂ := Classical.choose H.exists_factorization
  let b : ℂ := Classical.choose (Classical.choose_spec H.exists_factorization)
  have hfactor : ∀ z : ℂ,
      EntireXiPullback z = Complex.exp (a + b * z) *
        entireXiPullbackCanonicalProduct z :=
    Classical.choose_spec (Classical.choose_spec H.exists_factorization)
  exact
    EntireXiPullbackCanonicalHadamardLogDerivativeData.of_expAffineCanonicalProduct
      H.zeroDistribution a b hfactor

/-- The explicit-log interface constructs the same exact canonical
logarithmic-derivative data. -/
noncomputable def
    EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.toCanonicalHadamardLogDerivativeData
    (H : EntireXiPullbackCanonicalExplicitQuotientLogGrowthData) :
    EntireXiPullbackCanonicalHadamardLogDerivativeData := by
  let a : ℂ := Classical.choose H.exists_factorization
  let b : ℂ := Classical.choose (Classical.choose_spec H.exists_factorization)
  have hfactor : ∀ z : ℂ,
      EntireXiPullback z = Complex.exp (a + b * z) *
        entireXiPullbackCanonicalProduct z :=
    Classical.choose_spec (Classical.choose_spec H.exists_factorization)
  exact
    EntireXiPullbackCanonicalHadamardLogDerivativeData.of_expAffineCanonicalProduct
      H.zeroDistribution a b hfactor

/-- Pullback strict anti-Herglotz form obtained from the exact quotient-growth
input. -/
theorem
    riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalQuotientGrowthData
    (H : EntireXiPullbackCanonicalQuotientGrowthData) :
    RiemannHypothesis ↔ EntireXiPullback.StrictAntiHerglotzSign :=
  riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalLogDerivativeData
    H.toCanonicalHadamardLogDerivativeData

/-- Classical right-half-plane form obtained from the exact quotient-growth
input. -/
theorem
    riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_canonicalQuotientGrowthData
    (H : EntireXiPullbackCanonicalQuotientGrowthData) :
    RiemannHypothesis ↔ EntireXi.rightHalfPlaneStrictLogDerivSign :=
  riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_canonicalLogDerivativeData
    H.toCanonicalHadamardLogDerivativeData

/-- Punctured strict Lagarias equivalence obtained from the exact
quotient-growth input. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientGrowthData
    (H : EntireXiPullbackCanonicalQuotientGrowthData) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalLogDerivativeData
    H.toCanonicalHadamardLogDerivativeData

/-- Punctured strict Lagarias equivalence from a concrete entire quotient
logarithm and its subquadratic growth estimate. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_explicitCanonicalQuotientLogGrowthData
    (H : EntireXiPullbackCanonicalExplicitQuotientLogGrowthData) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalLogDerivativeData
    H.toCanonicalHadamardLogDerivativeData

/-- Explicit Backlund--Turing capstone.  A logarithmic bound for the exact
canonical height count provides inverse-square divisor distribution; after
that reduction, the only remaining analytic hypothesis is subquadratic growth
of the automatically constructed quotient logarithm. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_backlundTuring_and_quotientLogGrowth
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (hgrowth : HasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog
        Hcount.toCanonicalZeroDistribution)) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientGrowthData
    (EntireXiPullbackCanonicalQuotientGrowthData.of_backlundTuringHeightCount
      Hcount hgrowth)

/-- Witness-oriented Backlund--Turing capstone.  This version accepts a
naturally constructed entire logarithm directly, so no growth transfer to a
`Classical.choose` representative is required. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_backlundTuring_explicitLogGrowth
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (h : ℂ → ℂ) (hdiff : Differentiable ℂ h)
    (hexp : ∀ z : ℂ,
      Complex.exp (h z) = entireXiPullbackCanonicalQuotient z)
    (hgrowth : HasSubquadraticNormGrowth h) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_explicitCanonicalQuotientLogGrowthData
    (EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.of_backlundTuringHeightCount
      Hcount h hdiff hexp hgrowth)

/-- Jensen/dyadic-count capstone.  A cumulative multiplicity count of order
`O(R log R)` supplies inverse-square distribution; subquadratic growth of the
completed quotient logarithm is the only further analytic hypothesis. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_dyadicCount_and_quotientLogGrowth
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (hgrowth : HasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog
        Hcount.toCanonicalZeroDistribution)) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientGrowthData
    (EntireXiPullbackCanonicalQuotientGrowthData.of_dyadicCumulativeCount
      Hcount hgrowth)

/-- Witness-oriented Jensen/dyadic-count capstone. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_dyadicCount_explicitLogGrowth
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (h : ℂ → ℂ) (hdiff : Differentiable ℂ h)
    (hexp : ∀ z : ℂ,
      Complex.exp (h z) = entireXiPullbackCanonicalQuotient z)
    (hgrowth : HasSubquadraticNormGrowth h) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_explicitCanonicalQuotientLogGrowthData
    (EntireXiPullbackCanonicalExplicitQuotientLogGrowthData.of_dyadicCumulativeCount
      Hcount h hdiff hexp hgrowth)

end OverflowResidueRH
