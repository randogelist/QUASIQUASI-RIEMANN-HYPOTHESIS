/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import RiemannHypothesis.ComplexAnalysis.GrowthRigidity
import RiemannHypothesis.HadamardProduct.IndexedRealZeroSign
import RiemannHypothesis.Xi.BacklundTuringBridge
import RiemannHypothesis.Xi.StrictLagariasCriterion

/-!
# A divisor-indexed logarithmic-derivative criterion for xi

This module isolates the exact logarithmic-derivative data needed for the
reverse direction of the strict Lagarias criterion.  In contrast with the
factorization package in `StrictLagariasCriterion`, the zero occurrences may
be indexed by an arbitrary type.  Thus the interface does not force a finite
divisor to be represented by an infinite natural-number sequence.

The package deliberately assumes a punctured logarithmic-derivative expansion,
not a Hadamard factorization.  Constructing that expansion from the analytic
divisor of xi remains a separate classical-analysis obligation.
-/

namespace OverflowResidueRH

universe u

/-- The critical-line pullback is even.  This is the functional equation
`xi(1 - s) = xi(s)` in the coordinate `s = 1 / 2 + I z`. -/
theorem EntireXiPullback_neg (z : ℂ) :
    EntireXiPullback (-z) = EntireXiPullback z :=
  entireXiPullback_neg z

/-- The derivative of the even xi pullback is odd. -/
theorem EntireXiPullback_deriv_neg (z : ℂ) :
    deriv EntireXiPullback (-z) = -deriv EntireXiPullback z := by
  have hinner : HasDerivAt (fun w : ℂ => -w) (-1) z :=
    (hasDerivAt_id z).neg
  have houter : HasDerivAt EntireXiPullback
      (deriv EntireXiPullback (-z)) (-z) :=
    (EntireXiPullback_differentiable (-z)).hasDerivAt
  have hcomp : HasDerivAt (fun w : ℂ => EntireXiPullback (-w))
      (deriv EntireXiPullback (-z) * (-1)) z := by
    simpa [Function.comp_def] using houter.comp z hinner
  have hfun : (fun w : ℂ => EntireXiPullback (-w)) = EntireXiPullback :=
    funext EntireXiPullback_neg
  have hderiv_fun :
      deriv (fun w : ℂ => EntireXiPullback (-w)) z =
        deriv EntireXiPullback z :=
    congrArg (fun f : ℂ → ℂ => deriv f z) hfun
  have hderiv :
      deriv EntireXiPullback z = deriv EntireXiPullback (-z) * (-1) := by
    rw [← hderiv_fun]
    exact hcomp.deriv
  have hneg := congrArg Neg.neg hderiv
  simpa using hneg.symm

/-- The totalized logarithmic derivative of the even xi pullback is odd. -/
theorem EntireXiPullback_logDerivativeResponse_neg (z : ℂ) :
    logDerivativeResponse EntireXiPullback (-z) =
      -logDerivativeResponse EntireXiPullback z := by
  unfold logDerivativeResponse
  rw [EntireXiPullback_deriv_neg, EntireXiPullback_neg]
  ring

/-- The derivative of the even xi pullback vanishes at its center. -/
theorem EntireXiPullback_deriv_zero : deriv EntireXiPullback 0 = 0 := by
  have h := EntireXiPullback_deriv_neg 0
  simp only [neg_zero] at h
  have htwo : (2 : ℂ) * deriv EntireXiPullback 0 = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The elementary exact value `xi(2) = pi / 6`. -/
theorem entireRiemannXi_two :
    entireRiemannXi 2 = ((Real.pi / 6 : ℝ) : ℂ) := by
  have hzeta := riemannZeta_eq_completedRiemannZeta₀
    (s := (2 : ℂ)) (by norm_num)
  rw [riemannZeta_two] at hzeta
  unfold entireRiemannXi
  norm_num [Complex.Gamma_one, Complex.cpow_neg_one] at hzeta ⊢
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi] at hzeta ⊢
  ring_nf at hzeta ⊢
  exact hzeta.symm

/-- A concrete pullback value corresponding to `xi(0) = 1 / 2`. -/
theorem EntireXiPullback_apply_I_div_two :
    EntireXiPullback (Complex.I / 2) = (1 / 2 : ℂ) := by
  unfold EntireXiPullback
  rw [show (1 / 2 : ℂ) + Complex.I * (Complex.I / 2) = 0 by
    calc
      (1 / 2 : ℂ) + Complex.I * (Complex.I / 2) =
          1 / 2 + (Complex.I * Complex.I) / 2 := by ring
      _ = 0 := by rw [Complex.I_mul_I]; norm_num]
  simp [entireRiemannXi]

/-- A second concrete pullback value, corresponding to `xi(2) = pi / 6`. -/
theorem EntireXiPullback_apply_neg_three_halves_I :
    EntireXiPullback (-(3 / 2 : ℂ) * Complex.I) =
      ((Real.pi / 6 : ℝ) : ℂ) := by
  unfold EntireXiPullback
  rw [show (1 / 2 : ℂ) + Complex.I * (-(3 / 2 : ℂ) * Complex.I) = 2 by
    calc
      (1 / 2 : ℂ) + Complex.I * (-(3 / 2 : ℂ) * Complex.I) =
          1 / 2 - (3 / 2) * (Complex.I * Complex.I) := by ring
      _ = 2 := by rw [Complex.I_mul_I]; norm_num]
  exact entireRiemannXi_two

/-- The entire xi pullback is genuinely nonconstant. -/
theorem EntireXiPullback_not_constant :
    ¬ ∀ z w : ℂ, EntireXiPullback z = EntireXiPullback w := by
  intro hconst
  have heq := hconst (Complex.I / 2) (-(3 / 2 : ℂ) * Complex.I)
  rw [EntireXiPullback_apply_I_div_two,
    EntireXiPullback_apply_neg_three_halves_I] at heq
  have hre := congrArg Complex.re heq
  norm_num at hre
  linarith [Real.pi_gt_three]

/-- Minimal divisor-indexed logarithmic-derivative data for the xi pullback.

The indexed locations are occurrences, rather than necessarily distinct zero
values, so repetition can encode multiplicity.  Strictness needs at least one
residue contribution: either the origin term is present or the occurrence
index is nonempty. -/
structure EntireXiPullbackHadamardLogDerivativeData
    (ι : Type u) : Type (u + 1) where
  originMultiplicity : ℕ
  zeroLoc : ι → ℂ
  zeroData : HadamardZeroInvSqSummability zeroLoc
  zeroLoc_is_zero : ∀ i : ι, EntireXiPullback (zeroLoc i) = 0
  b : ℂ
  b_im : b.im = 0
  logDerivative_expansion :
    ∀ z : ℂ, z ≠ 0 → (∀ i : ι, z ≠ zeroLoc i) →
      logDerivativeResponse EntireXiPullback z =
        (originMultiplicity : ℂ) / z + b +
          hadamardRegularizedLogDerivSeries zeroLoc z
  support_nonempty : originMultiplicity ≠ 0 ∨ Nonempty ι

/-- The origin contribution has nonpositive imaginary part in the open upper
half-plane. -/
private theorem originMultiplicityResponse_im_nonpos
    (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    (((m : ℂ) / z).im) ≤ 0 := by
  rw [Complex.div_im]
  have hm_im : ((m : ℂ).im) = 0 := by simp
  have hm_re : ((m : ℂ).re) = (m : ℝ) := by simp
  rw [hm_im, hm_re]
  simp only [zero_mul, zero_div, zero_sub]
  exact neg_nonpos.mpr <| div_nonneg
    (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hz))
    (Complex.normSq_nonneg z)

/-- A nonzero origin multiplicity contributes strictly negatively in the open
upper half-plane. -/
private theorem originMultiplicityResponse_im_neg
    (m : ℕ) (hm : m ≠ 0) (z : ℂ) (hz : 0 < z.im) :
    (((m : ℂ) / z).im) < 0 := by
  rw [Complex.div_im]
  have hm_im : ((m : ℂ).im) = 0 := by simp
  have hm_re : ((m : ℂ).re) = (m : ℝ) := by simp
  rw [hm_im, hm_re]
  simp only [zero_mul, zero_div, zero_sub]
  apply neg_neg_of_pos
  apply div_pos
  · exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hz
  · apply Complex.normSq_pos.mpr
    intro hzero
    subst z
    simp at hz

/-- Under RH, the supplied logarithmic-derivative expansion is strictly
anti-Herglotz.  Strictness comes from the origin term or from one indexed zero
occurrence, according to `support_nonempty`. -/
theorem
    EntireXiPullbackHadamardLogDerivativeData.strictAntiHerglotz_of_riemannHypothesis
    {ι : Type u} (H : EntireXiPullbackHadamardLogDerivativeData ι)
    (hRH : RiemannHypothesis) :
    EntireXiPullback.StrictAntiHerglotzSign := by
  have hpull_zeros_real :
      ∀ z : ℂ, EntireXiPullback z = 0 → z.im = 0 :=
    riemannHypothesis_iff_entireXiPullback_zeros_real.mp hRH
  have hreal : ∀ i : ι, (H.zeroLoc i).im = 0 :=
    fun i => hpull_zeros_real (H.zeroLoc i) (H.zeroLoc_is_zero i)
  intro z hz
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hzloc : ∀ i : ι, z ≠ H.zeroLoc i := by
    intro i hzi
    have him := congrArg Complex.im hzi
    rw [hreal i] at him
    linarith
  rw [H.logDerivative_expansion z hz0 hzloc]
  simp only [Complex.add_im, H.b_im, add_zero]
  rcases H.support_nonempty with hm | hι
  · exact add_neg_of_neg_of_nonpos
      (originMultiplicityResponse_im_neg H.originMultiplicity hm z hz)
      (hadamardRegularizedLogDerivSeries_im_nonpos_of_real_indexed
        H.zeroLoc H.zeroData hreal hz)
  · letI : Nonempty ι := hι
    exact add_neg_of_nonpos_of_neg
      (originMultiplicityResponse_im_nonpos H.originMultiplicity z hz)
      (hadamardRegularizedLogDerivSeries_im_neg_of_real_indexed
        H.zeroLoc H.zeroData hreal hz)

/-- Minimal divisor-indexed logarithmic-derivative data makes RH exactly
equivalent to strict anti-Herglotz behavior of the xi pullback.  The reverse
implication is the unconditional analytic zero-exclusion theorem. -/
theorem riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_logDerivativeData
    {ι : Type u} (H : EntireXiPullbackHadamardLogDerivativeData ι) :
    RiemannHypothesis ↔ EntireXiPullback.StrictAntiHerglotzSign := by
  constructor
  · exact H.strictAntiHerglotz_of_riemannHypothesis
  · exact riemannHypothesis_of_entireXi_rightHalfPlaneStrictLogDerivSign ∘
      entireXi_rightHalfPlaneStrictLogDerivSign_iff_pullback.mpr

/-- Right-half-plane form of the divisor-indexed strict Lagarias criterion. -/
theorem
    riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_logDerivativeData
    {ι : Type u} (H : EntireXiPullbackHadamardLogDerivativeData ι) :
    RiemannHypothesis ↔ EntireXi.rightHalfPlaneStrictLogDerivSign :=
  (riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_logDerivativeData H).trans
    entireXi_rightHalfPlaneStrictLogDerivSign_iff_pullback.symm

/-- Punctured-domain form of the divisor-indexed strict Lagarias criterion. -/
theorem riemannHypothesis_iff_entireXi_lagariasPositivity_of_logDerivativeData
    {ι : Type u} (H : EntireXiPullbackHadamardLogDerivativeData ι) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  (riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_logDerivativeData H).trans
    entireXi_lagariasPositivity_iff_rightHalfPlaneStrictLogDerivSign.symm

/-- The older natural-number-indexed exact factorization package supplies the
minimal logarithmic-derivative interface. -/
noncomputable def
    EntireXiPullbackExpAffineHadamardData.toHadamardLogDerivativeData
    (H : EntireXiPullbackExpAffineHadamardData) :
    EntireXiPullbackHadamardLogDerivativeData ℕ where
  originMultiplicity := H.originMultiplicity
  zeroLoc := H.zeroLoc
  zeroData := H.zeroData.toHadamardZeroInvSqSummability
  zeroLoc_is_zero := by
    intro i
    exact (H.zero_iff_origin_or_exists_zeroLoc (H.zeroLoc i)).mpr
      (Or.inr ⟨i, rfl⟩)
  b := H.b
  b_im := H.slope_real
  logDerivative_expansion := by
    intro z hz0 hzloc
    rw [H.factorization]
    rw [logDerivativeResponse_expAffineGenusOneProductWithOriginMultiplicity
      H.constant_ne_zero H.zeroData.toHadamardZeroInvSqSummability hz0 hzloc]
    rw [logDerivativeResponse_infiniteHadamardProduct_eq_tsum_nat
      H.zeroData.toHadamardZeroInvSqSummability hzloc]
  support_nonempty := Or.inr (inferInstance : Nonempty ℕ)

/-- Logarithmic-derivative input specialized to the unconditional canonical
analytic divisor of the xi pullback.  Only the global inverse-square estimate,
the constant term, and the punctured expansion remain as fields.  Exact
negation symmetry forces the constant term to vanish; strict-support
nonemptiness then follows from the expansion and the proved nonconstancy of
the pullback. -/
structure EntireXiPullbackCanonicalHadamardLogDerivativeData : Type where
  zeroDistribution : EntireXiPullbackCanonicalZeroDistribution
  b : ℂ
  logDerivative_expansion :
    ∀ z : ℂ, z ≠ 0 →
      (∀ i : EntireXiPullbackZeroOccurrence,
        z ≠ entireXiPullbackZeroOccurrenceLoc i) →
      logDerivativeResponse EntireXiPullback z =
        (entireXiPullbackOriginMultiplicity : ℂ) / z + b +
          hadamardRegularizedLogDerivSeries
            entireXiPullbackZeroOccurrenceLoc z

/-- Build the canonical logarithmic-derivative package from the exact
multiplicity-aware output expected of a Backlund--Turing zero-count theorem
and the still-separate punctured expansion.  Thus Backlund--Turing discharges
the inverse-square field, but does not manufacture the expansion. -/
noncomputable def
    EntireXiPullbackCanonicalHadamardLogDerivativeData.of_backlundTuringShellBound
    (Hcount : EntireXiPullbackBacklundTuringShellBound)
    (b : ℂ)
    (hexpansion :
      ∀ z : ℂ, z ≠ 0 →
        (∀ i : EntireXiPullbackZeroOccurrence,
          z ≠ entireXiPullbackZeroOccurrenceLoc i) →
        logDerivativeResponse EntireXiPullback z =
          (entireXiPullbackOriginMultiplicity : ℂ) / z + b +
            hadamardRegularizedLogDerivSeries
              entireXiPullbackZeroOccurrenceLoc z) :
    EntireXiPullbackCanonicalHadamardLogDerivativeData where
  zeroDistribution := Hcount.toCanonicalZeroDistribution
  b := b
  logDerivative_expansion := hexpansion

/-- An alternative, growth-explicit input for the canonical xi divisor.

Instead of assuming that the punctured logarithmic-derivative remainder is a
constant, this structure asks for an entire extension of that remainder and
the quantitative bound `remainder = o(‖z‖)`.  Cauchy's estimate then proves
constancy.  This separates the local divisor computation from the global
growth theorem and prevents a Hadamard expansion from being smuggled into an
interface field. -/
structure EntireXiPullbackCanonicalRemainderData : Type where
  zeroDistribution : EntireXiPullbackCanonicalZeroDistribution
  remainder : ℂ → ℂ
  remainder_differentiable : Differentiable ℂ remainder
  remainder_sublinear : HasSublinearNormGrowth remainder
  remainder_eq :
    ∀ z : ℂ, z ≠ 0 →
      (∀ i : EntireXiPullbackZeroOccurrence,
        z ≠ entireXiPullbackZeroOccurrenceLoc i) →
      remainder z =
        logDerivativeResponse EntireXiPullback z -
          ((entireXiPullbackOriginMultiplicity : ℂ) / z +
            hadamardRegularizedLogDerivSeries
              entireXiPullbackZeroOccurrenceLoc z)

/-- Cauchy rigidity turns an entire sublinear canonical remainder into the
constant term required by the punctured logarithmic-derivative expansion. -/
noncomputable def
    EntireXiPullbackCanonicalRemainderData.toCanonicalHadamardLogDerivativeData
    (H : EntireXiPullbackCanonicalRemainderData) :
    EntireXiPullbackCanonicalHadamardLogDerivativeData := by
  let hconst := differentiable_eq_const_of_sublinearNormGrowth
    H.remainder_differentiable H.remainder_sublinear
  let b : ℂ := Classical.choose hconst
  have hb : ∀ z : ℂ, H.remainder z = b := Classical.choose_spec hconst
  refine
    { zeroDistribution := H.zeroDistribution
      b := b
      logDerivative_expansion := ?_ }
  intro z hz0 hzloc
  have hrem := H.remainder_eq z hz0 hzloc
  rw [hb z] at hrem
  have hsum :
      b + ((entireXiPullbackOriginMultiplicity : ℂ) / z +
        hadamardRegularizedLogDerivSeries
          entireXiPullbackZeroOccurrenceLoc z) =
        logDerivativeResponse EntireXiPullback z :=
    (eq_sub_iff_add_eq).mp hrem
  calc
    logDerivativeResponse EntireXiPullback z =
        b + ((entireXiPullbackOriginMultiplicity : ℂ) / z +
          hadamardRegularizedLogDerivSeries
            entireXiPullbackZeroOccurrenceLoc z) := hsum.symm
    _ = (entireXiPullbackOriginMultiplicity : ℂ) / z + b +
          hadamardRegularizedLogDerivSeries
            entireXiPullbackZeroOccurrenceLoc z := by ring

/-- The constant term in the canonical logarithmic-derivative expansion is
zero.  Both the pullback response and the exact multiplicity-bearing
regularized divisor series are odd under negation. -/
theorem EntireXiPullbackCanonicalHadamardLogDerivativeData.b_eq_zero
    (H : EntireXiPullbackCanonicalHadamardLogDerivativeData) :
    H.b = 0 := by
  let z : ℂ := Complex.I / 2
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact div_ne_zero Complex.I_ne_zero (by norm_num)
  have hFz : EntireXiPullback z ≠ 0 := by
    rw [show EntireXiPullback z = (1 / 2 : ℂ) by
      simpa only [z] using EntireXiPullback_apply_I_div_two]
    norm_num
  have hnegFz : EntireXiPullback (-z) ≠ 0 := by
    rw [EntireXiPullback_neg]
    exact hFz
  have hzloc : ∀ i : EntireXiPullbackZeroOccurrence,
      z ≠ entireXiPullbackZeroOccurrenceLoc i := by
    intro i hzi
    apply hFz
    rw [hzi]
    exact entireXiPullbackZeroOccurrenceLoc_is_zero i
  have hnegzloc : ∀ i : EntireXiPullbackZeroOccurrence,
      -z ≠ entireXiPullbackZeroOccurrenceLoc i := by
    intro i hzi
    apply hnegFz
    rw [hzi]
    exact entireXiPullbackZeroOccurrenceLoc_is_zero i
  have hodd := EntireXiPullback_logDerivativeResponse_neg z
  rw [H.logDerivative_expansion (-z) (neg_ne_zero.mpr hz0) hnegzloc,
    H.logDerivative_expansion z hz0 hzloc,
    entireXiPullbackCanonicalRegularizedSeries_neg, div_neg] at hodd
  have htwo : (2 : ℂ) * H.b = 0 := by
    linear_combination hodd
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The canonical expansion must contain at least one residue contribution.
If both the origin multiplicity and the nonzero occurrence type were empty,
the expansion and evenness would force the logarithmic derivative to vanish
everywhere.  The entire pullback would then be constant, contradicting its two
explicit values above. -/
theorem EntireXiPullbackCanonicalHadamardLogDerivativeData.support_nonempty
    (H : EntireXiPullbackCanonicalHadamardLogDerivativeData) :
    entireXiPullbackOriginMultiplicity ≠ 0 ∨
      Nonempty EntireXiPullbackZeroOccurrence := by
  by_contra hsupport
  push Not at hsupport
  rcases hsupport with ⟨hm, hocc⟩
  letI : IsEmpty EntireXiPullbackZeroOccurrence := hocc
  have hseries : ∀ z : ℂ,
      hadamardRegularizedLogDerivSeries
          entireXiPullbackZeroOccurrenceLoc z = 0 := by
    intro z
    simp [hadamardRegularizedLogDerivSeries]
  have haway : ∀ z : ℂ, z ≠ 0 →
      logDerivativeResponse EntireXiPullback z = H.b := by
    intro z hz0
    rw [H.logDerivative_expansion z hz0 (fun i => isEmptyElim i),
      hm, Nat.cast_zero, zero_div, zero_add, hseries, add_zero]
  have hb : H.b = 0 := H.b_eq_zero
  have hzero_free : ∀ z : ℂ, EntireXiPullback z ≠ 0 := by
    intro z
    by_cases hz0 : z = 0
    · subst z
      intro hFzero
      exact (entireXiPullbackOriginMultiplicity_ne_zero_iff.mpr hFzero) hm
    · intro hFzero
      obtain ⟨i, _hi⟩ :=
        entireXiPullbackZeroOccurrenceLoc_exhaustive hFzero hz0
      exact isEmptyElim i
  have hderiv : ∀ z : ℂ, deriv EntireXiPullback z = 0 := by
    intro z
    by_cases hz0 : z = 0
    · subst z
      exact EntireXiPullback_deriv_zero
    · have hlog : logDerivativeResponse EntireXiPullback z = 0 := by
        rw [haway z hz0, hb]
      unfold logDerivativeResponse at hlog
      exact (div_eq_zero_iff.mp hlog).resolve_right (hzero_free z)
  exact EntireXiPullback_not_constant
    (is_const_of_deriv_eq_zero EntireXiPullback_differentiable hderiv)

/-- Forget the canonical presentation and expose the generic arbitrary-index
logarithmic-derivative interface. -/
noncomputable def
    EntireXiPullbackCanonicalHadamardLogDerivativeData.toHadamardLogDerivativeData
    (H : EntireXiPullbackCanonicalHadamardLogDerivativeData) :
    EntireXiPullbackHadamardLogDerivativeData
      EntireXiPullbackZeroOccurrence where
  originMultiplicity := entireXiPullbackOriginMultiplicity
  zeroLoc := entireXiPullbackZeroOccurrenceLoc
  zeroData := H.zeroDistribution.toHadamardZeroInvSqSummability
  zeroLoc_is_zero := entireXiPullbackZeroOccurrenceLoc_is_zero
  b := H.b
  b_im := by
    rw [H.b_eq_zero]
    simp
  logDerivative_expansion := H.logDerivative_expansion
  support_nonempty := H.support_nonempty

/-- Canonical-divisor specialization of the pullback strict criterion. -/
theorem
    riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalLogDerivativeData
    (H : EntireXiPullbackCanonicalHadamardLogDerivativeData) :
    RiemannHypothesis ↔ EntireXiPullback.StrictAntiHerglotzSign :=
  riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_logDerivativeData
    H.toHadamardLogDerivativeData

/-- Canonical-divisor specialization in the classical right-half-plane form. -/
theorem
    riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_canonicalLogDerivativeData
    (H : EntireXiPullbackCanonicalHadamardLogDerivativeData) :
    RiemannHypothesis ↔ EntireXi.rightHalfPlaneStrictLogDerivSign :=
  riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_logDerivativeData
    H.toHadamardLogDerivativeData

/-- Canonical-divisor specialization in punctured Lagarias form. -/
theorem riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalLogDerivativeData
    (H : EntireXiPullbackCanonicalHadamardLogDerivativeData) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_logDerivativeData
    H.toHadamardLogDerivativeData

/-- Canonical-remainder specialization of the pullback strict criterion. -/
theorem
    riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalRemainderData
    (H : EntireXiPullbackCanonicalRemainderData) :
    RiemannHypothesis ↔ EntireXiPullback.StrictAntiHerglotzSign :=
  riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalLogDerivativeData
    H.toCanonicalHadamardLogDerivativeData

/-- Canonical-remainder specialization in the classical right-half-plane
form. -/
theorem
    riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_canonicalRemainderData
    (H : EntireXiPullbackCanonicalRemainderData) :
    RiemannHypothesis ↔ EntireXi.rightHalfPlaneStrictLogDerivSign :=
  riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_canonicalLogDerivativeData
    H.toCanonicalHadamardLogDerivativeData

/-- A fully formal conditional form of the classical strict Lagarias
equivalence.  The sole analytic package is now an entire sublinear remainder,
not an already-constant logarithmic-derivative expansion. -/
theorem riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalRemainderData
    (H : EntireXiPullbackCanonicalRemainderData) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalLogDerivativeData
    H.toCanonicalHadamardLogDerivativeData

end OverflowResidueRH
