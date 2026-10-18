/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.ExponentialPrefactor
import RiemannHypothesis.HadamardProduct.RealZeroSign
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Strict real-zero criteria for genus-one products

This module adds the affine exponential factor occurring in the classical
Hadamard factorization. A real logarithmic derivative of the prefactor does
not affect the upper-half-plane imaginary-part inequality, so the strict
criterion is controlled exactly by the zero product.
-/

namespace OverflowResidueRH

open scoped ComplexConjugate

/-- An affine-exponential prefactor times a normalized genus-one product. -/
noncomputable def expAffineGenusOneProduct
    (C a b : ℂ) (zeroLoc : ℕ → ℂ) : ℂ → ℂ :=
  fun z =>
    C * Complex.exp (a + b * z) * infiniteHadamardProduct zeroLoc z

/-- Away from the indexed zeros, the logarithmic derivative of an
affine-exponential genus-one product is the real-affine contribution `b`
plus the regularized logarithmic derivative of the zero product. -/
theorem logDerivativeResponse_expAffineGenusOneProduct
    {C a b : ℂ} (hC : C ≠ 0)
    {zeroLoc : ℕ → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {z : ℂ} (hz : ∀ i : ℕ, z ≠ zeroLoc i) :
    logDerivativeResponse (expAffineGenusOneProduct C a b zeroLoc) z =
      b + logDerivativeResponse (infiniteHadamardProduct zeroLoc) z := by
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion H) :=
    natHadamardProductLocallyUniformLimitData H
  have hpref_diff :
      DifferentiableAt ℂ (fun w : ℂ => C * Complex.exp (a + b * w)) z := by
    fun_prop
  have hprod_diff :
      DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) z :=
    Hluc.infinite_differentiableAt (Set.mem_univ z)
  have hpref_ne : C * Complex.exp (a + b * z) ≠ 0 :=
    mul_ne_zero hC (Complex.exp_ne_zero _)
  have hprod_ne : infiniteHadamardProduct zeroLoc z ≠ 0 :=
    H.infiniteProduct_ne_zero hz
  unfold expAffineGenusOneProduct
  rw [logDerivativeResponse_mul_eq_add
      hpref_diff hprod_diff hpref_ne hprod_ne,
    logDerivativeResponse_exp_affine_prefactor hC]

/-- A Schwarz-reflecting function has real totalized logarithmic derivative at
the origin. No nonvanishing assumption is needed for this general statement:
if the value at the origin is zero, totalized division makes the response zero.
-/
theorem logDerivativeResponse_zero_im_eq_zero_of_schwarz
    (F : ℂ → ℂ) (h_schwarz : ∀ z : ℂ, F (star z) = star (F z)) :
    (logDerivativeResponse F 0).im = 0 := by
  have hfun : conj ∘ F ∘ conj = F := by
    funext z
    change star (F (star z)) = F z
    rw [h_schwarz]
    simp
  have hderiv_eq := congrArg (fun f : ℂ → ℂ => deriv f 0) hfun
  have hderiv_star : star (deriv F 0) = deriv F 0 := by
    rw [deriv_conj_conj] at hderiv_eq
    simpa using hderiv_eq
  have hvalue_star : star (F 0) = F 0 := by
    simpa using (h_schwarz 0).symm
  have hderiv_im : (deriv F 0).im = 0 :=
    Complex.conj_eq_iff_im.mp hderiv_star
  have hvalue_im : (F 0).im = 0 :=
    Complex.conj_eq_iff_im.mp hvalue_star
  simp [logDerivativeResponse, Complex.div_im, hderiv_im, hvalue_im]

/-- Genus-one regularization normalizes the logarithmic derivative of the
canonical product to zero at the origin. -/
theorem logDerivativeResponse_infiniteHadamardProduct_zero
    {zeroLoc : ℕ → ℂ} (H : HadamardZeroInvSqSummability zeroLoc) :
    logDerivativeResponse (infiniteHadamardProduct zeroLoc) 0 = 0 := by
  have hzero_ne : ∀ i : ℕ, (0 : ℂ) ≠ zeroLoc i :=
    fun i => (H.zero_ne i).symm
  rw [logDerivativeResponse_infiniteHadamardProduct_eq_tsum_nat H hzero_ne]
  unfold hadamardRegularizedLogDerivSeries
  simp

/-- Schwarz reflection of the full affine genus-one product forces the affine
slope to be real. The normalized genus-one product contributes zero to the
logarithmic derivative at the origin, so the full response there is exactly
`b`; Schwarz reflection makes that response real. -/
theorem expAffineGenusOneProduct_slope_real_of_schwarz
    {C a b : ℂ} (hC : C ≠ 0)
    (zeroLoc : ℕ → ℂ) (H : NatHadamardZeroInvSqData zeroLoc)
    (h_schwarz : ∀ z : ℂ,
      expAffineGenusOneProduct C a b zeroLoc (star z) =
        star (expAffineGenusOneProduct C a b zeroLoc z)) :
    b.im = 0 := by
  have hzero_ne : ∀ i : ℕ, (0 : ℂ) ≠ zeroLoc i :=
    fun i => (H.zero_ne i).symm
  have hlog := logDerivativeResponse_expAffineGenusOneProduct
    (a := a) (b := b) hC H.toHadamardZeroInvSqSummability hzero_ne
  rw [logDerivativeResponse_infiniteHadamardProduct_zero
      H.toHadamardZeroInvSqSummability,
    add_zero] at hlog
  have him := congrArg Complex.im hlog
  rw [logDerivativeResponse_zero_im_eq_zero_of_schwarz
      (expAffineGenusOneProduct C a b zeroLoc) h_schwarz] at him
  exact him.symm

/-- If all indexed zeros are real and the affine exponential slope is real,
the full affine-exponential genus-one product is strictly anti-Herglotz. -/
theorem expAffineGenusOneProduct_strictAntiHerglotz_of_zero_sequence_real
    {C a b : ℂ} (hC : C ≠ 0) (hb : b.im = 0)
    (zeroLoc : ℕ → ℂ)
    (H : NatHadamardZeroInvSqData zeroLoc)
    (hreal : ∀ i : ℕ, (zeroLoc i).im = 0) :
    StrictAntiHerglotzUHP
      (logDerivativeResponse (expAffineGenusOneProduct C a b zeroLoc)) := by
  intro z hz
  have hz_ne : ∀ i : ℕ, z ≠ zeroLoc i := by
    intro i hzi
    have him := congrArg Complex.im hzi
    rw [hreal i] at him
    linarith
  rw [logDerivativeResponse_expAffineGenusOneProduct hC
      H.toHadamardZeroInvSqSummability hz_ne,
    Complex.add_im, hb, zero_add]
  exact infiniteHadamardProduct_strictAntiHerglotz_of_nat_invSqData
    zeroLoc H hreal z hz

/-- **Exact affine genus-one criterion.** Under inverse-square zero data,
a nonvanishing affine exponential prefactor with real slope, and Schwarz
reflection of the resulting entire function, strict anti-Herglotz behavior
is equivalent to all zeros of the full function being real. -/
theorem expAffineGenusOneProduct_strictAntiHerglotz_iff_zeros_real
    {C a b : ℂ} (hC : C ≠ 0) (hb : b.im = 0)
    (zeroLoc : ℕ → ℂ)
    (H : NatHadamardZeroInvSqData zeroLoc)
    (h_schwarz : ∀ z : ℂ,
      expAffineGenusOneProduct C a b zeroLoc (star z) =
        star (expAffineGenusOneProduct C a b zeroLoc z)) :
    StrictAntiHerglotzUHP
        (logDerivativeResponse
          (expAffineGenusOneProduct C a b zeroLoc)) ↔
      ∀ rho : ℂ,
        expAffineGenusOneProduct C a b zeroLoc rho = 0 → rho.im = 0 := by
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion H.toHadamardZeroInvSqSummability) :=
    natHadamardProductLocallyUniformLimitData
      H.toHadamardZeroInvSqSummability
  have hdifferentiable :
      Differentiable ℂ (expAffineGenusOneProduct C a b zeroLoc) := by
    intro z
    exact (by fun_prop :
      DifferentiableAt ℂ (fun w : ℂ => C * Complex.exp (a + b * w)) z).mul
        (Hluc.infinite_differentiableAt (Set.mem_univ z))
  have hanalytic :
      AnalyticOnNhd ℂ (expAffineGenusOneProduct C a b zeroLoc) Set.univ :=
    fun z _hz => hdifferentiable.analyticAt z
  have hnontrivial :
      ∃ z : ℂ, expAffineGenusOneProduct C a b zeroLoc z ≠ 0 := by
    refine ⟨0, ?_⟩
    simp [expAffineGenusOneProduct, infiniteHadamardProduct_zero,
      hC, Complex.exp_ne_zero]
  constructor
  · intro hstrict
    exact entire_function_roots_real_of_analytic_nontrivial
      (expAffineGenusOneProduct C a b zeroLoc)
      hanalytic hnontrivial
      (fun z hz _hz_nonzero => hstrict.antiHerglotz z hz)
      h_schwarz
  · intro hzeros
    apply expAffineGenusOneProduct_strictAntiHerglotz_of_zero_sequence_real
      hC hb zeroLoc H
    intro i
    apply hzeros (zeroLoc i)
    unfold expAffineGenusOneProduct
    rw [infiniteHadamardProduct_eq_zero_at_zeroLoc H.zero_ne i, mul_zero]

/-- **Slope-free exact affine genus-one criterion.** Schwarz reflection of the
full function determines the affine slope automatically, so no independent
`b.im = 0` premise is needed. -/
theorem expAffineGenusOneProduct_strictAntiHerglotz_iff_zeros_real_of_schwarz
    {C a b : ℂ} (hC : C ≠ 0)
    (zeroLoc : ℕ → ℂ)
    (H : NatHadamardZeroInvSqData zeroLoc)
    (h_schwarz : ∀ z : ℂ,
      expAffineGenusOneProduct C a b zeroLoc (star z) =
        star (expAffineGenusOneProduct C a b zeroLoc z)) :
    StrictAntiHerglotzUHP
        (logDerivativeResponse
          (expAffineGenusOneProduct C a b zeroLoc)) ↔
      ∀ rho : ℂ,
        expAffineGenusOneProduct C a b zeroLoc rho = 0 → rho.im = 0 :=
  expAffineGenusOneProduct_strictAntiHerglotz_iff_zeros_real
    hC
    (expAffineGenusOneProduct_slope_real_of_schwarz
      hC zeroLoc H h_schwarz)
    zeroLoc H h_schwarz

end OverflowResidueRH
