/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.InfiniteProducts

/-!
# HadamardProduct.ExponentialPrefactor

The z-plane zero-contribution functions attached to an exponential-affine Hadamard
prefactor `C·exp(a + b·s)`. These pull the regularized ξ-side zero sum
`b + Σ_ρ (1/(s−ρ) + 1/ρ)` to the critical-line variable via `s = ½ + I·z`, in series,
expanded, and finite-truncation forms. Identity content only.

## Main declarations

* `logDerivativeResponse_exp_affine_prefactor` — `Λ[C·exp(a + b·s)] = b`.
* `expAffineHadamardPullbackZeroContribution` — the z-plane zero contribution as the
  pullback of `b +` the regularized log-derivative series.
* `expAffineHadamardPullbackZeroContributionExpanded` — the same contribution written
  with the zero sum expanded termwise.
* `expAffineHadamardPullbackFiniteContribution` — the finite-zero truncation.
-/

namespace OverflowResidueRH

/-- 🌟🌟🌟 **PROVED — the exponential-affine Hadamard prefactor has
constant log-derivative `b`.**

This is the concrete Hadamard prefactor calculation used in the
classical genus-one product: the nonzero scalar `C` contributes no
log-derivative, and `exp (a + b·s)` contributes exactly `b`. -/
theorem logDerivativeResponse_exp_affine_prefactor
    {C a b s : ℂ} (hC : C ≠ 0) :
    logDerivativeResponse
        (fun w : ℂ => C * Complex.exp (a + b * w)) s = b := by
  unfold logDerivativeResponse
  have h_aff : DifferentiableAt ℂ (fun w : ℂ => a + b * w) s :=
    (differentiableAt_const _).add
      ((differentiableAt_const _).mul differentiableAt_fun_id)
  have h_deriv_aff :
      deriv (fun w : ℂ => a + b * w) s = b := by
    rw [deriv_fun_add (differentiableAt_const _)
          ((differentiableAt_const _).mul differentiableAt_fun_id),
        deriv_const,
        deriv_fun_mul (differentiableAt_const _) differentiableAt_fun_id,
        deriv_const, deriv_id'']
    ring
  have h_deriv_exp :
      deriv (fun w : ℂ => Complex.exp (a + b * w)) s
        = Complex.exp (a + b * s) * b := by
    rw [deriv_cexp h_aff, h_deriv_aff]
  have h_deriv :
      deriv (fun w : ℂ => C * Complex.exp (a + b * w)) s
        = C * (Complex.exp (a + b * s) * b) := by
    rw [deriv_fun_mul (differentiableAt_const _) h_aff.cexp,
        deriv_const, h_deriv_exp]
    ring
  rw [h_deriv]
  have h_exp : Complex.exp (a + b * s) ≠ 0 := Complex.exp_ne_zero _
  field_simp [hC, h_exp]

/-- **Explicit z-plane Hadamard zero contribution for an exp-affine
entire-ξ Hadamard product.**

For `s(z) = 1/2 + I z`, this is the chain-rule pullback of the
classical source `b + Σρ (1/(s-ρ)+1/ρ)`. -/
noncomputable def expAffineHadamardPullbackZeroContribution
    {ι : Type} (zeroLoc : ι → ℂ) (b : ℂ) : ℂ → ℂ :=
  fun z =>
    Complex.I *
      (b + hadamardRegularizedLogDerivSeries zeroLoc
        ((1 / 2 : ℂ) + Complex.I * z))

/-- **Expanded z-plane exp-affine Hadamard contribution.**

This is definitionally the expression produced after distributing the
chain-rule factor `I` across the prefactor term and the regularized
Hadamard zero series. -/
noncomputable def expAffineHadamardPullbackZeroContributionExpanded
    {ι : Type} (zeroLoc : ι → ℂ) (b : ℂ) : ℂ → ℂ :=
  fun z =>
    Complex.I * b
      + ∑' i : ι,
          Complex.I *
            (1 / (((1 / 2 : ℂ) + Complex.I * z) - zeroLoc i)
              + 1 / zeroLoc i)

/-- **Finite expanded z-plane exp-affine Hadamard contribution.**

This is the finite-zero truncation of
`expAffineHadamardPullbackZeroContributionExpanded`, with the same
constant chain-rule prefactor term `I*b`. -/
noncomputable def expAffineHadamardPullbackFiniteContribution
    {ι : Type} (zeroLoc : ι → ℂ) (b : ℂ) (F : Finset ι) : ℂ → ℂ :=
  fun z =>
    Complex.I * b
      + ∑ i ∈ F,
          Complex.I *
            (1 / (((1 / 2 : ℂ) + Complex.I * z) - zeroLoc i)
              + 1 / zeroLoc i)

/-- 🌟🌟🌟 **PROVED — expand the explicit z-plane Hadamard contribution
as the prefactor term plus the pulled-back regularized zero series.**

This is the form the Stieltjes proof actually integrates/splits:
the constant chain-rule term `I*b` plus the genus-one zero sum on the
line `s = 1/2 + I*z`. -/
theorem expAffineHadamardPullbackZeroContribution_eq_prefactor_plus_tsum
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) :
    expAffineHadamardPullbackZeroContribution zeroLoc b z
      =
    Complex.I * b
      + ∑' i : ι,
          Complex.I *
            (1 / (((1 / 2 : ℂ) + Complex.I * z) - zeroLoc i)
              + 1 / zeroLoc i) := by
  unfold expAffineHadamardPullbackZeroContribution
    hadamardRegularizedLogDerivSeries
  rw [mul_add, tsum_mul_left]

/-- 🌟🌟 **PROVED — finite expanded pullback contribution in terms of
the existing finite regularized Hadamard sum.** -/
theorem expAffineHadamardPullbackFiniteContribution_eq_prefactor_plus_finiteRegularizedSum
    {ι : Type} (zeroLoc : ι → ℂ) (b : ℂ) (F : Finset ι) (z : ℂ) :
    expAffineHadamardPullbackFiniteContribution zeroLoc b F z
      =
    Complex.I * b
      + Complex.I *
          finiteHadamardRegularizedSum zeroLoc F
            ((1 / 2 : ℂ) + Complex.I * z) := by
  unfold expAffineHadamardPullbackFiniteContribution
    finiteHadamardRegularizedSum
  rw [Finset.mul_sum]

/-- 🌟🌟🌟 **PROVED — compact and expanded exp-affine Hadamard pullback
contributions agree pointwise.** -/
theorem expAffineHadamardPullbackZeroContribution_eq_expanded
    {ι : Type} (zeroLoc : ι → ℂ) (b z : ℂ) :
    expAffineHadamardPullbackZeroContribution zeroLoc b z
      =
    expAffineHadamardPullbackZeroContributionExpanded zeroLoc b z := by
  rw [expAffineHadamardPullbackZeroContribution_eq_prefactor_plus_tsum]
  rfl


end OverflowResidueRH
