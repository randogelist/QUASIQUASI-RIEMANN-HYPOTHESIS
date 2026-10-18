/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import RiemannHypothesis.ComplexAnalysis.GrowthRigidity

/-!
# Entire quotients with matched divisors

This file isolates two generic analytic steps used in Hadamard-factorization
arguments.

* `entireQuotientCompletion` fills the removable singularities of `f / g`.
  If two entire functions have the same finite analytic order at every point,
  the completed quotient is entire and nowhere zero.
* Every nowhere-zero entire function is the exponential of an entire function.
  The proof integrates its logarithmic derivative, so it does not choose a
  discontinuous pointwise branch of `Complex.log`.
* The final bridge applies the reusable subquadratic-growth rigidity theorem to
  such an entire logarithm.

The file deliberately does not assert a growth bound for the Riemann xi
function or for a canonical product quotient.
-/

open Metric Set

namespace OverflowResidueRH

/-- The global normal-form completion of the pointwise quotient `f / g`.

At a common zero, field division is totalized and therefore has the wrong
value.  `toMeromorphicNFOn` replaces precisely these isolated bad values by
their meromorphic normal-form values. -/
noncomputable def entireQuotientCompletion (f g : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (f / g) Set.univ

private theorem entireQuotientCompletion_meromorphicOrderAt_eq_zero
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (horder : ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤)
    (z : ℂ) :
    meromorphicOrderAt (entireQuotientCompletion f g) z = 0 := by
  have hmer : MeromorphicOn (f / g) Set.univ := by
    intro w _hw
    exact (hf.analyticAt w).meromorphicAt.div (hg.analyticAt w).meromorphicAt
  rw [entireQuotientCompletion,
    meromorphicOrderAt_toMeromorphicNFOn hmer (Set.mem_univ z),
    meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt
      (hg.analyticAt z).meromorphicAt,
    (hf.analyticAt z).meromorphicOrderAt_eq,
    (hg.analyticAt z).meromorphicOrderAt_eq]
  lift analyticOrderAt f z to ℕ using hfinite z with n hn
  have hgn : analyticOrderAt g z = n := by
    rw [← horder z, hn]
  rw [hgn]
  simp

/-- Equal finite analytic-order divisors make the completed quotient entire. -/
theorem entireQuotientCompletion_differentiable
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (horder : ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤) :
    Differentiable ℂ (entireQuotientCompletion f g) := by
  intro z
  have hnormal :
      MeromorphicNFAt (entireQuotientCompletion f g) z :=
    meromorphicNFOn_toMeromorphicNFOn (f / g) Set.univ (Set.mem_univ z)
  exact (hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp <| by
    rw [entireQuotientCompletion_meromorphicOrderAt_eq_zero
      hf hg horder hfinite z]).differentiableAt

/-- Equal finite analytic-order divisors make the completed quotient nowhere
zero. -/
theorem entireQuotientCompletion_ne_zero
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (horder : ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤)
    (z : ℂ) :
    entireQuotientCompletion f g z ≠ 0 := by
  have hnormal :
      MeromorphicNFAt (entireQuotientCompletion f g) z :=
    meromorphicNFOn_toMeromorphicNFOn (f / g) Set.univ (Set.mem_univ z)
  exact hnormal.meromorphicOrderAt_eq_zero_iff.mp
    (entireQuotientCompletion_meromorphicOrderAt_eq_zero
      hf hg horder hfinite z)

/-- Away from zeros of the denominator, completion does not change the
ordinary quotient. -/
theorem entireQuotientCompletion_eq_div
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    {z : ℂ} (hgz : g z ≠ 0) :
    entireQuotientCompletion f g z = f z / g z := by
  have hmer : MeromorphicOn (f / g) Set.univ := by
    intro w _hw
    exact (hf.analyticAt w).meromorphicAt.div (hg.analyticAt w).meromorphicAt
  have hnormal : MeromorphicNFAt (f / g) z :=
    ((hf.analyticAt z).div (hg.analyticAt z) hgz).meromorphicNFAt
  rw [entireQuotientCompletion,
    toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (Set.mem_univ z),
    toMeromorphicNFAt_eq_self.2 hnormal]
  simp only [Pi.div_apply]

/-- A nowhere-zero entire function has an entire logarithm.

The logarithm is obtained by integrating `q' / q`, normalized to
`Complex.log (q 0)`.  Constancy of `exp h / q` then gives `exp h = q`
globally. -/
theorem exists_differentiable_log_of_differentiable_ne_zero
    {q : ℂ → ℂ}
    (hq : Differentiable ℂ q)
    (hq_ne : ∀ z : ℂ, q z ≠ 0) :
    ∃ h : ℂ → ℂ,
      Differentiable ℂ h ∧ ∀ z : ℂ, Complex.exp (h z) = q z := by
  let r : ℂ → ℂ := fun z ↦ deriv q z / q z
  have hq_deriv : Differentiable ℂ (deriv q) := by
    intro z
    exact (hq.analyticAt z).deriv.differentiableAt
  have hr : Differentiable ℂ r := by
    intro z
    exact (hq_deriv z).div (hq z) (hq_ne z)
  obtain ⟨h, hh_zero, hh_deriv⟩ :=
    hr.isExactOn_univ.with_val_at 0 (Complex.log (q 0))
  have hh : Differentiable ℂ h := by
    intro z
    exact (hh_deriv z (Set.mem_univ z)).differentiableAt
  let u : ℂ → ℂ := fun z ↦ Complex.exp (h z) / q z
  have hu : Differentiable ℂ u := by
    intro z
    exact (hh z).cexp.div (hq z) (hq_ne z)
  have hu_deriv : ∀ z : ℂ, deriv u z = 0 := by
    intro z
    have hhz := hh_deriv z (Set.mem_univ z)
    change deriv (fun w : ℂ ↦ Complex.exp (h w) / q w) z = 0
    rw [deriv_fun_div (hh z).cexp (hq z) (hq_ne z),
      deriv_cexp (hh z), hhz.deriv]
    dsimp [r]
    field_simp [hq_ne z]
    ring
  have hu_const (z : ℂ) : u z = u 0 :=
    is_const_of_deriv_eq_zero hu hu_deriv z 0
  have hu_zero : u 0 = 1 := by
    dsimp [u]
    rw [hh_zero, Complex.exp_log (hq_ne 0), div_self (hq_ne 0)]
  refine ⟨h, hh, fun z ↦ ?_⟩
  have huz : u z = 1 := (hu_const z).trans hu_zero
  exact (div_eq_one_iff_eq (hq_ne z)).mp (by simpa [u] using huz)

/-- If an entire logarithm of a zero-free quotient has subquadratic norm
growth, then the quotient is an affine exponential.  This is the exact handoff
from divisor matching to `differentiable_eq_affine_of_subquadraticNormGrowth`.
-/
theorem eq_exp_affine_of_differentiable_log_of_subquadraticNormGrowth
    {q h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hexp : ∀ z : ℂ, Complex.exp (h z) = q z)
    (hgrowth : HasSubquadraticNormGrowth h) :
    ∃ a b : ℂ, ∀ z : ℂ, q z = Complex.exp (a + b * z) := by
  obtain ⟨a, b, hab⟩ :=
    differentiable_eq_affine_of_subquadraticNormGrowth hh hgrowth
  exact ⟨a, b, fun z ↦ by rw [← hexp z, hab z]⟩

/-- A zero-free entire completed quotient therefore has an entire logarithm.
This packages the two generic steps most directly used by a Hadamard quotient
argument. -/
theorem exists_differentiable_log_entireQuotientCompletion
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (horder : ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z : ℂ, analyticOrderAt f z ≠ ⊤) :
    ∃ h : ℂ → ℂ,
      Differentiable ℂ h ∧
        ∀ z : ℂ,
          Complex.exp (h z) = entireQuotientCompletion f g z :=
  exists_differentiable_log_of_differentiable_ne_zero
    (entireQuotientCompletion_differentiable hf hg horder hfinite)
    (entireQuotientCompletion_ne_zero hf hg horder hfinite)

end OverflowResidueRH
