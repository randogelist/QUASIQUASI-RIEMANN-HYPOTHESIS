/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.FieldSimp
import RiemannHypothesis.HadamardProduct.GenusOne

/-!
# HadamardProduct.InfiniteProducts

Finite, indexed-finite, and infinite genus-one Hadamard products, with their
log-derivative identities. Each finite product's logarithmic derivative is the
regularized zero-sum `Σ (1/(s-ρ) + 1/ρ)`; the indexed/infinite products lift this to an
arbitrary index set via Mathlib's `tprod`/`tsum`. Identity content only.

## Main declarations

* `finiteHadamardProduct`, `indexedFiniteHadamardProduct`, `infiniteHadamardProduct`,
  `hadamardRegularizedLogDerivSeries`, `finiteHadamardRegularizedSum` — the products and
  series.
* `logDeriv_finiteHadamardProduct(_regularized)`,
  `logDeriv_indexedFiniteHadamardProduct` — log-derivative = regularized zero-sum.
* `deriv_indexedFiniteHadamardProduct(_eq_response)` — the finite derivative identity.
-/

namespace OverflowResidueRH

/-- **Finite Hadamard product** over a finite set of zero ordinates. -/
noncomputable def finiteHadamardProduct (zeros : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ zeros, hadamardGenus1Factor ρ s

/-- 🌟🌟 **PROVED — `logDeriv` of the finite Hadamard product = Σ of
per-factor `logDeriv`s.** Direct application of Mathlib's `logDeriv_prod`. -/
theorem logDeriv_finiteHadamardProduct
    {zeros : Finset ℂ} {s : ℂ}
    (hρ_ne : ∀ ρ ∈ zeros, ρ ≠ 0)
    (hs_ne : ∀ ρ ∈ zeros, s ≠ ρ) :
    logDeriv (finiteHadamardProduct zeros) s
      = ∑ ρ ∈ zeros, logDeriv (hadamardGenus1Factor ρ) s := by
  unfold finiteHadamardProduct
  exact logDeriv_prod
    (fun ρ hρ => hadamardGenus1Factor_ne_zero (hρ_ne ρ hρ) (hs_ne ρ hρ))
    (fun ρ _ => hadamardGenus1Factor_differentiableAt ρ s)

/-- 🌟🌟 **PROVED — `logDerivativeResponse` of the finite Hadamard
product = Σ of per-factor responses.** -/
theorem logDerivativeResponse_finiteHadamardProduct
    {zeros : Finset ℂ} {s : ℂ}
    (hρ_ne : ∀ ρ ∈ zeros, ρ ≠ 0)
    (hs_ne : ∀ ρ ∈ zeros, s ≠ ρ) :
    logDerivativeResponse (finiteHadamardProduct zeros) s
      = ∑ ρ ∈ zeros, logDerivativeResponse (hadamardGenus1Factor ρ) s := by
  simp only [logDerivativeResponse_eq_logDeriv]
  exact logDeriv_finiteHadamardProduct hρ_ne hs_ne

/-- 🌟🌟🌟 **PROVED — regularized form of the finite Hadamard product
log-derivative.** `logDeriv (finiteHadamardProduct zeros) s =
Σ_{ρ ∈ zeros} (1/(s-ρ) + 1/ρ)`. -/
theorem logDeriv_finiteHadamardProduct_regularized
    {zeros : Finset ℂ} {s : ℂ}
    (hρ_ne : ∀ ρ ∈ zeros, ρ ≠ 0)
    (hs_ne : ∀ ρ ∈ zeros, s ≠ ρ) :
    logDeriv (finiteHadamardProduct zeros) s
      = ∑ ρ ∈ zeros, (1 / (s - ρ) + 1 / ρ) := by
  rw [logDeriv_finiteHadamardProduct hρ_ne hs_ne]
  apply Finset.sum_congr rfl
  intro ρ hρmem
  exact logDeriv_hadamardGenus1Factor (hρ_ne ρ hρmem) (hs_ne ρ hρmem)

/-- 🌟🌟🌟 **PROVED — regularized form of the finite Hadamard product
`logDerivativeResponse`.** -/
theorem logDerivativeResponse_finiteHadamardProduct_regularized
    {zeros : Finset ℂ} {s : ℂ}
    (hρ_ne : ∀ ρ ∈ zeros, ρ ≠ 0)
    (hs_ne : ∀ ρ ∈ zeros, s ≠ ρ) :
    logDerivativeResponse (finiteHadamardProduct zeros) s
      = ∑ ρ ∈ zeros, (1 / (s - ρ) + 1 / ρ) := by
  rw [logDerivativeResponse_eq_logDeriv]
  exact logDeriv_finiteHadamardProduct_regularized hρ_ne hs_ne

/-- **Indexed infinite Hadamard product** over an arbitrary index set of
zero ordinates. Falls back to `1` when not multipliable (Mathlib's `tprod`). -/
noncomputable def infiniteHadamardProduct
    {ι : Type*} (zeroLoc : ι → ℂ) (s : ℂ) : ℂ :=
  ∏' i : ι, hadamardGenus1Factor (zeroLoc i) s

/-- **Indexed regularized log-derivative series** `Σ (1/(s-ρᵢ) + 1/ρᵢ)`.
Falls back to `0` when not summable. -/
noncomputable def hadamardRegularizedLogDerivSeries
    {ι : Type*} (zeroLoc : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, (1 / (s - zeroLoc i) + 1 / zeroLoc i)

/-- **Finite regularized log-derivative sum** over a Finset. -/
noncomputable def finiteHadamardRegularizedSum
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) (s : ℂ) : ℂ :=
  ∑ i ∈ F, (1 / (s - zeroLoc i) + 1 / zeroLoc i)

/-- **Indexed finite Hadamard product**: the partial product over a Finset,
used for finite truncations of `infiniteHadamardProduct`. -/
noncomputable def indexedFiniteHadamardProduct
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) (s : ℂ) : ℂ :=
  ∏ i ∈ F, hadamardGenus1Factor (zeroLoc i) s

/-- ⭐ **PROVED — every indexed finite Hadamard product is normalized
to `1` at the origin.** -/
theorem indexedFiniteHadamardProduct_zero
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) :
    indexedFiniteHadamardProduct zeroLoc F 0 = 1 := by
  simp [indexedFiniteHadamardProduct, hadamardGenus1Factor_zero]

/-- ⭐ **PROVED — the infinite genus-one Hadamard product is normalized
to `1` at the origin.** -/
theorem infiniteHadamardProduct_zero
    {ι : Type*} (zeroLoc : ι → ℂ) :
    infiniteHadamardProduct zeroLoc 0 = 1 := by
  simp [infiniteHadamardProduct, hadamardGenus1Factor_zero]

/-- 🌟🌟🌟 **PROVED — indexed finite Hadamard product log-derivative.**
The log-derivative of the indexed finite product equals the indexed
regularized sum. -/
theorem logDeriv_indexedFiniteHadamardProduct
    {ι : Type*} {zeroLoc : ι → ℂ} {F : Finset ι} {s : ℂ}
    (hρ : ∀ i ∈ F, zeroLoc i ≠ 0)
    (hs : ∀ i ∈ F, s ≠ zeroLoc i) :
    logDeriv (fun s' : ℂ => indexedFiniteHadamardProduct zeroLoc F s') s
      = finiteHadamardRegularizedSum zeroLoc F s := by
  unfold indexedFiniteHadamardProduct finiteHadamardRegularizedSum
  rw [logDeriv_prod (f := fun i => fun s' => hadamardGenus1Factor (zeroLoc i) s')
        (fun i hi => hadamardGenus1Factor_ne_zero (hρ i hi) (hs i hi))
        (fun i _ => hadamardGenus1Factor_differentiableAt (zeroLoc i) s)]
  apply Finset.sum_congr rfl
  intro i hi
  exact logDeriv_hadamardGenus1Factor (hρ i hi) (hs i hi)

/-- 🌟🌟🌟 **PROVED — indexed finite Hadamard product
`logDerivativeResponse`.** -/
theorem logDerivativeResponse_indexedFiniteHadamardProduct
    {ι : Type*} {zeroLoc : ι → ℂ} {F : Finset ι} {s : ℂ}
    (hρ : ∀ i ∈ F, zeroLoc i ≠ 0)
    (hs : ∀ i ∈ F, s ≠ zeroLoc i) :
    logDerivativeResponse
        (fun s' : ℂ => indexedFiniteHadamardProduct zeroLoc F s') s
      = finiteHadamardRegularizedSum zeroLoc F s := by
  rw [logDerivativeResponse_eq_logDeriv]
  exact logDeriv_indexedFiniteHadamardProduct hρ hs

/-- 🌟🌟🌟 **PROVED — derivative of an indexed finite Hadamard product.**
Away from the indexed zeros, the derivative of the finite genus-one
product is the product times its regularized finite log-derivative sum. -/
theorem deriv_indexedFiniteHadamardProduct
    {ι : Type*} {zeroLoc : ι → ℂ} {F : Finset ι} {s : ℂ}
    (hρ : ∀ i ∈ F, zeroLoc i ≠ 0)
    (hs : ∀ i ∈ F, s ≠ zeroLoc i) :
    deriv (fun s' : ℂ => indexedFiniteHadamardProduct zeroLoc F s') s
      =
    indexedFiniteHadamardProduct zeroLoc F s
      * finiteHadamardRegularizedSum zeroLoc F s := by
  have hprod_ne :
      indexedFiniteHadamardProduct zeroLoc F s ≠ 0 := by
    unfold indexedFiniteHadamardProduct
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact hadamardGenus1Factor_ne_zero (hρ i hi) (hs i hi))
  have hlog :=
    logDeriv_indexedFiniteHadamardProduct
      (zeroLoc := zeroLoc) (F := F) (s := s) hρ hs
  simp only [logDeriv_apply] at hlog
  field_simp [hprod_ne] at hlog
  exact hlog

/-- 🌟🌟🌟 **PROVED — finite derivative response identity for indexed
Hadamard products.** The same statement in `logDerivativeResponse`
coordinates. -/
theorem deriv_indexedFiniteHadamardProduct_eq_response
    {ι : Type*} {zeroLoc : ι → ℂ} {F : Finset ι} {s : ℂ}
    (hρ : ∀ i ∈ F, zeroLoc i ≠ 0)
    (hs : ∀ i ∈ F, s ≠ zeroLoc i) :
    deriv (fun s' : ℂ => indexedFiniteHadamardProduct zeroLoc F s') s
      =
    indexedFiniteHadamardProduct zeroLoc F s
      * logDerivativeResponse
          (fun s' : ℂ => indexedFiniteHadamardProduct zeroLoc F s') s := by
  rw [logDerivativeResponse_indexedFiniteHadamardProduct hρ hs]
  exact deriv_indexedFiniteHadamardProduct hρ hs

/-- 🌟🌟 **PROVED — the infinite Hadamard product vanishes at every
indexed zero.** This discharges the zero-side of the quotient
factorization data directly from the canonical genus-one factor. -/
theorem infiniteHadamardProduct_eq_zero_at_zeroLoc
    {ι : Type*} {zeroLoc : ι → ℂ}
    (hzero : ∀ i : ι, zeroLoc i ≠ 0)
    (i : ι) :
    infiniteHadamardProduct zeroLoc (zeroLoc i) = 0 := by
  unfold infiniteHadamardProduct
  exact tprod_of_exists_eq_zero
    ⟨i, hadamardGenus1Factor_self_eq_zero (hzero i)⟩

end OverflowResidueRH
