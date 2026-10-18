/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.Liouville

/-!
# Quantitative rigidity for entire functions

This module records two elementary but useful consequences of Cauchy's
estimates.  They are formulated as little-oh growth conditions at infinity,
without introducing an order-of-an-entire-function API.

* `differentiable_eq_const_of_sublinearNormGrowth` says that an entire
  function satisfying `‖f z‖ = o(‖z‖)` is constant.
* `differentiable_eq_affine_of_subquadraticNormGrowth` says that an entire
  function satisfying `‖f z‖ = o(‖z‖²)` is affine.

The proofs use Cauchy estimates on circles centered at an arbitrary point.
The radius is chosen large enough that every point of the circle lies in the
region where the asymptotic estimate applies.  This moving-center formulation
is particularly convenient for controlling the entire remainder in a
Hadamard or Mittag--Leffler logarithmic-derivative expansion.
-/

namespace OverflowResidueRH

open Metric Set

/-- `f` has sublinear norm growth at infinity: for every positive `ε`, one
eventually has `‖f z‖ ≤ ε * ‖z‖`. -/
def HasSublinearNormGrowth (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ ε * ‖z‖

/-- Adding a constant does not change sublinear norm growth at infinity. -/
theorem HasSublinearNormGrowth.add_const
    {f : ℂ → ℂ} (hf : HasSublinearNormGrowth f) (c : ℂ) :
    HasSublinearNormGrowth (fun z => f z + c) := by
  intro ε hε
  obtain ⟨Rf, hRf, hf_bound⟩ := hf (ε / 2) (by positivity)
  let Rc : ℝ := 2 * ‖c‖ / ε
  refine ⟨max Rf Rc, hRf.trans (le_max_left _ _), ?_⟩
  intro z hz
  have hzRf : Rf ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hzRc : Rc ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hc : ‖c‖ ≤ (ε / 2) * ‖z‖ := by
    have hmul : 2 * ‖c‖ ≤ ‖z‖ * ε := (div_le_iff₀ hε).mp hzRc
    nlinarith
  calc
    ‖f z + c‖ ≤ ‖f z‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖z‖ + (ε / 2) * ‖z‖ :=
      add_le_add (hf_bound z hzRf) hc
    _ = ε * ‖z‖ := by ring

/-- Subtracting a constant does not change sublinear norm growth. -/
theorem HasSublinearNormGrowth.sub_const
    {f : ℂ → ℂ} (hf : HasSublinearNormGrowth f) (c : ℂ) :
    HasSublinearNormGrowth (fun z => f z - c) := by
  simpa [sub_eq_add_neg] using hf.add_const (-c)

/-- The derivative of an entire function with sublinear norm growth vanishes
at every point.  This is the first-derivative Cauchy estimate with an
arbitrarily small asymptotic coefficient. -/
theorem deriv_eq_zero_of_sublinearNormGrowth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : HasSublinearNormGrowth f) (c : ℂ) :
    deriv f c = 0 := by
  apply norm_le_zero_iff.mp
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro ε hε
  obtain ⟨R, _hR, hbound⟩ := hgrowth (ε / 2) (by positivity)
  let r : ℝ := max (R + ‖c‖) (‖c‖ + 1)
  have hr_pos : 0 < r :=
    lt_of_lt_of_le (by positivity : 0 < ‖c‖ + 1) (le_max_right _ _)
  have hr_c : ‖c‖ ≤ r := by
    linarith [le_max_right (R + ‖c‖) (‖c‖ + 1)]
  have hsphere : ∀ z ∈ sphere c r, ‖f z‖ ≤ (ε / 2) * (2 * r) := by
    intro z hz
    have hzdist : ‖z - c‖ = r := mem_sphere_iff_norm.mp hz
    have hlower : R ≤ ‖z‖ := by
      have htri : ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le z c
      rw [hzdist] at htri
      have hr_R : R + ‖c‖ ≤ r := le_max_left _ _
      linarith
    have hupper : ‖z‖ ≤ 2 * r := by
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc
          ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      rw [hzdist] at htri
      linarith
    exact (hbound z hlower).trans
      (mul_le_mul_of_nonneg_left hupper (by positivity))
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr_pos hf.diffContOnCl hsphere
  calc
    ‖deriv f c‖ ≤ ((ε / 2) * (2 * r)) / r := hcauchy
    _ = ε := by field_simp

/-- An entire function with sublinear norm growth is constant. -/
theorem differentiable_eq_const_of_sublinearNormGrowth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : HasSublinearNormGrowth f) :
    ∃ b : ℂ, ∀ z : ℂ, f z = b := by
  exact ⟨f 0, fun z ↦ is_const_of_deriv_eq_zero hf
    (deriv_eq_zero_of_sublinearNormGrowth hf hgrowth) z 0⟩

/-- `f` has subquadratic norm growth at infinity: for every positive `ε`, one
eventually has `‖f z‖ ≤ ε * ‖z‖²`. -/
def HasSubquadraticNormGrowth (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ ε * ‖z‖ ^ 2

/-- Adding a constant does not change subquadratic norm growth at infinity. -/
theorem HasSubquadraticNormGrowth.add_const
    {f : ℂ → ℂ} (hf : HasSubquadraticNormGrowth f) (c : ℂ) :
    HasSubquadraticNormGrowth (fun z => f z + c) := by
  intro ε hε
  obtain ⟨Rf, hRf, hf_bound⟩ := hf (ε / 2) (by positivity)
  let Rc : ℝ := max 1 (2 * ‖c‖ / ε)
  refine ⟨max Rf Rc, hRf.trans (le_max_left _ _), ?_⟩
  intro z hz
  have hzRf : Rf ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hzRc : Rc ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hz_one : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hzRc
  have hz_c : 2 * ‖c‖ / ε ≤ ‖z‖ :=
    le_trans (le_max_right _ _) hzRc
  have hc_linear : ‖c‖ ≤ (ε / 2) * ‖z‖ := by
    have hmul : 2 * ‖c‖ ≤ ‖z‖ * ε := (div_le_iff₀ hε).mp hz_c
    nlinarith
  have hnorm_sq : ‖z‖ ≤ ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg z]
  have hc : ‖c‖ ≤ (ε / 2) * ‖z‖ ^ 2 :=
    hc_linear.trans (mul_le_mul_of_nonneg_left hnorm_sq (by positivity))
  calc
    ‖f z + c‖ ≤ ‖f z‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖z‖ ^ 2 + (ε / 2) * ‖z‖ ^ 2 :=
      add_le_add (hf_bound z hzRf) hc
    _ = ε * ‖z‖ ^ 2 := by ring

/-- Subtracting a constant does not change subquadratic norm growth. -/
theorem HasSubquadraticNormGrowth.sub_const
    {f : ℂ → ℂ} (hf : HasSubquadraticNormGrowth f) (c : ℂ) :
    HasSubquadraticNormGrowth (fun z => f z - c) := by
  simpa [sub_eq_add_neg] using hf.add_const (-c)

/-- The second derivative of an entire function with subquadratic norm growth
vanishes at every point. -/
theorem iteratedDeriv_two_eq_zero_of_subquadraticNormGrowth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : HasSubquadraticNormGrowth f) (c : ℂ) :
    iteratedDeriv 2 f c = 0 := by
  apply norm_le_zero_iff.mp
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro ε hε
  obtain ⟨R, _hR, hbound⟩ := hgrowth (ε / 8) (by positivity)
  let r : ℝ := max (R + ‖c‖) (‖c‖ + 1)
  have hr_pos : 0 < r :=
    lt_of_lt_of_le (by positivity : 0 < ‖c‖ + 1) (le_max_right _ _)
  have hr_c : ‖c‖ ≤ r := by
    linarith [le_max_right (R + ‖c‖) (‖c‖ + 1)]
  have hsphere : ∀ z ∈ sphere c r,
      ‖f z‖ ≤ (ε / 8) * (2 * r) ^ 2 := by
    intro z hz
    have hzdist : ‖z - c‖ = r := mem_sphere_iff_norm.mp hz
    have hlower : R ≤ ‖z‖ := by
      have htri : ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le z c
      rw [hzdist] at htri
      have hr_R : R + ‖c‖ ≤ r := le_max_left _ _
      linarith
    have hupper : ‖z‖ ≤ 2 * r := by
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc
          ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      rw [hzdist] at htri
      linarith
    exact (hbound z hlower).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg z) hupper 2) (by positivity))
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 hr_pos hf.diffContOnCl hsphere
  calc
    ‖iteratedDeriv 2 f c‖ ≤
        (Nat.factorial 2 : ℝ) * ((ε / 8) * (2 * r) ^ 2) / r ^ 2 := hcauchy
    _ = ε := by
      field_simp [ne_of_gt hr_pos]
      ring

/-- An entire function with subquadratic norm growth is affine. -/
theorem differentiable_eq_affine_of_subquadraticNormGrowth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hgrowth : HasSubquadraticNormGrowth f) :
    ∃ a b : ℂ, ∀ z : ℂ, f z = a + b * z := by
  have hderiv_diff : Differentiable ℂ (deriv f) := by
    rw [← differentiableOn_univ]
    exact hf.differentiableOn.deriv isOpen_univ
  have hsecond : ∀ z : ℂ, deriv (deriv f) z = 0 := by
    intro z
    simpa [iteratedDeriv_succ] using
      iteratedDeriv_two_eq_zero_of_subquadraticNormGrowth hf hgrowth z
  let b : ℂ := deriv f 0
  have hderiv_const : ∀ z : ℂ, deriv f z = b := by
    intro z
    exact is_const_of_deriv_eq_zero hderiv_diff hsecond z 0
  refine ⟨f 0, b, ?_⟩
  intro z
  have hlinear_diff : Differentiable ℂ (fun w : ℂ ↦ b * w) := by
    fun_prop
  have hlinear_deriv : ∀ w : ℂ, deriv (fun u : ℂ ↦ b * u) w = b := by
    intro w
    simp
  have heq : ∀ w : ℂ, f w - b * w = f 0 - b * 0 := by
    intro w
    exact is_const_of_deriv_eq_zero (hf.sub hlinear_diff)
      (fun u ↦ by rw [deriv_sub hf.differentiableAt hlinear_diff.differentiableAt,
        hderiv_const, hlinear_deriv, sub_self]) w 0
  specialize heq z
  calc
    f z = (f z - b * z) + b * z := by ring
    _ = (f 0 - b * 0) + b * z := by rw [heq]
    _ = f 0 + b * z := by ring

end OverflowResidueRH
