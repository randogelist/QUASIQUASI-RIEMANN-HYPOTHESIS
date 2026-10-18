/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Explicit factorial growth bounds for Mellin transforms

This file turns two-sided exponential decay of a kernel into a global,
explicit factorial envelope for its Mellin transform.  It is designed for the
theta-kernel representation of the completed zeta function.

The positive half of the Mellin integral is dominated by

`x ^ n * exp (-p * x)`,

whose integral is `p ^ (-(n + 1)) * n!`.  On `(0, 1]`, inversion changes the
model kernel

`x ^ (-(n + 2)) * exp (-p / x)`

into the same gamma integral.  The final theorem combines the two estimates
without asymptotic notation and preserves all constants.
-/

namespace OverflowResidueRH

open MeasureTheory Set
open Real

/-- An exponent bounded above by a natural number can be dominated on
`[1, ∞)` by the corresponding gamma-integrable natural power. -/
theorem integrableOn_Ioi_one_rpow_mul_exp_neg_mul_of_le_nat
    {q p : ℝ} (n : ℕ) (hp : 0 < p) (hq : q ≤ n) :
    IntegrableOn (fun x : ℝ ↦ x ^ q * exp (-(p * x))) (Ioi 1) := by
  let g : ℝ → ℝ := fun x ↦ x ^ (n : ℝ) * exp (-(p * x))
  have hg_int : IntegrableOn g (Ioi 0) := by
    simpa [g] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (n : ℝ)) (p := (1 : ℝ)) (b := p)
        (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)
        (by norm_num) hp)
  refine (hg_int.mono_set (Ioi_subset_Ioi zero_lt_one.le)).mono_nonneg ?_ ?_ ?_
  · fun_prop
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦
      mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx.le) _)
        (Real.exp_nonneg _)
  · exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hx.le hq) (Real.exp_nonneg _)

/-- The upper Mellin tail is bounded by a scaled factorial. -/
theorem integral_Ioi_one_rpow_mul_exp_neg_mul_le_factorial
    {q p : ℝ} (n : ℕ) (hp : 0 < p) (hq : q ≤ n) :
    (∫ x : ℝ in Ioi 1, x ^ q * exp (-(p * x))) ≤
      (1 / p) ^ (n + 1 : ℝ) * n.factorial := by
  let g : ℝ → ℝ := fun x ↦ x ^ (n : ℝ) * exp (-(p * x))
  have hg_int : IntegrableOn g (Ioi 0) := by
    simpa [g] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (n : ℝ)) (p := (1 : ℝ)) (b := p)
        (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)
        (by norm_num) hp)
  have hpoint : ∀ x ∈ Ioi (1 : ℝ),
      x ^ q * exp (-(p * x)) ≤ g x := by
    intro x hx
    dsimp [g]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx.le hq) (Real.exp_nonneg _)
  have hleft_int :
      IntegrableOn (fun x : ℝ ↦ x ^ q * exp (-(p * x))) (Ioi 1) :=
    integrableOn_Ioi_one_rpow_mul_exp_neg_mul_of_le_nat n hp hq
  calc
    (∫ x : ℝ in Ioi 1, x ^ q * exp (-(p * x)))
        ≤ ∫ x : ℝ in Ioi 1, g x :=
          setIntegral_mono_on hleft_int
            (hg_int.mono_set (Ioi_subset_Ioi zero_lt_one.le)) measurableSet_Ioi hpoint
    _ ≤ ∫ x : ℝ in Ioi 0, g x := by
      apply setIntegral_mono_set hg_int
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        dsimp [g]
        exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_nonneg _)
      · exact (Ioi_subset_Ioi zero_lt_one.le).eventuallyLE
    _ = (1 / p) ^ (n + 1 : ℝ) * n.factorial := by
      dsimp [g]
      simpa [Real.Gamma_nat_eq_factorial] using
        (integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := p)
          (by
            have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith)
          hp)

/-- Under inversion, the lower-tail model has exactly the same gamma
integral as the upper-tail model. -/
theorem integral_Ioi_zero_inv_rpow_mul_exp_neg_mul_eq_factorial
    (n : ℕ) {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ in Ioi 0,
        x ^ (-(n : ℝ) - 2) * exp (-(p / x))) =
      (1 / p) ^ (n + 1 : ℝ) * n.factorial := by
  let g : ℝ → ℝ := fun y ↦ y ^ (n : ℝ) * exp (-(p * y))
  have hsub := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
  have hleft :
      (∫ x : ℝ in Ioi 0,
          ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ)))) =
        ∫ x : ℝ in Ioi 0,
          x ^ (-(n : ℝ) - 2) * exp (-(p / x)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    dsimp [g]
    rw [← Real.rpow_mul hx0.le]
    rw [abs_neg, abs_one, one_mul, ← mul_assoc,
      ← Real.rpow_add hx0, Real.rpow_neg_one]
    congr 2
    · ring
  rw [← hleft, hsub]
  simpa [g, Real.Gamma_nat_eq_factorial] using
    (integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := p)
      (by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
      hp)

/-- The inverted lower-tail model is integrable. -/
theorem integrableOn_Ioi_zero_inv_rpow_mul_exp_neg_mul
    (n : ℕ) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ ↦
      x ^ (-(n : ℝ) - 2) * exp (-(p / x))) (Ioi 0) := by
  let g : ℝ → ℝ := fun y ↦ y ^ (n : ℝ) * exp (-(p * y))
  have hg_int : IntegrableOn g (Ioi 0) := by
    simpa [g] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (n : ℝ)) (p := (1 : ℝ)) (b := p)
        (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)
        (by norm_num) hp)
  have htrans : IntegrableOn
      (fun x : ℝ ↦ (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
        g (x ^ (-1 : ℝ))) (Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff g (p := (-1 : ℝ)) (by norm_num)).mpr hg_int
  refine htrans.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  dsimp [g]
  rw [← Real.rpow_mul hx0.le]
  rw [abs_neg, abs_one, one_mul, ← mul_assoc,
    ← Real.rpow_add hx0, Real.rpow_neg_one]
  congr 2
  · ring

/-- Quantitative two-sided decay for a Mellin kernel.  The power `x⁻ᵏ` in
the lower tail records the weight introduced by a functional equation. -/
structure MellinTwoSidedExponentialDecay (f : ℝ → ℂ) : Type where
  k : ℝ
  p : ℝ
  A : ℝ
  p_pos : 0 < p
  A_nonneg : 0 ≤ A
  upper : ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ A * exp (-(p * x))
  lower : ∀ x : ℝ, 0 < x → x ≤ 1 →
    ‖f x‖ ≤ A * x ^ (-k) * exp (-(p / x))

/-- Two-sided exponential decay bounds a convergent Mellin transform by an
explicit factorial envelope.  The exponent hypotheses say that `n` dominates
both powers occurring after splitting the integral at `1`. -/
theorem MellinTwoSidedExponentialDecay.norm_mellin_le_factorial
    {f : ℝ → ℂ} (H : MellinTwoSidedExponentialDecay f)
    (s : ℂ) (n : ℕ)
    (hupper : s.re - 1 ≤ n)
    (hlower : -(n : ℝ) - 2 ≤ s.re - 1 - H.k)
    (hconv : MellinConvergent f s) :
    ‖mellin f s‖ ≤
      2 * H.A * ((1 / H.p) ^ (n + 1 : ℝ) * n.factorial) := by
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) • f x
  let E : ℝ := (1 / H.p) ^ (n + 1 : ℝ) * n.factorial
  have hF_int : IntegrableOn F (Ioi 0) := by
    simpa only [F, MellinConvergent] using hconv
  have hFnorm_full : IntegrableOn (fun x : ℝ ↦ ‖F x‖) (Ioi 0) := hF_int.norm
  have hFnorm (x : ℝ) (hx : 0 < x) :
      ‖F x‖ = x ^ (s.re - 1) * ‖f x‖ := by
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hupper_int :
      ∫ x : ℝ in Ioi 1, ‖F x‖ ≤ H.A * E := by
    have hmajor_int : IntegrableOn
        (fun x : ℝ ↦ H.A * (x ^ (s.re - 1) * exp (-(H.p * x))))
        (Ioi 1) :=
      (integrableOn_Ioi_one_rpow_mul_exp_neg_mul_of_le_nat
        n H.p_pos hupper).const_mul H.A
    have hFnorm_int : IntegrableOn (fun x : ℝ ↦ ‖F x‖) (Ioi 1) :=
      IntegrableOn.mono_set hFnorm_full (Ioi_subset_Ioi zero_lt_one.le)
    calc
      ∫ x : ℝ in Ioi 1, ‖F x‖ ≤
          ∫ x : ℝ in Ioi 1,
            H.A * (x ^ (s.re - 1) * exp (-(H.p * x))) := by
        apply setIntegral_mono_on hFnorm_int hmajor_int measurableSet_Ioi
        intro x hx
        rw [hFnorm x (zero_lt_one.trans hx)]
        calc
          x ^ (s.re - 1) * ‖f x‖ ≤
              x ^ (s.re - 1) * (H.A * exp (-(H.p * x))) :=
            mul_le_mul_of_nonneg_left (H.upper x hx.le)
              (Real.rpow_nonneg (zero_le_one.trans hx.le) _)
          _ = H.A * (x ^ (s.re - 1) * exp (-(H.p * x))) := by ring
      _ = H.A *
          (∫ x : ℝ in Ioi 1,
            x ^ (s.re - 1) * exp (-(H.p * x))) := by
        rw [← integral_const_mul]
      _ ≤ H.A * E := by
        exact mul_le_mul_of_nonneg_left
          (integral_Ioi_one_rpow_mul_exp_neg_mul_le_factorial
            n H.p_pos hupper) H.A_nonneg
  have hlower_int :
      ∫ x : ℝ in Ioc 0 1, ‖F x‖ ≤ H.A * E := by
    have hmajor_full : IntegrableOn
        (fun x : ℝ ↦ H.A *
          (x ^ (-(n : ℝ) - 2) * exp (-(H.p / x)))) (Ioi 0) :=
      (integrableOn_Ioi_zero_inv_rpow_mul_exp_neg_mul n H.p_pos).const_mul H.A
    have hmajor_int : IntegrableOn
        (fun x : ℝ ↦ H.A *
          (x ^ (-(n : ℝ) - 2) * exp (-(H.p / x)))) (Ioc 0 1) :=
      IntegrableOn.mono_set hmajor_full Ioc_subset_Ioi_self
    have hFnorm_int : IntegrableOn (fun x : ℝ ↦ ‖F x‖) (Ioc 0 1) :=
      IntegrableOn.mono_set hFnorm_full Ioc_subset_Ioi_self
    calc
      ∫ x : ℝ in Ioc 0 1, ‖F x‖ ≤
          ∫ x : ℝ in Ioc 0 1,
            H.A * (x ^ (-(n : ℝ) - 2) * exp (-(H.p / x))) := by
        apply setIntegral_mono_on hFnorm_int hmajor_int measurableSet_Ioc
        intro x hx
        rw [hFnorm x hx.1]
        calc
          x ^ (s.re - 1) * ‖f x‖ ≤
              x ^ (s.re - 1) *
                (H.A * x ^ (-H.k) * exp (-(H.p / x))) :=
            mul_le_mul_of_nonneg_left (H.lower x hx.1 hx.2)
              (Real.rpow_nonneg hx.1.le _)
          _ = H.A *
              (x ^ (s.re - 1 - H.k) * exp (-(H.p / x))) := by
            calc
              x ^ (s.re - 1) *
                    (H.A * x ^ (-H.k) * exp (-(H.p / x))) =
                  H.A * ((x ^ (s.re - 1) * x ^ (-H.k)) *
                    exp (-(H.p / x))) := by ring
              _ = H.A *
                    (x ^ (s.re - 1 - H.k) * exp (-(H.p / x))) := by
                rw [← Real.rpow_add hx.1]
                ring_nf
          _ ≤ H.A *
              (x ^ (-(n : ℝ) - 2) * exp (-(H.p / x))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hlower)
                (Real.exp_nonneg _)) H.A_nonneg
      _ ≤ ∫ x : ℝ in Ioi 0,
            H.A * (x ^ (-(n : ℝ) - 2) * exp (-(H.p / x))) := by
        apply setIntegral_mono_set hmajor_full
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact mul_nonneg H.A_nonneg
            (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_nonneg _))
        · exact Ioc_subset_Ioi_self.eventuallyLE
      _ = H.A * E := by
        rw [integral_const_mul]
        dsimp [E]
        rw [integral_Ioi_zero_inv_rpow_mul_exp_neg_mul_eq_factorial n H.p_pos]
  calc
    ‖mellin f s‖ = ‖∫ x : ℝ in Ioi 0, F x‖ := rfl
    _ ≤ ∫ x : ℝ in Ioi 0, ‖F x‖ := norm_integral_le_integral_norm _
    _ = (∫ x : ℝ in Ioc 0 1, ‖F x‖) +
        ∫ x : ℝ in Ioi 1, ‖F x‖ := by
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
      · exact IntegrableOn.mono_set hFnorm_full Ioc_subset_Ioi_self
      · exact IntegrableOn.mono_set hFnorm_full (Ioi_subset_Ioi zero_lt_one.le)
    _ ≤ H.A * E + H.A * E := add_le_add hlower_int hupper_int
    _ = 2 * H.A * E := by ring

end OverflowResidueRH
