import RiemannHypothesis.ComplexAnalysis.MellinGrowth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Quantitative Mellin bounds retaining the splitting endpoint at one. -/

noncomputable section
open MeasureTheory Set Real

namespace AngularMaster

theorem integral_Ioi_one_exp_neg_mul {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ in Ioi 1, exp (-(p * x))) = exp (-p) / p := by
  simpa only [neg_mul, mul_one, neg_div_neg_eq] using
    (integral_exp_mul_Ioi (a := -p) (by linarith) 1)

theorem integral_Ioc_zero_one_inv_sq_exp {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ in Ioc 0 1, x ^ (-2 : ℝ) * exp (-(p / x))) = exp (-p) / p := by
  let g : ℝ → ℝ := (Ioi 1).indicator (fun y => exp (-(p * y)))
  have hsub := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
  have heq :
      (∫ x : ℝ in Ioi 0, (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        ∫ x : ℝ in Ioi 0,
          (Iio 1).indicator (fun x => x ^ (-2 : ℝ) * exp (-(p / x))) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    have hi : x ^ (-1 : ℝ) ∈ Ioi (1 : ℝ) ↔ x ∈ Iio (1 : ℝ) := by
      simpa only [Real.rpow_neg_one, mem_Ioi, mem_Iio] using one_lt_inv₀ hx0
    by_cases hx1 : x < 1
    · have hxmem : x ∈ Iio (1 : ℝ) := hx1
      simp only [g, indicator_of_mem (hi.mpr hxmem), indicator_of_mem hxmem,
        abs_neg, abs_one, one_mul, smul_eq_mul]
      norm_num
      rw [Real.rpow_neg_one, div_eq_mul_inv]
      simp
    · have hxmem : x ∉ Iio (1 : ℝ) := hx1
      simp only [g, indicator_of_notMem (fun h => hxmem (hi.mp h)),
        indicator_of_notMem hxmem, smul_zero]
  rw [heq, setIntegral_indicator measurableSet_Iio] at hsub
  have hleft : Ioi (0 : ℝ) ∩ Iio 1 = Ioo 0 1 := by ext x; simp
  rw [hleft] at hsub
  have hright : (∫ y : ℝ in Ioi 0, g y) =
      ∫ y : ℝ in Ioi 1, exp (-(p * y)) := by
    dsimp only [g]
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  rw [hright] at hsub
  rw [integral_Ioc_eq_integral_Ioo, hsub, integral_Ioi_one_exp_neg_mul hp]

open OverflowResidueRH

/-- On the central Mellin strip, both tails retain the endpoint factor
`exp (-p)`. In particular no extension of the upper integral to zero occurs. -/
theorem norm_mellin_le_endpoint
    {f : ℝ → ℂ} (H : MellinTwoSidedExponentialDecay f)
    (s : ℂ) (hupper : s.re - 1 ≤ 0)
    (hlower : -2 ≤ s.re - 1 - H.k)
    (hconv : MellinConvergent f s) :
    ‖mellin f s‖ ≤ 2 * H.A * (exp (-H.p) / H.p) := by
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) • f x
  let E : ℝ := exp (-H.p) / H.p
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
        (fun x : ℝ ↦ H.A * exp (-(H.p * x))) (Ioi 1) := by
      simpa only [neg_mul, IntegrableOn] using
        (integrableOn_exp_mul_Ioi (a := -H.p) (neg_neg_of_pos H.p_pos) 1).const_mul H.A
    have hFnorm_int : IntegrableOn (fun x : ℝ ↦ ‖F x‖) (Ioi 1) :=
      IntegrableOn.mono_set hFnorm_full (Ioi_subset_Ioi zero_lt_one.le)
    calc
      ∫ x : ℝ in Ioi 1, ‖F x‖ ≤
          ∫ x : ℝ in Ioi 1, H.A * exp (-(H.p * x)) := by
        apply setIntegral_mono_on hFnorm_int hmajor_int measurableSet_Ioi
        intro x hx
        rw [hFnorm x (zero_lt_one.trans hx)]
        have hpow : x ^ (s.re - 1) ≤ 1 := by
          simpa using Real.rpow_le_rpow_of_exponent_le hx.le hupper
        calc
          x ^ (s.re - 1) * ‖f x‖ ≤
              x ^ (s.re - 1) * (H.A * exp (-(H.p * x))) :=
            mul_le_mul_of_nonneg_left (H.upper x hx.le)
              (Real.rpow_nonneg (zero_le_one.trans hx.le) _)
          _ ≤ 1 * (H.A * exp (-(H.p * x))) :=
            mul_le_mul_of_nonneg_right hpow (mul_nonneg H.A_nonneg (exp_nonneg _))
          _ = _ := one_mul _
      _ = H.A * E := by
        rw [integral_const_mul, integral_Ioi_one_exp_neg_mul H.p_pos]
  have hlower_int :
      ∫ x : ℝ in Ioc 0 1, ‖F x‖ ≤ H.A * E := by
    have hmajor_full : IntegrableOn
        (fun x : ℝ ↦ H.A * (x ^ (-2 : ℝ) * exp (-(H.p / x)))) (Ioi 0) := by
      simpa [IntegrableOn] using
        (integrableOn_Ioi_zero_inv_rpow_mul_exp_neg_mul 0 H.p_pos).const_mul H.A
    have hmajor_int : IntegrableOn
        (fun x : ℝ ↦ H.A * (x ^ (-2 : ℝ) * exp (-(H.p / x)))) (Ioc 0 1) :=
      IntegrableOn.mono_set hmajor_full Ioc_subset_Ioi_self
    have hFnorm_int : IntegrableOn (fun x : ℝ ↦ ‖F x‖) (Ioc 0 1) :=
      IntegrableOn.mono_set hFnorm_full Ioc_subset_Ioi_self
    calc
      ∫ x : ℝ in Ioc 0 1, ‖F x‖ ≤
          ∫ x : ℝ in Ioc 0 1, H.A * (x ^ (-2 : ℝ) * exp (-(H.p / x))) := by
        apply setIntegral_mono_on hFnorm_int hmajor_int measurableSet_Ioc
        intro x hx
        rw [hFnorm x hx.1]
        calc
          x ^ (s.re - 1) * ‖f x‖ ≤
              x ^ (s.re - 1) *
                (H.A * x ^ (-H.k) * exp (-(H.p / x))) :=
            mul_le_mul_of_nonneg_left (H.lower x hx.1 hx.2)
              (Real.rpow_nonneg hx.1.le _)
          _ = H.A * (x ^ (s.re - 1 - H.k) * exp (-(H.p / x))) := by
            calc
              x ^ (s.re - 1) * (H.A * x ^ (-H.k) * exp (-(H.p / x))) =
                  H.A * ((x ^ (s.re - 1) * x ^ (-H.k)) * exp (-(H.p / x))) := by ring
              _ = H.A * (x ^ (s.re - 1 - H.k) * exp (-(H.p / x))) := by
                rw [← Real.rpow_add hx.1]
                ring_nf
          _ ≤ H.A * (x ^ (-2 : ℝ) * exp (-(H.p / x))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hlower)
                (Real.exp_nonneg _)) H.A_nonneg
      _ = H.A * E := by
        rw [integral_const_mul, integral_Ioc_zero_one_inv_sq_exp H.p_pos]
  calc
    ‖mellin f s‖ = ‖∫ x : ℝ in Ioi 0, F x‖ := rfl
    _ ≤ ∫ x : ℝ in Ioi 0, ‖F x‖ := norm_integral_le_integral_norm _
    _ = (∫ x : ℝ in Ioc 0 1, ‖F x‖) + ∫ x : ℝ in Ioi 1, ‖F x‖ := by
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
      · exact IntegrableOn.mono_set hFnorm_full Ioc_subset_Ioi_self
      · exact IntegrableOn.mono_set hFnorm_full (Ioi_subset_Ioi zero_lt_one.le)
    _ ≤ H.A * E + H.A * E := add_le_add hlower_int hupper_int
    _ = 2 * H.A * (exp (-H.p) / H.p) := by dsimp [E]; ring

end AngularMaster
