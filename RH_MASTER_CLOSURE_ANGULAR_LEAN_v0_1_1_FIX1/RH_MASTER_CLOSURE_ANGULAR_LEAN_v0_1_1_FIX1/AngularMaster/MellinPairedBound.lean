import AngularMaster.MellinEndpointBound

/-! A paired Mellin estimate preserving both endpoint weights on the strip. -/

noncomputable section
open MeasureTheory Set Real OverflowResidueRH

namespace AngularMaster

theorem rpow_paired_endpoint_le {x t : ℝ} (hx : 1 ≤ x)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    x ^ (t - 1) + x ^ (-t - 1 / 2) ≤ x ^ (-1 : ℝ) + x ^ (-1 / 2 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hu : 1 ≤ x ^ t := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx ht0
  have hv : 1 ≤ x ^ (1 / 2 - t) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show 0 ≤ 1 / 2 - t by linarith)
  have huv : x ^ t * x ^ (1 / 2 - t) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hsum : x ^ t + x ^ (1 / 2 - t) ≤ 1 + x ^ (1 / 2 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
  have h := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hx0.le (-1))
  have heq1 : x ^ (-1 : ℝ) * x ^ t = x ^ (t - 1) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have heq2 : x ^ (-1 : ℝ) * x ^ (1 / 2 - t) = x ^ (-t - 1 / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have heq3 : x ^ (-1 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  simpa only [mul_add, mul_one, heq1, heq2, heq3] using h

private theorem integral_inverse_tail (p q : ℝ) :
    (∫ x : ℝ in Ioc 0 1, x ^ (-q - 2) * exp (-(p / x))) =
      ∫ x : ℝ in Ioi 1, x ^ q * exp (-(p * x)) := by
  let g : ℝ → ℝ := (Ioi 1).indicator (fun y => y ^ q * exp (-(p * y)))
  have hsub := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
  have heq :
      (∫ x : ℝ in Ioi 0, (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        ∫ x : ℝ in Ioi 0,
          (Iio 1).indicator (fun x => x ^ (-q - 2) * exp (-(p / x))) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := hx
    have hi : x ^ (-1 : ℝ) ∈ Ioi (1 : ℝ) ↔ x ∈ Iio (1 : ℝ) := by
      simpa only [Real.rpow_neg_one, mem_Ioi, mem_Iio] using one_lt_inv₀ hx0
    by_cases hx1 : x < 1
    · have hxmem : x ∈ Iio (1 : ℝ) := hx1
      simp only [g, indicator_of_mem (hi.mpr hxmem), indicator_of_mem hxmem,
        abs_neg, abs_one, one_mul, smul_eq_mul]
      rw [← Real.rpow_mul hx0.le, ← mul_assoc, ← Real.rpow_add hx0,
        Real.rpow_neg_one]
      congr 2
      · ring
    · have hxmem : x ∉ Iio (1 : ℝ) := hx1
      simp only [g, indicator_of_notMem (fun h => hxmem (hi.mp h)),
        indicator_of_notMem hxmem, smul_zero]
  rw [heq, setIntegral_indicator measurableSet_Iio] at hsub
  have hleft : Ioi (0 : ℝ) ∩ Iio 1 = Ioo 0 1 := by ext x; simp
  rw [hleft] at hsub
  have hright : (∫ y : ℝ in Ioi 0, g y) =
      ∫ y : ℝ in Ioi 1, y ^ q * exp (-(p * y)) := by
    dsimp only [g]
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  rw [hright] at hsub
  rw [integral_Ioc_eq_integral_Ioo, hsub]

/-- Pairing the upper and inverted lower tails before estimating their powers
retains the sharper sum `x⁻¹ + x⁻¹ᐟ²` throughout the central Mellin strip. -/
theorem norm_mellin_le_paired_endpoint
    {f : ℝ → ℂ} (H : MellinTwoSidedExponentialDecay f) (hk : H.k = 1 / 2)
    (s : ℂ) (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1 / 2)
    (hconv : MellinConvergent f s) :
    ‖mellin f s‖ ≤ H.A *
      ∫ x : ℝ in Ioi 1, (x ^ (-1 : ℝ) + x ^ (-1 / 2 : ℝ)) * exp (-(H.p * x)) := by
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) • f x
  have hF_int : IntegrableOn F (Ioi 0) := by
    simpa only [F, MellinConvergent] using hconv
  have hFnorm_full : IntegrableOn (fun x : ℝ => ‖F x‖) (Ioi 0) := hF_int.norm
  have hFnorm (x : ℝ) (hx : 0 < x) :
      ‖F x‖ = x ^ (s.re - 1) * ‖f x‖ := by
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hInt (q : ℝ) (hq : q ≤ 0) :
      IntegrableOn (fun x : ℝ => x ^ q * exp (-(H.p * x))) (Ioi 1) :=
    integrableOn_Ioi_one_rpow_mul_exp_neg_mul_of_le_nat 0 H.p_pos (by simpa using hq)
  have huInt := hInt (s.re - 1) (by linarith)
  have hvInt := hInt (-s.re - 1 / 2) (by linarith)
  have hlInt : IntegrableOn
      (fun x : ℝ => x ^ (s.re - 3 / 2) * exp (-(H.p / x))) (Ioc 0 1) := by
    have hbase := (integrableOn_Ioi_zero_inv_rpow_mul_exp_neg_mul 0 H.p_pos).mono_set
      (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)
    refine hbase.mono_nonneg ?_ ?_ ?_
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (exp_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by norm_num; linarith))
        (exp_nonneg _)
  have hupper : (∫ x : ℝ in Ioi 1, ‖F x‖) ≤ H.A *
      ∫ x : ℝ in Ioi 1, x ^ (s.re - 1) * exp (-(H.p * x)) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      (hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one))
      (huInt.const_mul H.A) measurableSet_Ioi
    intro x hx
    rw [hFnorm x (zero_lt_one.trans hx)]
    calc
      _ ≤ x ^ (s.re - 1) * (H.A * exp (-(H.p * x))) :=
        mul_le_mul_of_nonneg_left (H.upper x hx.le)
          (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
      _ = _ := by ring
  have hlower : (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤ H.A *
      ∫ x : ℝ in Ioi 1, x ^ (-s.re - 1 / 2) * exp (-(H.p * x)) := by
    have hlow : (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤ H.A *
        ∫ x : ℝ in Ioc 0 1, x ^ (s.re - 3 / 2) * exp (-(H.p / x)) := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on
        (hFnorm_full.mono_set Ioc_subset_Ioi_self)
        (hlInt.const_mul H.A) measurableSet_Ioc
      intro x hx
      rw [hFnorm x hx.1]
      calc
        _ ≤ x ^ (s.re - 1) * (H.A * x ^ (-H.k) * exp (-(H.p / x))) :=
          mul_le_mul_of_nonneg_left (H.lower x hx.1 hx.2) (Real.rpow_nonneg hx.1.le _)
        _ = H.A * ((x ^ (s.re - 1) * x ^ (-H.k)) * exp (-(H.p / x))) := by ring
        _ = _ := by rw [← Real.rpow_add hx.1, hk]; congr 3; ring
    have hid := integral_inverse_tail H.p (-s.re - 1 / 2)
    convert hlow using 1
    rw [← hid]
    congr 2
    funext x
    congr 2
    ring
  have hpaired :
      (∫ x : ℝ in Ioi 1, x ^ (s.re - 1) * exp (-(H.p * x))) +
      (∫ x : ℝ in Ioi 1, x ^ (-s.re - 1 / 2) * exp (-(H.p * x))) ≤
      ∫ x : ℝ in Ioi 1, (x ^ (-1 : ℝ) + x ^ (-1 / 2 : ℝ)) * exp (-(H.p * x)) := by
    rw [← integral_add huInt hvInt]
    have heInt := (hInt (-1) (by norm_num)).add (hInt (-1 / 2) (by norm_num))
    have heInt' : IntegrableOn
        (fun x : ℝ => (x ^ (-1 : ℝ) + x ^ (-1 / 2 : ℝ)) * exp (-(H.p * x))) (Ioi 1) := by
      simpa only [Pi.add_def, add_mul] using heInt
    apply setIntegral_mono_on (huInt.add hvInt) heInt' measurableSet_Ioi
    intro x hx
    simp only [Pi.add_apply]
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (rpow_paired_endpoint_le hx.le hs0 hs1) (exp_nonneg _)
  calc
    ‖mellin f s‖ = ‖∫ x : ℝ in Ioi 0, F x‖ := rfl
    _ ≤ ∫ x : ℝ in Ioi 0, ‖F x‖ := norm_integral_le_integral_norm _
    _ = (∫ x : ℝ in Ioc 0 1, ‖F x‖) + ∫ x : ℝ in Ioi 1, ‖F x‖ := by
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
      · exact hFnorm_full.mono_set Ioc_subset_Ioi_self
      · exact hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one)
    _ ≤ H.A * (∫ x : ℝ in Ioi 1, x ^ (-s.re - 1 / 2) * exp (-(H.p * x))) +
        H.A * (∫ x : ℝ in Ioi 1, x ^ (s.re - 1) * exp (-(H.p * x))) :=
      add_le_add hlower hupper
    _ = H.A * ((∫ x : ℝ in Ioi 1, x ^ (s.re - 1) * exp (-(H.p * x))) +
        (∫ x : ℝ in Ioi 1, x ^ (-s.re - 1 / 2) * exp (-(H.p * x)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpaired H.A_nonneg

end AngularMaster
