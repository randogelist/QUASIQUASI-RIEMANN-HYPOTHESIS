import Merger02.Actual

namespace Merger02
open Complex Filter
open scoped Topology

/-- Branch independence at a squared argument, derived from evenness. -/
theorem theta_sq (w : ℂ) : theta (w ^ 2) = centeredXi w := by
  have hs : (Complex.sqrt (w ^ 2)) ^ 2 = w ^ 2 := by
    simpa only [Complex.sqrt, Nat.cast_ofNat] using
      Complex.cpow_nat_inv_pow (w ^ 2) (by norm_num : (2 : ℕ) ≠ 0)
  have hp : (Complex.sqrt (w ^ 2) - w) * (Complex.sqrt (w ^ 2) + w) = 0 := by
    calc
      _ = (Complex.sqrt (w ^ 2)) ^ 2 - w ^ 2 := by ring
      _ = 0 := by rw [hs]; ring
  rcases mul_eq_zero.mp hp with h | h
  · simp only [theta, sub_eq_zero.mp h]
  · have he : Complex.sqrt (w ^ 2) = -w := eq_neg_of_add_eq_zero_left h
    simpa only [theta, he] using centeredXi_even w

/-- The actual zeta zero is also an actual xi zero. No free zero-binding field. -/
theorem actualXi_zero_of_nontrivialZero {rho : ℂ} (hz : NontrivialZero rho) :
    actualXi rho = 0 := by
  have hgam : Complex.Gamma (rho / 2 + 1) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    apply hz.2.1
    refine ⟨n, ?_⟩
    have he : rho / 2 = -(n : ℂ) - 1 := (eq_sub_iff_add_eq).2 hn
    calc
      rho = 2 * (rho / 2) := by ring
      _ = -2 * ((n : ℂ) + 1) := by rw [he]; ring
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpower : (Real.pi : ℂ) ^ (-rho / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _
  have hden : 2 * (Real.pi : ℂ) ^ (-rho / 2) * Complex.Gamma (rho / 2 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpower) hgam
  have hzeta := hz.1
  rw [riemannZeta_eq_mul_completedRiemannZeta₀] at hzeta
  have hnum : rho * completedRiemannZeta₀ rho - 1 - rho / (1 - rho) = 0 := by
    rcases div_eq_zero_iff.mp hzeta with h | h
    · exact h
    · exact (hden h).elim
  have hd : (1 : ℂ) - rho ≠ 0 := sub_ne_zero.mpr (Ne.symm hz.2.2)
  have hid : (rho * completedRiemannZeta₀ rho - 1 - rho / (1 - rho)) * (1 - rho) =
      -(1 + rho * (rho - 1) * completedRiemannZeta₀ rho) := by
    field_simp [hd]
    ring
  rw [hnum, zero_mul] at hid
  have hraw : 1 + rho * (rho - 1) * completedRiemannZeta₀ rho = 0 :=
    neg_eq_zero.mp hid.symm
  simp only [actualXi, hraw, zero_div]

theorem theta_zero_of_nontrivialZero {rho : ℂ} (hz : NontrivialZero rho) :
    theta ((rho - (1 / 2 : ℂ)) ^ 2) = 0 := by
  rw [theta_sq]
  change actualXi ((1 / 2 : ℂ) + (rho - (1 / 2 : ℂ))) = 0
  rw [show (1 / 2 : ℂ) + (rho - (1 / 2 : ℂ)) = rho by ring]
  exact actualXi_zero_of_nontrivialZero hz

noncomputable def mobius (z v : ℂ) : ℂ := (1 - z * v) / (1 - v)

theorem one_sub_ne_zero_of_norm_lt_one {v : ℂ} (hv : ‖v‖ < 1) : 1 - v ≠ 0 := by
  intro h
  have he : v = 1 := (sub_eq_zero.mp h).symm
  simpa [he] using hv

@[simp] theorem mobius_zero (z : ℂ) : mobius z 0 = 1 := by simp [mobius]

theorem mobius_balance (z v : ℂ) (hv : v ≠ 1) :
    mobius z v - 1 = v * (mobius z v - z) := by
  have hd : (1 : ℂ) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  unfold mobius
  field_simp [hd]
  ring

/-- The whole strict v-disk stays in the actual theta's analytic domain. -/
theorem mobius_mem_slitPlane {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ < 1) :
    mobius z v ∈ Complex.slitPlane := by
  have hne : v ≠ 1 := by intro h; simpa [h] using hv
  let u := mobius z v
  have heq : u - 1 = v * (u - z) := mobius_balance z v hne
  by_contra h
  change u ∉ Complex.slitPlane at h
  rw [Complex.mem_slitPlane_iff] at h
  push_neg at h
  rcases h with ⟨hre, him⟩
  let a : ℝ := -u.re
  have ha : 0 ≤ a := neg_nonneg.mpr hre
  have hu : u = -(a : ℂ) := by
    apply Complex.ext
    · simp [a]
    · simp [him]
  have hnorm : ‖u‖ = a := by
    rw [hu, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hnorm1 : ‖u - 1‖ = a + 1 := by
    have he : u - 1 = -((a + 1 : ℝ) : ℂ) := by rw [hu]; push_cast; ring
    rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ a + 1)]
  have hbound : a + 1 ≤ ‖v‖ * (a + 1) := by
    calc
      a + 1 = ‖u - 1‖ := hnorm1.symm
      _ = ‖v‖ * ‖u - z‖ := by rw [heq, norm_mul]
      _ ≤ ‖v‖ * (‖u‖ + ‖z‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le u z) (norm_nonneg v)
      _ ≤ ‖v‖ * (a + 1) := by rw [hnorm]; gcongr
  nlinarith

theorem mobius_analyticAt (z : ℂ) {v : ℂ} (hv : ‖v‖ < 1) :
    AnalyticAt ℂ (mobius z) v := by
  unfold mobius
  exact (analyticAt_const.fun_sub (analyticAt_const.fun_mul analyticAt_id)).fun_div
    (analyticAt_const.fun_sub analyticAt_id) (one_sub_ne_zero_of_norm_lt_one hv)

theorem mobius_hasDerivAt (z : ℂ) {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (mobius z) ((1 - z) / (1 - v) ^ 2) v := by
  have hd := ((hasDerivAt_const v (1 : ℂ)).sub ((hasDerivAt_id v).const_mul z)).div
    ((hasDerivAt_const v (1 : ℂ)).sub (hasDerivAt_id v))
    (one_sub_ne_zero_of_norm_lt_one hv)
  change HasDerivAt (fun w : ℂ => (1 - z * w) / (1 - w))
    (((0 - z * 1) * (1 - v) - (1 - z * v) * (0 - 1)) / (1 - v) ^ 2) v at hd
  have hnum : (0 - z * 1) * (1 - v) - (1 - z * v) * (0 - 1) = 1 - z := by
    ring
  rw [hnum] at hd
  exact hd

noncomputable def thetaMobius (z v : ℂ) : ℂ := theta (mobius z v)

theorem thetaMobius_analyticOnDisk {z : ℂ} (hz : ‖z‖ ≤ 1) :
    AnalyticOnNhd ℂ (thetaMobius z) (Metric.ball 0 1) := by
  intro v hv
  have hv' : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hv
  exact (theta_analyticOnSlit _ (mobius_mem_slitPlane hz hv')).comp
    (mobius_analyticAt z hv')

@[simp] theorem thetaMobius_zero (z : ℂ) : thetaMobius z 0 = theta 1 := by
  simp [thetaMobius]

theorem thetaMobius_zero_ne_zero (z : ℂ) : thetaMobius z 0 ≠ 0 := by
  simpa using theta_one_ne_zero

/-- A zero of the actual composed denominator has a finite positive order. -/
theorem thetaMobius_zero_finite_order {z v : ℂ}
    (hz : ‖z‖ ≤ 1) (hv : v ∈ Metric.ball (0 : ℂ) 1)
    (hzero : thetaMobius z v = 0) :
    ∃ (m : ℕ) (h : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ h v ∧ h v ≠ 0 ∧
      ∀ᶠ w in 𝓝 v, thetaMobius z w = (w - v) ^ m * h w := by
  have hF := thetaMobius_analyticOnDisk hz
  have hnot : ¬ ∀ᶠ w in 𝓝 v, thetaMobius z w = 0 := by
    intro he
    have hall := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected hv he
    exact thetaMobius_zero_ne_zero z (hall (by simp))
  obtain ⟨m, h, hh, hn, he⟩ :=
    (hF v hv).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    have he0 : thetaMobius z v = (v - v) ^ m • h v :=
      Filter.Eventually.self_of_nhds
        (x := v)
        (p := fun w : ℂ => thetaMobius z w = (w - v) ^ m • h w) he
    simp only [hm0, pow_zero, one_smul, hzero] at he0
    exact hn he0.symm
  exact ⟨m, h, hm, hh, hn, by simpa only [smul_eq_mul] using he⟩

/-- This is the meromorphic formula, not an asserted all-disk power-series sum.
Its totalized value at zero is irrelevant to the meromorphic germ. -/
noncomputable def rawGenerating (z v : ℂ) : ℂ :=
  (g (mobius z v) - g 1) / ((1 - z) * v)

theorem g_meromorphicAt_slit {u : ℂ} (hu : u ∈ Complex.slitPlane) :
    MeromorphicAt g u := by
  have htheta := theta_analyticOnSlit u hu
  unfold g
  exact (analyticAt_id.fun_mul htheta.deriv).meromorphicAt.fun_div
    htheta.meromorphicAt

theorem rawGenerating_meromorphicOnDisk {z : ℂ} (hz : ‖z‖ ≤ 1) :
    MeromorphicOn (rawGenerating z) (Metric.ball 0 1) := by
  intro v hv
  have hv' : ‖v‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hv
  have hcomp : MeromorphicAt (fun w => g (mobius z w)) v :=
    (g_meromorphicAt_slit (mobius_mem_slitPlane hz hv')).comp_analyticAt
      (mobius_analyticAt z hv')
  unfold rawGenerating
  exact (hcomp.fun_sub (MeromorphicAt.const (g 1) v)).fun_div
    (analyticAt_const.fun_mul analyticAt_id).meromorphicAt

/-- A denominator zero is transported exactly to the selected finite pole location. -/
theorem mobius_at_pole (t z : ℂ) (hzt : z + t ≠ 0) (hz : z ≠ 1) :
    mobius z ((1 + t) / (z + t)) = -t := by
  have hden : (1 : ℂ) - (1 + t) / (z + t) ≠ 0 := by
    intro h
    have he : (1 + t) / (z + t) = 1 := (sub_eq_zero.mp h).symm
    have he' := (div_eq_one_iff_eq hzt).mp he
    apply hz
    linear_combination -he'
  unfold mobius
  apply (div_eq_iff hden).2
  field_simp [hzt] <;> ring

end Merger02
