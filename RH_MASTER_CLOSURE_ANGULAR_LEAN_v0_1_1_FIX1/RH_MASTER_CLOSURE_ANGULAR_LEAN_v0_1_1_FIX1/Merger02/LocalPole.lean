import Merger02.ActualPoleLocation

/-!
A finite-order denominator zero gives a genuine simple pole of the actual
logarithmic derivative. Multiplicity is retained, not assumed to equal one.
-/
namespace Merger02
open Complex Filter
open scoped Topology

/-- Local factorization gives the exact logarithmic-derivative principal part. -/
theorem logDeriv_local_factor {f h : ℂ → ℂ} {v : ℂ} {m : ℕ}
    (hh : AnalyticAt ℂ h v) (hn : h v ≠ 0)
    (he : ∀ᶠ u in 𝓝 v, f u = (u - v) ^ m * h u) :
    ∀ᶠ u in 𝓝[≠] v, logDeriv f u = (m : ℂ) / (u - v) + logDeriv h u := by
  have hlog := logDeriv_congr_nhds he
  have han := hh.eventually_analyticAt
  have hne := hh.continuousAt.eventually_ne hn
  filter_upwards [hlog.filter_mono nhdsWithin_le_nhds,
    han.filter_mono nhdsWithin_le_nhds, hne.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with u hlogu hhu hnu huv
  have huv' : u ≠ v := by simpa using huv
  have hsub : DifferentiableAt ℂ (fun a : ℂ => a - v) u := by fun_prop
  have hd : HasDerivAt (fun a : ℂ => a - v) 1 u := by
    simpa using (hasDerivAt_id u).sub_const v
  have hpow_ne : (u - v) ^ m ≠ 0 :=
    pow_ne_zero m (sub_ne_zero.mpr huv')
  have hmul :
      logDeriv (fun a : ℂ => (a - v) ^ m * h a) u =
        logDeriv (fun a : ℂ => (a - v) ^ m) u + logDeriv h u :=
    logDeriv_mul (f := fun a : ℂ => (a - v) ^ m) (g := h)
      u hpow_ne hnu (hsub.pow m) hhu.differentiableAt
  have hpow :
      logDeriv (fun a : ℂ => (a - v) ^ m) u =
        (m : ℂ) * logDeriv (fun a : ℂ => a - v) u :=
    logDeriv_fun_pow (f := fun a : ℂ => a - v) (x := u) hsub m
  have hld : logDeriv (fun a : ℂ => a - v) u = 1 / (u - v) := by
    rw [logDeriv_apply, hd.deriv]
  calc
    logDeriv f u =
        logDeriv (fun a : ℂ => (a - v) ^ m * h a) u := hlogu
    _ = logDeriv (fun a : ℂ => (a - v) ^ m) u + logDeriv h u := hmul
    _ = (m : ℂ) / (u - v) + logDeriv h u := by
      rw [hpow, hld, mul_one_div]

noncomputable def poleMultiplier (z v : ℂ) : ℂ :=
  (1 - z * v) * (1 - v) / ((1 - z) ^ 2 * v)

noncomputable def poleOffset (z v : ℂ) : ℂ := -g 1 / ((1 - z) * v)

theorem poleMultiplier_analyticAt {z v : ℂ} (hz : z ≠ 1) (hv : v ≠ 0) :
    AnalyticAt ℂ (poleMultiplier z) v := by
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold poleMultiplier
  exact ((analyticAt_const.fun_sub (analyticAt_const.fun_mul analyticAt_id)).fun_mul
    (analyticAt_const.fun_sub analyticAt_id)).fun_div
    (analyticAt_const.fun_mul analyticAt_id) (mul_ne_zero (pow_ne_zero 2 hz') hv)

theorem poleOffset_analyticAt {z v : ℂ} (hz : z ≠ 1) (hv : v ≠ 0) :
    AnalyticAt ℂ (poleOffset z) v := by
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold poleOffset
  exact analyticAt_const.fun_div (analyticAt_const.fun_mul analyticAt_id)
    (mul_ne_zero hz' hv)

theorem poleMultiplier_ne_zero {z v : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1)
    (hv : ‖v‖ < 1) (hv0 : v ≠ 0) : poleMultiplier z v ≠ 0 := by
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hzv : ‖z * v‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hz (norm_nonneg v)).trans_lt (by simpa using hv)
  exact div_ne_zero
    (mul_ne_zero (one_sub_ne_zero_of_norm_lt_one hzv)
      (one_sub_ne_zero_of_norm_lt_one hv))
    (mul_ne_zero (pow_ne_zero 2 hz') hv0)

/-- Chain rule in the actual meromorphic formula, away from denominator zeros. -/
theorem rawGenerating_logDeriv_formula {z v : ℂ}
    (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (hv : ‖v‖ < 1) (hv0 : v ≠ 0)
    (hden : thetaMobius z v ≠ 0) :
    rawGenerating z v = poleMultiplier z v * logDeriv (thetaMobius z) v + poleOffset z v := by
  have hu := theta_analyticOnSlit _ (mobius_mem_slitPlane hz hv)
  have hd := (hu.differentiableAt.hasDerivAt).comp v (mobius_hasDerivAt z hv)
  have hd' : deriv (thetaMobius z) v =
      deriv theta (mobius z v) * ((1 - z) / (1 - v) ^ 2) := by
    exact hd.deriv
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hv' := one_sub_ne_zero_of_norm_lt_one hv
  have ht : theta (mobius z v) ≠ 0 := hden
  unfold rawGenerating poleMultiplier poleOffset
  rw [logDeriv_apply, hd']
  rw [show g (mobius z v) = mobius z v * deriv theta (mobius z v) /
    theta (mobius z v) by rfl]
  unfold thetaMobius mobius
  change theta ((1 - z * v) / (1 - v)) ≠ 0 at ht
  field_simp [hz', hv', hv0, ht] <;> ring

/-- Explicit local analytic remainder at a zero of the actual composed denominator. -/
theorem rawGenerating_simple_pole {z v : ℂ} {m : ℕ} {h : ℂ → ℂ}
    (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (hv : ‖v‖ < 1) (hv0 : v ≠ 0)
    (hm : 0 < m) (hh : AnalyticAt ℂ h v) (hn : h v ≠ 0)
    (he : ∀ᶠ u in 𝓝 v, thetaMobius z u = (u - v) ^ m * h u) :
    ∃ (A : ℂ) (R : ℂ → ℂ), A ≠ 0 ∧ AnalyticAt ℂ R v ∧
      ∀ᶠ u in 𝓝[≠] v, rawGenerating z u = A / (u - v) + R u := by
  let a := poleMultiplier z
  let A : ℂ := (m : ℂ) * a v
  let R : ℂ → ℂ := fun u => (m : ℂ) * dslope a v u +
    a u * (deriv h u / h u) + poleOffset z u
  have ha : AnalyticAt ℂ a v := poleMultiplier_analyticAt hz1 hv0
  have hds : AnalyticAt ℂ (dslope a v) v := by
    obtain ⟨p, hp⟩ := ha
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hA : A ≠ 0 := mul_ne_zero (by exact_mod_cast hm.ne')
    (poleMultiplier_ne_zero hz hz1 hv hv0)
  have hR : AnalyticAt ℂ R v := by
    exact ((analyticAt_const.fun_mul hds).fun_add
      (ha.fun_mul (hh.deriv.fun_div hh hn))).fun_add (poleOffset_analyticAt hz1 hv0)
  refine ⟨A, R, hA, hR, ?_⟩
  have hlog := logDeriv_local_factor hh hn he
  have hunit := hh.continuousAt.eventually_ne hn
  have hball : ∀ᶠ u in 𝓝 v, ‖u‖ < 1 :=
    (continuous_norm.tendsto v).eventually (gt_mem_nhds hv)
  have hnonzero : ∀ᶠ u in 𝓝 v, u ≠ 0 := eventually_ne_nhds hv0
  filter_upwards [hlog, he.filter_mono nhdsWithin_le_nhds,
    hunit.filter_mono nhdsWithin_le_nhds, hball.filter_mono nhdsWithin_le_nhds,
    hnonzero.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with u hlogu heu hnu hbu h0u huv
  have huv' : u ≠ v := by simpa using huv
  have htu : thetaMobius z u ≠ 0 := by
    rw [heu]
    exact mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr huv')) hnu
  rw [rawGenerating_logDeriv_formula hz hz1 hbu h0u htu, hlogu, logDeriv_apply]
  have hdsu : dslope a v u = (a u - a v) / (u - v) := by
    simp [dslope, slope, huv', div_eq_mul_inv, mul_comm]
  dsimp [A, R]
  rw [hdsu]
  dsimp [a]
  ring

/-- The genuine simple pole is derived from an actual off-line zero. -/
theorem actual_offline_simple_pole {rho : ℂ}
    (hzeta : NontrivialZero rho) (hOff : rho.re ≠ (1 / 2 : ℝ)) :
    ∃ (z v A : ℂ) (R : ℂ → ℂ),
      ‖z‖ = 1 ∧ z ≠ 1 ∧ v ≠ 0 ∧ ‖v‖ < 1 ∧ 1 < ‖v⁻¹‖ ∧
      A ≠ 0 ∧ AnalyticAt ℂ R v ∧
      ∀ᶠ u in 𝓝[≠] v, rawGenerating z u = A / (u - v) + R u := by
  obtain ⟨z, v, m, h, hz, hz1, hv0, hv, hexp, hm, hh, hn, _, he⟩ :=
    actual_offline_positive_order hzeta hOff
  obtain ⟨A, R, hA, hR, hlocal⟩ :=
    rawGenerating_simple_pole hz.le hz1 hv hv0 hm hh hn he
  exact ⟨z, v, A, R, hz, hz1, hv0, hv, hexp, hA, hR, hlocal⟩

end Merger02
