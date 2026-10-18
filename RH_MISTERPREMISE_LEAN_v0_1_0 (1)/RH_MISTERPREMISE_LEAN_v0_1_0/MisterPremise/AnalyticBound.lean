import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

open Set Filter
open scoped Topology

namespace MisterPremise

/-- The endpoint singularity of the weighted logarithmic derivative is removable. -/
theorem weighted_logDeriv_tendsto_of_analyticAt
    {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a)
    (hne : ¬ ∀ᶠ x in 𝓝 a, f x = 0) :
    ∃ n : ℕ, Tendsto (fun x => (x - a) * logDeriv f x)
      (𝓝[≠] a) (𝓝 (n : ℝ)) := by
  obtain ⟨n, g, hg, hga, hfg⟩ :=
    hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hfg' : f =ᶠ[𝓝 a] fun x => (x - a) ^ n * g x := by
    filter_upwards [hfg] with x hx
    simpa only [smul_eq_mul] using hx
  have hlog := logDeriv_congr_nhds hfg'
  have hcont : ContinuousAt (fun x => (n : ℝ) + (x - a) * logDeriv g x) a :=
    continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul
      (hg.deriv.continuousAt.div hg.continuousAt hga))
  refine ⟨n, ?_⟩
  have heq : (fun x => (x - a) * logDeriv f x) =ᶠ[𝓝[≠] a]
      (fun x => (n : ℝ) + (x - a) * logDeriv g x) := by
    filter_upwards [hlog.filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (hg.continuousAt.eventually_ne hga).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with x hx hga' hgx hxa
    have hxa' : x - a ≠ 0 := sub_ne_zero.mpr hxa
    rw [hx, logDeriv_mul (f := fun z : ℝ => (z - a) ^ n) (g := g)
      x (pow_ne_zero _ hxa') hgx (by fun_prop)
      hga'.differentiableAt, logDeriv_fun_pow (by fun_prop)]
    have hsub : logDeriv (fun z : ℝ => z - a) x = 1 / (x - a) := by
      simp [logDeriv_apply]
    rw [hsub]
    field_simp
  apply Tendsto.congr' heq.symm
  simpa only [sub_self, zero_mul, add_zero] using
    hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Positivity on a half-open interval makes the endpoint-weighted logarithmic
derivative bounded above, even when the function vanishes at the left endpoint. -/
theorem exists_pos_weighted_deriv_le
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : AnalyticOnNhd ℝ f (Icc a b))
    (hpos : ∀ x ∈ Ioc a b, 0 < f x) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Ioc a b,
      (x - a) * deriv f x ≤ M * f x := by
  classical
  have hne : ¬ ∀ᶠ x in 𝓝 a, f x = 0 := by
    intro hz
    let : NeBot (𝓝[Ioc a b] a) := left_nhdsWithin_Ioc_neBot hab
    have hmem : ∀ᶠ x in 𝓝[Ioc a b] a, x ∈ Ioc a b := self_mem_nhdsWithin
    obtain ⟨x, hx, hzx⟩ :=
      (hmem.and (hz.filter_mono nhdsWithin_le_nhds)).exists
    exact (ne_of_gt (hpos x hx)) hzx
  obtain ⟨n, hn⟩ := weighted_logDeriv_tendsto_of_analyticAt
    (hf a ⟨le_rfl, hab.le⟩) hne
  let q : ℝ → ℝ := fun x => (x - a) * logDeriv f x
  let Q : ℝ → ℝ := Function.update q a (n : ℝ)
  have hQ : ContinuousOn Q (Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    by_cases hxa : x = a
    · subst x
      exact continuousAt_update_same.mpr hn
    · apply (continuousAt_update_of_ne hxa).mpr
      have hpx : 0 < f x := hpos x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩
      exact (continuousAt_id.sub continuousAt_const).mul
        ((hf x hx).deriv.continuousAt.div (hf x hx).continuousAt hpx.ne')
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hQ
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  have hxne : x ≠ a := ne_of_gt hx.1
  have hqx : q x ≤ C := by
    have h := hC (mem_image_of_mem Q ⟨hx.1.le, hx.2⟩)
    simpa only [Q, Function.update_of_ne hxne] using h
  have hbound : (x - a) * deriv f x / f x ≤ max 1 C := by
    simpa only [q, logDeriv_apply, mul_div_assoc] using
      hqx.trans (le_max_right 1 C)
  exact (div_le_iff₀ (hpos x hx)).mp hbound

/-- An analytic nonnegative monotone function admits the same upper bound
wherever it is positive; the identically-zero alternative is vacuous. -/
theorem exists_pos_weighted_deriv_le_of_nonneg_monotone
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : AnalyticOnNhd ℝ f (Icc a b))
    (hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hmono : MonotoneOn f (Icc a b)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Ioc a b, 0 < f x →
      (x - a) * deriv f x ≤ M * f x := by
  classical
  by_cases hpos : ∀ x ∈ Ioc a b, 0 < f x
  · obtain ⟨M, hM, hbound⟩ := exists_pos_weighted_deriv_le hab hf hpos
    exact ⟨M, hM, fun x hx _ => hbound x hx⟩
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp hpos
    obtain ⟨hx₀mem, hx₀not⟩ := Classical.not_imp.mp hx₀
    have hx₀Icc : x₀ ∈ Icc a b := ⟨hx₀mem.1.le, hx₀mem.2⟩
    have hxzero : f x₀ = 0 :=
      le_antisymm (le_of_not_gt hx₀not) (hnonneg x₀ hx₀Icc)
    obtain ⟨c, hac, hcx₀⟩ := exists_between hx₀mem.1
    have hlocal : f =ᶠ[𝓝 c] 0 := by
      filter_upwards [Ioo_mem_nhds hac hcx₀] with y hy
      have hyIcc : y ∈ Icc a b := ⟨hy.1.le, hy.2.le.trans hx₀mem.2⟩
      exact le_antisymm
        ((hmono hyIcc hx₀Icc hy.2.le).trans_eq hxzero) (hnonneg y hyIcc)
    have hzero : EqOn f 0 (Icc a b) :=
      hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Icc
        ⟨hac.le, hcx₀.le.trans hx₀mem.2⟩ hlocal
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hpx
    have hz : f x = 0 := hzero ⟨hx.1.le, hx.2⟩
    exact False.elim ((ne_of_gt hpx) hz)

end MisterPremise
