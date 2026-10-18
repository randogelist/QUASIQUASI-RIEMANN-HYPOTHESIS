import AngularMaster.ActualHadamard
import AngularRegularity.Actual
import MisterPremise.AnalyticBound

/-!
# Actual angular regularity for MISTERPREMISE

The ordinary angular slope is smooth in the open angular interval without RH.
Under RH the canonical product supplies a real analytic extension across both
angular endpoints.  Its nonnegativity and monotonicity follow by passing the
corresponding finite product inequalities to the derivative limit.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace MisterPremise

theorem actualAngularSlope_differentiableAt {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (AngularRegularity.actualAngularSlope r) x := by
  have hs : ContDiffAt ℝ ⊤ (AngularRegularity.profile AWPIRH.theta r) x :=
    AngularRegularity.profile_slice_contDiffAt AWPIRH.theta_differentiable hx
  have hd : ContDiffAt ℝ ⊤ (deriv (AngularRegularity.profile AWPIRH.theta r)) x :=
    hs.derivWithin (by simp)
  exact hd.differentiableAt (by simp)

theorem actualAngularSlope_differentiableOn (r : ℝ) :
    DifferentiableOn ℝ (AngularRegularity.actualAngularSlope r) (Ioo (-1 : ℝ) 1) := by
  intro x hx
  exact (actualAngularSlope_differentiableAt hx).differentiableWithinAt

theorem actualProfile_eq_master (r : ℝ) :
    AngularRegularity.actualProfile r = AngularMaster.actualProfile r := rfl

/-- RH supplies an analytic extension of the actual angular slope, with the
nonnegative and monotone properties retained all the way to the endpoints.
The extension is not Lean's totalized ordinary derivative at an endpoint. -/
theorem actualAngularSlope_exists_analytic_extension_of_RH
    (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r) :
    ∃ f : ℝ → ℝ,
      AnalyticOnNhd ℝ f univ ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, f x = AngularRegularity.actualAngularSlope r x) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x) ∧
      MonotoneOn f (Icc (-1 : ℝ) 1) := by
  classical
  obtain ⟨c, hc, hp⟩ := AngularMaster.actualProfile_indexed_product_values hRH
  let α := AngularMaster.actualZeroScale
  let F : ℂ → ℂ := fun z => (c r : ℂ) *
    AngularMaster.complexIndexedAngularProduct (fun i => 1 / α i) r z
  have hα : ∀ i, 0 < α i := AngularMaster.actualZeroScale_positive
  have hs : Summable (fun i => 1 / α i) := by
    simpa only [one_div] using AngularMaster.actualZeroScale_inv_summable
  have hlim : TendstoLocallyUniformlyOn
      (fun s z => (c r : ℂ) * AngularMaster.indexedComplexFiniteProductProfile α r s z)
      F atTop univ := by
    have h := AngularMaster.scaled_indexedComplexProfile_tendstoLocallyUniformlyOn
      (fun i => le_of_lt (one_div_pos.mpr (hα i))) hs hr.le (c r)
    simpa only [AngularMaster.indexedComplexFiniteProductProfile_eq_reciprocal] using h
  have hpoly : ∀ᶠ s : Finset AngularMaster.ActualPairIndex in atTop,
      DifferentiableOn ℂ
        (fun z => (c r : ℂ) * AngularMaster.indexedComplexFiniteProductProfile α r s z)
        univ :=
    Eventually.of_forall (fun s =>
      ((AngularMaster.indexedComplexFiniteProductProfile_differentiable α r s).const_mul
        (c r)).differentiableOn)
  have hF : Differentiable ℂ F :=
    differentiableOn_univ.mp (hlim.differentiableOn hpoly isOpen_univ)
  have hagree : ∀ x ∈ Icc (-1 : ℝ) 1, (F (x : ℂ)).re = AngularMaster.actualProfile r x := by
    intro x hx
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (hlim.tendsto_at (mem_univ (x : ℂ)))
    have h' : Tendsto (fun s => c r * AngularMaster.indexedFiniteProductProfile α r s x)
        atTop (𝓝 (F (x : ℂ)).re) := by
      simpa only [Function.comp_def,
        AngularMaster.indexedComplexFiniteProductProfile_ofReal,
        ← Complex.ofReal_mul, Complex.ofReal_re] using h
    exact tendsto_nhds_unique h' (hp r hr x hx)
  let f : ℝ → ℝ := fun x => (deriv F (x : ℂ)).re
  have hderiv : ∀ x : ℝ,
      Tendsto (fun s => c r * AngularMaster.indexedFiniteProductFlux α r s x)
        atTop (𝓝 (f x)) := by
    intro x
    have hd := (hlim.deriv hpoly isOpen_univ).tendsto_at (mem_univ (x : ℂ))
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hd
    change Tendsto (fun s =>
      (deriv (fun z => (c r : ℂ) *
        AngularMaster.indexedComplexFiniteProductProfile α r s z) (x : ℂ)).re)
      atTop (𝓝 (f x)) at hre
    simpa only [AngularMaster.scaled_indexedComplexFiniteProductProfile_deriv_re] using hre
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact (Complex.reCLM.analyticAt _).comp
      (((hF.deriv.analyticAt (x : ℂ)).restrictScalars (𝕜 := ℝ)).comp
        (Complex.ofRealCLM.analyticAt x))
  · intro x hx
    have heq : (fun y : ℝ => (F (y : ℂ)).re) =ᶠ[𝓝 x]
        AngularRegularity.actualProfile r := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
      exact hagree y hy
    have hd := ((hF (x : ℂ)).hasDerivAt.real_of_complex).congr_of_eventuallyEq heq.symm
    exact hd.deriv.symm
  · intro x hx
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hderiv x)
      (fun s => mul_nonneg (hc r hr)
        (AngularMaster.indexedFiniteProductFlux_nonnegative hα hr hx.1 s))
  · intro x hx y hy hxy
    exact le_of_tendsto_of_tendsto' (hderiv x) (hderiv y)
      (fun s => mul_le_mul_of_nonneg_left
        (AngularMaster.indexedFiniteProductFlux_mono hα hr hx.1 hxy s) (hc r hr))

/-- At any interior right endpoint, RH supplies the finite weighted upper
bound required by MISTERPREMISE.  The bound may depend on the fixed radius. -/
theorem actualAngularSlope_weighted_bound_of_RH
    (hRH : RiemannHypothesis) {r b : ℝ} (hr : 0 < r)
    (hb : -1 < b) (hb1 : b < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Ioc (-1 : ℝ) b,
      0 < AngularRegularity.actualAngularSlope r x →
      (1 + x) * deriv (AngularRegularity.actualAngularSlope r) x ≤
        M * AngularRegularity.actualAngularSlope r x := by
  obtain ⟨f, hf, heq, hn, hm⟩ :=
    actualAngularSlope_exists_analytic_extension_of_RH hRH hr
  have hsub : Icc (-1 : ℝ) b ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hb1.le⟩
  obtain ⟨M, hM, hbound⟩ := exists_pos_weighted_deriv_le_of_nonneg_monotone hb
    (hf.mono (subset_univ _))
    (fun x hx => hn x (hsub hx)) (hm.mono hsub)
  refine ⟨M, hM, ?_⟩
  intro x hx hpos
  have hxi : x ∈ Ioo (-1 : ℝ) 1 := ⟨hx.1, hx.2.trans_lt hb1⟩
  have hfx : f x = AngularRegularity.actualAngularSlope r x := heq x hxi
  have hevent : f =ᶠ[𝓝 x] AngularRegularity.actualAngularSlope r := by
    filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
    exact heq y hy
  have h := hbound x hx (hfx.symm ▸ hpos)
  rw [hevent.deriv_eq, hfx] at h
  simpa only [sub_neg_eq_add, add_comm x 1] using h

end MisterPremise
