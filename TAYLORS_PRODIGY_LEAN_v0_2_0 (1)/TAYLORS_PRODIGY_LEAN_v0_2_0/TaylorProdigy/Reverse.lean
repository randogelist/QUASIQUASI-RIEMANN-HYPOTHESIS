import TaylorProdigy.AngularExtension
import TaylorProdigy.ActualPositivity
import TaylorProdigy.StrictProductSlope
import TaylorProdigy.PositiveExtension
import AngularMaster.ActualHadamard

/-!
# RH implies the unchanged Taylor's Prodigy premise

The actual Hadamard product under RH supplies a smooth positive extension of
its angular derivative through the positive real axis. Its logarithmic decay
rate is locally integrable. The ordinary endpoint value `F r 0` is not used.
An empty divisor index is handled separately by the constant profile.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace TaylorsProdigy

/-- The exact first-order premise follows from native RH. No new research
hypothesis or endpoint derivative assumption is introduced. -/
theorem TAYLORS_PRODIGY_PREMISE_of_native_RH
    (hRH : _root_.RiemannHypothesis) : TAYLORS_PRODIGY_PREMISE := by
  classical
  obtain ⟨c, hc, hprod⟩ := AngularMaster.actualProfile_indexed_product_values hRH
  intro r hr
  let b : AngularMaster.ActualPairIndex → ℝ :=
    fun i => 1 / AngularMaster.actualZeroScale i
  have hα : ∀ i : AngularMaster.ActualPairIndex, 0 < AngularMaster.actualZeroScale i :=
    AngularMaster.actualZeroScale_positive
  have hb : ∀ i, 0 ≤ b i := fun i => (one_div_pos.mpr (hα i)).le
  have hs : Summable b := by
    simpa only [b, one_div] using AngularMaster.actualZeroScale_inv_summable
  let g : ℝ → ℝ := fun θ => c r * angleExtension b r θ
  have hg : ContDiff ℝ ⊤ g :=
    contDiff_const.mul (angleExtension_contDiff hb hs hr.le)
  have heq : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, F r θ = g θ := by
    intro θ hθ
    exact (scaled_angleExtension_eq_F hα hs hr (hprod r hr) hθ).symm
  by_cases hindex : Nonempty AngularMaster.ActualPairIndex
  · let i : AngularMaster.ActualPairIndex := Classical.choice hindex
    let P : ℝ → ℝ := fun x => c r * realProduct b r x
    have hPc : ContDiff ℝ ⊤ P :=
      contDiff_const.mul (realProduct_contDiff hb hs hr.le)
    have hPd : Differentiable ℝ P := hPc.differentiable (by simp)
    have hvalues : ∀ t ∈ Ioi (-1 : ℝ),
        Tendsto (fun s : Finset AngularMaster.ActualPairIndex =>
          c r * ∏ j ∈ s, AngularMaster.genusZeroFactor
            (AngularMaster.actualZeroScale j) r t) atTop (𝓝 (P t)) := by
      intro t _
      simpa only [P, b, AngularMaster.indexedFiniteProductProfile] using
        indexedProductValues_tendsto_realProduct hα hs hr.le (c r) t
    have hpositive : ∀ θ ∈ Ico (0 : ℝ) Real.pi, 0 < g θ := by
      intro θ hθ
      have hx : Real.cos θ ∈ Ioc (-1 : ℝ) 1 := by
        constructor
        · rcases eq_or_lt_of_le hθ.1 with heq0 | hpos
          · rw [← heq0, Real.cos_zero]
            norm_num
          · exact (cos_mem_interior ⟨hpos, hθ.2⟩).1
        · exact Real.cos_le_one θ
      have hPvalue : P (Real.cos θ) = AngularMaster.actualProfile r (Real.cos θ) :=
        scaled_realProduct_eq_actualProfile hα hs hr (hprod r hr) ⟨hx.1.le, hx.2⟩
      have hPpositive : 0 < P (Real.cos θ) := by
        rw [hPvalue]
        exact actualProfile_pos_of_RH hRH hr hx
      have hderivpositive : 0 < deriv P (Real.cos θ) :=
        deriv_pos_of_product_values hα (hc r hr) hr hvalues hx.1
          (hPd _) hPpositive i
      have hderiv : deriv P (Real.cos θ) = g θ := by
        exact ((realProduct_contDiff hb hs hr.le).differentiable (by simp)
          (Real.cos θ)).hasDerivAt.const_mul (c r) |>.deriv
      rw [hderiv] at hderivpositive
      exact hderivpositive
    have hgd : ContDiff ℝ ⊤ (deriv g) := hg.deriv'
    exact relative_decay_rate_of_positive_extension hg.continuous.continuousOn
      hgd.continuous.continuousOn hpositive heq
  · haveI : IsEmpty AngularMaster.ActualPairIndex := not_nonempty_iff.mp hindex
    have hreal : realProduct b r = fun _ => (1 : ℝ) := by
      funext x
      simp [realProduct, AngularMaster.complexIndexedAngularProduct]
    have hzero : ∀ θ, g θ = 0 := by
      intro θ
      change c r * deriv (realProduct b r) (Real.cos θ) = 0
      rw [hreal]
      simp
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro t _ _
      simp
    · intro θ _
      exact le_rfl
    · intro θ hθ hpos
      have hz : F r θ = 0 := (heq θ hθ).trans (hzero θ)
      rw [hz] at hpos
      exact False.elim (lt_irrefl (0 : ℝ) hpos)

end TaylorsProdigy
