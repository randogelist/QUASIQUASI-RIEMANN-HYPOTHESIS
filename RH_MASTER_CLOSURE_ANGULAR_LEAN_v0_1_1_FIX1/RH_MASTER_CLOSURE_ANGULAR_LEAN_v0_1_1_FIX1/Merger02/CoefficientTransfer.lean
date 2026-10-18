import Merger02.PoleFilterPolynomial
import Merger02.SlitTransport

/-!
Regularized actual generating germ at v=0.
The dslope removes the removable 0/0 singularity and keeps the coefficient
sequence tied to the actual derivative jet.
-/
namespace Merger02

open Complex Filter
open scoped Topology BigOperators

/-- Shift g from the regular anchor 1 to the origin. -/
noncomputable def shiftedG (w : ℂ) : ℂ := g (1 + w)

/-- The coefficient germ C(w)=(g(1)-g(1-w))/w, regularized at w=0. -/
noncomputable def jetQuotient (w : ℂ) : ℂ :=
  dslope shiftedG 0 (-w)

/-- The formal series obtained from the actual Taylor series by dslope and w↦-w. -/
noncomputable def jetSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  gTaylor.fslope.compContinuousLinearMap (-ContinuousLinearMap.id ℂ ℂ)

/-- The regularized quotient has the actual transformed Taylor series. -/
theorem jetQuotient_hasFPowerSeriesAt :
    HasFPowerSeriesAt jetQuotient jetSeries 0 := by
  have hshift : HasFPowerSeriesAt shiftedG gTaylor 0 := by
    change HasFPowerSeriesAt (fun w : ℂ => g (1 + w)) gTaylor 0
    have h := g_has_actual_Taylor_series.comp_sub (-1 : ℂ)
    simpa [sub_eq_add_neg, add_comm] using h
  have hslope : HasFPowerSeriesAt (dslope shiftedG 0) gTaylor.fslope 0 :=
    hshift.has_fpower_series_dslope_fslope
  have hslope' :
      HasFPowerSeriesAt (dslope shiftedG 0) gTaylor.fslope
        ((-ContinuousLinearMap.id ℂ ℂ) 0) := by
    simpa using hslope
  have hneg :
      HasFPowerSeriesAt
        ((dslope shiftedG 0) ∘ (-ContinuousLinearMap.id ℂ ℂ))
        (gTaylor.fslope.compContinuousLinearMap (-ContinuousLinearMap.id ℂ ℂ)) 0 :=
    hslope'.compContinuousLinearMap
  change HasFPowerSeriesAt (fun w : ℂ => dslope shiftedG 0 (-w)) jetSeries 0
  simpa [jetSeries, Function.comp_def] using hneg

/-- The coefficients of the regularized quotient are exactly the actual jet. -/
theorem jetSeries_coeff (n : ℕ) : jetSeries.coeff n = actualJet n := by
  unfold jetSeries actualJet
  rw [FormalMultilinearSeries.coeff]
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
  change (gTaylor.fslope n) (fun _ : Fin n => (-1 : ℂ)) =
    (-1 : ℂ) ^ n * iteratedDeriv (n + 1) g 1 / ((n + 1).factorial : ℂ)
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [FormalMultilinearSeries.coeff_fslope]
  simp [gTaylor, smul_eq_mul]
  rw [mul_div_assoc]

/-- Concrete quotient identity away from zero. -/
theorem jetQuotient_eq {w : ℂ} (hw : w ≠ 0) :
    jetQuotient w = (g 1 - g (1 - w)) / w := by
  have hn : -w ≠ (0 : ℂ) := neg_ne_zero.mpr hw
  rw [jetQuotient, dslope_of_ne shiftedG hn]
  simp [shiftedG, slope, hw, div_eq_mul_inv]
  ring

/-- Möbius change in the coefficient variable. -/
noncomputable def coefficientMobius (z v : ℂ) : ℂ :=
  (z - 1) * v / (1 - v)

/-- Analytic generating function with its value at v=0 filled in canonically. -/
noncomputable def regularGenerating (z v : ℂ) : ℂ :=
  (1 - v)⁻¹ * jetQuotient (coefficientMobius z v)

@[simp] theorem coefficientMobius_zero (z : ℂ) : coefficientMobius z 0 = 0 := by
  simp [coefficientMobius]

@[simp] theorem regularGenerating_zero (z : ℂ) :
    regularGenerating z 0 = actualJet 0 := by
  have h0 := jetQuotient_hasFPowerSeriesAt.coeff_zero
    (fun _ : Fin 0 => (1 : ℂ))
  change jetSeries.coeff 0 = jetQuotient 0 at h0
  have hc : jetQuotient 0 = actualJet 0 := by
    rw [← h0]
    exact jetSeries_coeff 0
  simp only [regularGenerating, coefficientMobius_zero, sub_zero, inv_one, one_mul]
  exact hc

/-- Away from v=0 the regular germ equals the original meromorphic formula. -/
theorem regularGenerating_eq_raw {z v : ℂ}
    (hz : z ≠ 1) (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    regularGenerating z v = rawGenerating z v := by
  have hw : coefficientMobius z v ≠ 0 := by
    unfold coefficientMobius
    apply div_ne_zero
    · exact mul_ne_zero (sub_ne_zero.mpr hz) hv0
    · exact sub_ne_zero.mpr hv1.symm
  rw [regularGenerating, jetQuotient_eq hw]
  unfold coefficientMobius rawGenerating mobius
  have hd : (1 : ℂ) - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  field_simp [hd, hz', hv0]
  ring

/-- The regularized generating function is analytic at the origin. -/
theorem regularGenerating_analyticAt_zero (z : ℂ) :
    AnalyticAt ℂ (regularGenerating z) 0 := by
  have hj0 : AnalyticAt ℂ jetQuotient 0 := jetQuotient_hasFPowerSeriesAt.analyticAt
  have hm : AnalyticAt ℂ (coefficientMobius z) 0 := by
    change AnalyticAt ℂ (fun v : ℂ => (z - 1) * v / (1 - v)) 0
    have hn : AnalyticAt ℂ (fun v : ℂ => (z - 1) * v) 0 := by fun_prop
    have hd : AnalyticAt ℂ (fun v : ℂ => 1 - v) 0 := by fun_prop
    exact hn.div hd (by norm_num)
  have hjm : AnalyticAt ℂ (fun v : ℂ => jetQuotient (coefficientMobius z v)) 0 := by
    exact hj0.fun_comp_of_eq hm (by simp)
  have hi : AnalyticAt ℂ (fun v : ℂ => (1 - v)⁻¹) 0 := by
    fun_prop
  unfold regularGenerating
  exact hi.fun_mul hjm

end Merger02
