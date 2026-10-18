import AWPIRH.RowTransform
import AWPIRH.OneBindingAssembly

/-!
The local ODE is derived once the two ORIGINAL coefficient sequences are
identified.  This module does not prove that identity and does not alter US_AWPI.
The unproved identity is explicitly retained as an argument of the new assembly.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

/-- Exact unresolved analytic identification, not an energy or RH assertion. -/
def NativeProductCoefficientIdentity : Prop :=
  ∀ n : ℕ, nativeCoefficients n = productLogCoefficients n

/-- The residual obligation is equality of the two fixed functions. -/
theorem nativeProductCoefficientIdentity_iff_fun_eq :
    NativeProductCoefficientIdentity ↔ nativeCoefficients = productLogCoefficients := by
  constructor
  · intro h
    exact funext h
  · intro h n
    exact congrFun h n

/-- Scalar derivative of the literal phase map, with inner function fixed. -/
theorem phaseMap_hasDerivAt (η : ℂ) {v : ℂ} (hv : (1 : ℂ)-v ≠ 0) :
    HasDerivAt (phaseMap η) ((η-1)/(1-v)^2) v := by
  have hn : HasDerivAt (fun w : ℂ => (η-1)*w) (η-1) v :=
    hasDerivAt_const_mul (𝕜 := ℂ) (x := v) (η-1)
  have hd : HasDerivAt (fun w : ℂ => 1-w) (-1 : ℂ) v := by
    apply HasDerivAt.const_sub
    exact hasDerivAt_id v
  have hquot := hn.fun_div hd hv
  have halg : ((η-1)*(1-v)-((η-1)*v)*(-1))/(1-v)^2 = (η-1)/(1-v)^2 := by
    congr 1
    ring
  rw [halg] at hquot
  exact hquot

/-- Chain rule for the same entire product already checked in v0.7.4. -/
theorem product_phase_deriv (η : ℂ) {v : ℂ} (hv : (1 : ℂ)-v ≠ 0) :
    deriv (fun w : ℂ => symmetricProduct (phaseMap η w)) v =
      deriv symmetricProduct (phaseMap η v) * ((η-1)/(1-v)^2) := by
  have hp := (symmetricProduct_differentiable (phaseMap η v)).hasDerivAt
  have hcomp := HasDerivAt.comp
    (h₂ := symmetricProduct) (h := phaseMap η) v hp (phaseMap_hasDerivAt η hv)
  exact hcomp.deriv

/-- Every analytic expansion of the actual log derivative supplies a local row ODE. -/
theorem localRowODE_of_productLog_expansion {c : ℕ → ℂ}
    (hF : HasFPowerSeriesAt productLogDerivative
      (FormalMultilinearSeries.ofScalars ℂ c) (0 : ℂ)) (η : ℂ) :
    ∀ᶠ v in 𝓝 (0 : ℂ),
      deriv (fun w : ℂ => symmetricProduct (phaseMap η w)) v +
        (((η-1)/(1-v)) * rowAnalyticSum c η v) *
          symmetricProduct (phaseMap η v) = 0 := by
  have hrow := rowAnalyticSum_transform_eventually hF η
  have hcont : ContinuousAt (phaseMap η) (0 : ℂ) := by
    unfold phaseMap
    have hnum : ContinuousAt (fun v : ℂ => (η - 1) * v) 0 :=
      continuousAt_const.mul continuousAt_id
    have hden0 : ContinuousAt (fun v : ℂ => 1 - v) 0 :=
      continuousAt_const.sub continuousAt_id
    have hne : (1 - (0 : ℂ)) ≠ 0 := by norm_num
    exact hnum.div hden0 hne
  have ht : Tendsto (phaseMap η) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [phaseMap_zero] using hcont.tendsto
  have hclear := ht.eventually productLogDerivative_local_cleared_identity
  have hden : ∀ᶠ v : ℂ in 𝓝 0, (1 : ℂ)-v ≠ 0 := by
    have hv : ∀ᶠ v : ℂ in 𝓝 0, ‖v‖ < 1 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
    filter_upwards [hv] with v hv
    exact one_sub_ne_zero_of_mem_unitDisc ((unitDisc_iff v).mpr hv)
  filter_upwards [hrow,hclear,hden] with v hr hc hv
  rw [product_phase_deriv η hv, hr]
  calc
    deriv symmetricProduct (phaseMap η v) * ((η-1)/(1-v)^2) +
        (((η-1)/(1-v)) * (productLogDerivative (phaseMap η v)/(1-v))) *
          symmetricProduct (phaseMap η v) =
      ((η-1)/(1-v)^2) *
        (deriv symmetricProduct (phaseMap η v) +
          productLogDerivative (phaseMap η v)*symmetricProduct (phaseMap η v)) := by
            field_simp [hv]
    _ = 0 := by rw [hc, mul_zero]

/-- The product's own canonical coefficients have the required row identity. -/
theorem PRODUCT_LOG_COEFFICIENTS_LOCAL_ROW_ODE (η : ℂ) :
    ∀ᶠ v in 𝓝 (0 : ℂ),
      deriv (fun w : ℂ => symmetricProduct (phaseMap η w)) v +
        (((η-1)/(1-v)) * rowAnalyticSum productLogCoefficients η v) *
          symmetricProduct (phaseMap η v) = 0 := by
  have hF : HasFPowerSeriesAt productLogDerivative
      (FormalMultilinearSeries.ofScalars ℂ productLogCoefficients) (0 : ℂ) := by
    exact productLogSeries_hasFPowerSeriesAt
  exact localRowODE_of_productLog_expansion hF η

/-- Only the displayed identification remains supplied; no modification of US. -/
theorem ACTUAL_LOCAL_ROW_ODE_OF_COEFFICIENT_IDENTITY
    (hCoeff : NativeProductCoefficientIdentity) : ActualLocalRowODE := by
  have heq : nativeCoefficients = productLogCoefficients := funext hCoeff
  intro η hη
  rw [heq]
  exact PRODUCT_LOG_COEFFICIENTS_LOCAL_ROW_ODE η

/-- Partial native forward assembly with an explicit all-depth coefficient input. -/
theorem MATHLIB_RH_OF_US_AND_COEFFICIENT_IDENTITY
    (hUS : US_AWPI) (hCoeff : NativeProductCoefficientIdentity) :
    _root_.RiemannHypothesis := by
  exact MATHLIB_RH_OF_US_AND_LOCAL_ROW_ODE hUS
    (ACTUAL_LOCAL_ROW_ODE_OF_COEFFICIENT_IDENTITY hCoeff)

end AWPIRH
