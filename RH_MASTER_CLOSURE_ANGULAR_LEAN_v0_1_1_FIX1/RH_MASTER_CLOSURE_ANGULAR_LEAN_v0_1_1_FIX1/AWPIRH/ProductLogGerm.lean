import AWPIRH.ProductEntire

/-!
Unconditional local logarithmic derivative of the original symmetric product.
This supplies an actual analytic germ, not the missing native coefficient identity.
The series here is deliberately NOT substituted for nativeCoefficients or US_AWPI.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

def productLogDerivative (r : ℂ) : ℂ :=
  -deriv symmetricProduct r / symmetricProduct r

theorem symmetricProduct_eventually_ne_zero :
    ∀ᶠ r : ℂ in 𝓝 (0 : ℂ), symmetricProduct r ≠ 0 := by
  have hne : ∀ᶠ z : ℂ in 𝓝 (symmetricProduct 0), z ≠ 0 :=
    IsOpen.eventually_mem isOpen_ne (by
      change symmetricProduct (0 : ℂ) ≠ 0
      rw [symmetricProduct_zero]
      exact one_ne_zero)
  exact (symmetricProduct_differentiable 0).continuousAt.tendsto.eventually hne

theorem productLogDerivative_analyticAt_zero :
    AnalyticAt ℂ productLogDerivative (0 : ℂ) := by
  exact (symmetricProduct_analyticAt_zero.deriv.neg).div
    symmetricProduct_analyticAt_zero (by simp)

/-- Local cleared identity for -P'/P. The row-generating identity is still separate. -/
theorem productLogDerivative_local_cleared_identity :
    ∀ᶠ r : ℂ in 𝓝 (0 : ℂ),
      deriv symmetricProduct r + productLogDerivative r * symmetricProduct r = 0 := by
  filter_upwards [symmetricProduct_eventually_ne_zero] with r hr
  unfold productLogDerivative
  rw [div_mul_cancel₀ _ hr]
  ring

def productLogCoefficients (n : ℕ) : ℂ :=
  iteratedDeriv n productLogDerivative 0 / (n.factorial : ℂ)

def productLogSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ productLogCoefficients

theorem productLogSeries_hasFPowerSeriesAt :
    HasFPowerSeriesAt productLogDerivative productLogSeries (0 : ℂ) := by
  unfold productLogSeries productLogCoefficients
  convert! (config := { preTransparency := .all, postTransparency := .all })
    productLogDerivative_analyticAt_zero.hasFPowerSeriesAt using 0

theorem productLogSeries_radius_pos : 0 < productLogSeries.radius :=
  productLogSeries_hasFPowerSeriesAt.radius_pos

end AWPIRH
