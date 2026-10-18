import OriginTrace
import AngularIntegral
import NativeClosure
import ScalarLittleO

/-!
# Native RH closure from the angular little-o remainder

The public endpoint has one hypothesis, `SmallOPremise`.  Both the angular
integral and the multiplicity-bearing critical-line cutoff are concrete.
The normalized integral limit and the positive actual-zero trace are proved
in the imported modules and are not parameters of the endpoint.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RHSmallO

/-- The literal weighted angular logarithmic-derivative integral. -/
def I : ℝ → ℝ := AngularMaster.angularI

/-- The real first logarithmic coefficient of the actual entire theta. -/
def q1 : ℝ := (deriv AWPIRH.theta 0 / AWPIRH.theta 0).re

/-- The only hypothesis of the conditional closure theorem. -/
def SmallOPremise : Prop :=
  (fun r : ℝ => I r - Real.pi * r * criticalLineCutoff r)
    =o[𝓝[>] 0] (fun r : ℝ => r)

/-- Unconditional first-order asymptotics of the concrete angular integral. -/
theorem normalized_integral_tendsto :
    Tendsto (fun r : ℝ => I r / r) (𝓝[>] 0) (𝓝 (Real.pi * q1)) := by
  exact AngularMaster.angularI_div_radius_tendsto

/-- The unnormalized angular integral tends to zero unconditionally. -/
theorem integral_tendsto_zero : Tendsto I (𝓝[>] 0) (𝓝 0) := by
  exact AngularMaster.angularI_tendsto_zero

/-- Under the little-o hypothesis, the concrete finite line cutoffs
converge to the full first logarithmic coefficient. -/
theorem cutoff_tendsto_of_small_o (h : SmallOPremise) :
    Tendsto criticalLineCutoff (𝓝[>] 0) (𝓝 q1) := by
  exact RHScalarLittleO.cutoff_tendsto_of_normalized_integral_and_isLittleO
    I criticalLineCutoff q1 normalized_integral_tendsto h

/-- The omitted normalized scalar response vanishes under the sole premise. -/
theorem residual_tendsto_of_small_o (h : SmallOPremise) :
    Tendsto (fun r : ℝ => q1 - criticalLineCutoff r) (𝓝[>] 0) (𝓝 0) := by
  exact RHScalarLittleO.residual_tendsto_zero_of_normalized_integral_and_isLittleO
    I criticalLineCutoff q1 normalized_integral_tendsto h

/-- Conditional closure to Mathlib's literal Riemann hypothesis. -/
theorem rh_of_small_o (h : SmallOPremise) : _root_.RiemannHypothesis := by
  apply scalar_response_limit_implies_RH q1
  · simpa only [q1, spectralWeight] using
      AngularMaster.actual_theta_origin_real_trace
  · exact residual_tendsto_of_small_o h

/-- The same endpoint with the sole hypothesis fully expanded. -/
theorem rh_of_angular_integral_isLittleO
    (h : (fun r : ℝ =>
      AngularMaster.angularI r - Real.pi * r * criticalLineCutoff r)
        =o[𝓝[>] 0] (fun r : ℝ => r)) :
    _root_.RiemannHypothesis := by
  exact rh_of_small_o h

end RHSmallO
