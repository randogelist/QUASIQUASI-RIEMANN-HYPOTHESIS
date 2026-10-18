import AWPIRH.NativeCompletionReduction
import Bridge.USForwardLocalPole07
import Bridge.ExplicitMersenneReadout
import Merger02.Dominance
import Merger02.PoleAlgebra
import Merger02.RowCoefficient
import Core.QuarterShiftReciprocalAngleJet
import Derivations.FreeEnergyFrontierDerivation
import Derivations.BKQR.PiActualCayleyClosure
import Derivations.BKQR.StrictPiActualCayleyClosure
import Derivations.BKQR.HardyCoeffActualCayleyClosure

/-!
Native RH endpoints with every residual hypothesis visible.

The existing generic SOLOBOLO geometry theorems remain supporting imports.
Every endpoint declared below concludes Mathlib's literal RiemannHypothesis.
The local-pole + trace theorem is a new composition of the supplied branches;
it does not prove either its local coefficient premise or its trace convergence.
-/

set_option autoImplicit false

namespace RHMaster.NativeRoutes

/-- Both actual completed-xi normalizations are definitionally identical. -/
theorem soloboloXi_eq_canonical : NativeSolobolo.mathlibXi = AWPIRH.xi := rfl

/-- The slit representative and the canonical entire theta have the same values. -/
theorem soloboloTheta_eq_canonical : NativeSolobolo.mathlibSlitTheta = AWPIRH.theta := rfl

/-- The local-pole branch uses the same actual completed-xi function. -/
theorem mergerXi_eq_canonical : Merger02.actualXi = AWPIRH.xi := rfl

/-- The local-pole branch uses the same actual theta function. -/
theorem mergerTheta_eq_canonical : Merger02.theta = AWPIRH.theta := rfl

/-- The direct and recursive Widder branch uses the same actual completed xi. -/
theorem widderXi_eq_canonical : NativeSoloboloNegativity.xiEntire = AWPIRH.xi := rfl

/-- Entire-product ODE closure with its remaining coefficient identification. -/
theorem rh_of_native_energy_and_coefficient_identity
    (hUS : AWPIRH.US_AWPI)
    (hCoeff : AWPIRH.NativeProductCoefficientIdentity) :
    _root_.RiemannHypothesis :=
  AWPIRH.MATHLIB_RH_OF_US_AND_COEFFICIENT_IDENTITY hUS hCoeff

/-- Equivalent available assembly at the local-row-ODE interface. -/
theorem rh_of_native_energy_and_local_row_ode
    (hUS : AWPIRH.US_AWPI)
    (hLocal : AWPIRH.ActualLocalRowODE) :
    _root_.RiemannHypothesis :=
  AWPIRH.MATHLIB_RH_OF_US_AND_LOCAL_ROW_ODE hUS hLocal

/-- More explicit split into the native Mellin germ and product coefficient germ. -/
theorem rh_of_native_energy_mellin_and_product_germs
    (hUS : AWPIRH.US_AWPI)
    (hMellin : AWPIRH.NativeMellinAnchorGerm)
    (hProduct : AWPIRH.XiWidderProductCoefficientIdentity) :
    _root_.RiemannHypothesis :=
  AWPIRH.MATHLIB_RH_OF_US_MELLIN_GERM_AND_PRODUCT_GERM hUS hMellin hProduct

/-- Actual-xi row-energy route, with the remaining finite-filter estimate supplied. -/
theorem rh_of_actual_energy_and_finite_filter
    (hFilter : Merger02.ActualFiniteFilterStatement)
    (hUS : Merger02.ActualUS) :
    _root_.RiemannHypothesis :=
  Merger02.US_ENERGY_IMPLIES_RH_GIVEN_FINITE_FILTER hFilter hUS

/-- Frozen original positivity route with the smaller local-pole interface. -/
theorem rh_of_frozen_positivity_and_local_pole
    (hLocal : Merger04.ForwardLocalPole.ActualLocalPoleForcesDirectNegativity)
    (hUS : NativeSoloboloContinuant.ActualCofinalUniformDepthPositive) :
    _root_.RiemannHypothesis :=
  Merger04.ForwardLocalPole.FROZEN_US_IMPLIES_RH_FROM_LOCAL_POLE hLocal hUS

/-- Original direct trace route; global channel analysis is still explicit. -/
theorem rh_of_cayley_trace_and_channel_analysis
    (S : NativeSoloboloNegativity.FiniteCayleyDefectSystem)
    (hChannel : NativeSoloboloNegativity.ActualOffLineChannelAnalysis)
    (hTrace : NativeSoloboloNegativity.CofinalMersenneXiCayleyTraceConvergence S) :
    _root_.RiemannHypothesis :=
  NativeSoloboloNegativity.MERSENNE_XI_CAYLEY_TRACE_AND_CHANNEL_ANALYSIS_IMPLY_RH
    S hChannel hTrace

/-- New cross-branch assembly: direct negativity on the supplied regular anchors
contradicts cofinal positivity of the actual entire-xi recursive moments. -/
theorem rh_of_local_pole_and_actual_cofinal_positivity
    (hLocal : Merger04.ForwardLocalPole.ActualLocalPoleForcesDirectNegativity)
    (hPositive : NativeSoloboloNegativity.CofinalUniformDepthPositive) :
    _root_.RiemannHypothesis := by
  by_contra hNot
  rcases Merger04.LocalPole.NOT_RH_GIVES_ACTUAL_XI_INTERIOR_SIMPLE_POLE hNot with
    ⟨P, _⟩
  rcases hLocal P with ⟨K, hK⟩
  rcases hPositive K with ⟨N, hKN, hN⟩
  rcases hK N hKN with ⟨a, haRegular, haNegative⟩
  have hEq :=
    NativeSoloboloNegativity.XI_WIDDER_DIRECT_EQ_RECURSIVE_ON_REGULAR_ANCHORS
      a haRegular N
  rw [hEq] at haNegative
  exact (not_lt_of_ge (hN a haRegular.1)) haNegative

/-- New merged trace endpoint: the global channel premise is replaced by the
local-pole coefficient-negativity premise, using only proven regular-anchor
transport. Both remaining inputs are displayed separately. -/
theorem rh_of_local_pole_and_cayley_trace
    (S : NativeSoloboloNegativity.FiniteCayleyDefectSystem)
    (hLocal : Merger04.ForwardLocalPole.ActualLocalPoleForcesDirectNegativity)
    (hTrace : NativeSoloboloNegativity.CofinalMersenneXiCayleyTraceConvergence S) :
    _root_.RiemannHypothesis :=
  rh_of_local_pole_and_actual_cofinal_positivity hLocal
    (NativeSoloboloNegativity.MERSENNE_XI_CAYLEY_TRACE_CONVERGENCE_GIVES_COFINAL_WIDDER
      S hTrace)

end RHMaster.NativeRoutes
