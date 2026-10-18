import RHMaster.AngularCoverage
import RHMaster.QQRHClosure
import RHMaster.CayleyRoutes
import RHMaster.AWPIRoutes
import RHMaster.NativeRoutes
import GPHausdorff.Our.FiniteHierarchy

/-!
The master endpoint is the literal Mathlib RiemannHypothesis. The following
atlas connects the selected criteria and retains all open premises. The
equivalences do not assert either side.
-/

set_option autoImplicit false
namespace RHMaster

theorem residual_iff_cayley_zero_loss :
    AngularResidualNonnegative ↔ CayleyRHAClosure.ZetaCayleyZeroLoss :=
  native_RH_iff_angularResidualNonnegative.symm.trans rh_iff_cayley_zero_loss

theorem residual_iff_allSlopePositivity :
    AngularResidualNonnegative ↔ AllSlopePositivity :=
  native_RH_iff_angularResidualNonnegative.symm.trans rh_iff_allSlopePositivity

theorem residual_iff_awpi_exact_tail_upper :
    AngularResidualNonnegative ↔ AWPIExactTailUpper :=
  native_RH_iff_angularResidualNonnegative.symm.trans awpi_exact_tail_upper_iff_rh.symm

theorem no_regular_stationary_implies_residual
    (h : AngularRegularity.ActualNoRegularAngularStationary) :
    AngularResidualNonnegative :=
  native_RH_iff_angularResidualNonnegative.mp
    (native_RH_of_noRegularAngularStationary h)

/-- The one-input residual angular closure, after both proved coverage regions. -/
theorem RH_MASTER_CLOSURE (h : AngularResidualNonnegative) :
    _root_.RiemannHypothesis :=
  native_RH_of_angularResidualNonnegative h

/-- Exact residual equivalence; its right-hand side remains a research target. -/
theorem RH_MASTER_EQUIVALENCE :
    _root_.RiemannHypothesis ↔ AngularResidualNonnegative :=
  native_RH_iff_angularResidualNonnegative

/-- Each listed condition is exactly equivalent to native RH. -/
theorem RH_MASTER_EQUIVALENCE_ATLAS :
    (_root_.RiemannHypothesis ↔ AngularResidualNonnegative) ∧
    (_root_.RiemannHypothesis ↔ ActualInteriorSlopeNonnegative) ∧
    (_root_.RiemannHypothesis ↔ AllSlopeQQRH) ∧
    (_root_.RiemannHypothesis ↔ CofinalSlopeQQRH) ∧
    (_root_.RiemannHypothesis ↔ AllSlopePositivity) ∧
    (_root_.RiemannHypothesis ↔ CayleyRHAClosure.ZetaCayleyZeroLoss) ∧
    (_root_.RiemannHypothesis ↔ AWPIExactTailUpper) ∧
    (_root_.RiemannHypothesis ↔ AngularMaster.frozenLogMaster (1 / 2)) :=
  ⟨native_RH_iff_angularResidualNonnegative,
    native_RH_iff_actualInteriorSlopeNonnegative,
    rh_iff_allSlopeQQRH, rh_iff_cofinalSlopeQQRH,
    rh_iff_allSlopePositivity, rh_iff_cayley_zero_loss,
    awpi_exact_tail_upper_iff_rh.symm,
    AngularMaster.FROZEN_RH_MASTER_EQUIVALENCE⟩

end RHMaster
