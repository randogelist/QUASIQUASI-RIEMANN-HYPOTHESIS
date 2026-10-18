import CayleyRHClosure
import AngularMaster.Chain

/-!
Actual-object alignment and routes between the Cayley and angular criteria.
Every route concludes native Mathlib RH from an explicit criterion, or proves
an equivalence of criteria. None asserts that those criteria are satisfied.
The generic jet-loss nonnegativity theorem is not used as zero loss.
-/

set_option autoImplicit false
noncomputable section
namespace RHMaster

/-- Both source branches use exactly the same completed xi normalization. -/
theorem cayley_xi_eq_angular_xi :
    CayleyGolPhi.mathlibXi = AWPIRH.xi := rfl

/-- Both source branches use exactly the same centered xi. -/
theorem cayley_centeredXi_eq_angular_centeredXi :
    CayleyGolPhi.centeredXi = AWPIRH.centeredXi := rfl

/-- The object named slitTheta in the Cayley package is the entire angular theta. -/
theorem cayley_theta_eq_angular_theta :
    CayleyGolPhi.slitTheta = AWPIRH.theta := rfl

/-- The two literal nontrivial-zeta-zero predicates agree definitionally. -/
theorem cayley_nontrivialZero_iff_angular_nontrivialZero (s : ℂ) :
    CayleyGolPhi.NontrivialZetaZero s ↔ AWPIRH.NontrivialZero s := Iff.rfl

/-- The entire-descent proof supplies global analyticity to the Cayley object. -/
theorem cayley_theta_entire :
    AnalyticOnNhd ℂ CayleyGolPhi.slitTheta Set.univ := by
  rw [cayley_theta_eq_angular_theta]
  exact AWPIRH.theta_entire

/-- Native RH is equivalent to spectral zero loss at every nontrivial zeta zero. -/
theorem rh_iff_cayley_zero_loss :
    _root_.RiemannHypothesis ↔ CayleyRHAClosure.ZetaCayleyZeroLoss :=
  CayleyRHAClosure.ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.symm

/-- Native RH is equivalent to zero loss at every nontrivial completed-GolPhi zero. -/
theorem rh_iff_golphi_cayley_zero_loss :
    _root_.RiemannHypothesis ↔ CayleyRHAClosure.GolPhiCayleyZeroLoss :=
  CayleyRHAClosure.GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.symm

/-- Native RH is equivalent to Cayley saturation at the completed-GolPhi zeros. -/
theorem rh_iff_cayley_saturation :
    _root_.RiemannHypothesis ↔ CayleyRHAClosure.GolPhiCayleySaturation :=
  CayleyRHAClosure.GOLPHI_CAYLEY_SATURATION_IFF_MATHLIB_RH.symm

/-- Native RH is equivalent to preservation of the constructed unit-state energy. -/
theorem rh_iff_cayley_unit_energy_preservation :
    _root_.RiemannHypothesis ↔ CayleyRHAClosure.GolPhiCayleyUnitEnergyPreservation :=
  CayleyRHAClosure.GOLPHI_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_MATHLIB_RH.symm

/-- Conditional Cayley closure, exposing the entire remaining zero-loss input. -/
theorem rh_of_cayley_zero_loss
    (h : CayleyRHAClosure.ZetaCayleyZeroLoss) : _root_.RiemannHypothesis :=
  rh_iff_cayley_zero_loss.mpr h

/-- Spectral zero loss and the actual angular Master are equivalent. -/
theorem cayley_zero_loss_iff_angular_master :
    CayleyRHAClosure.ZetaCayleyZeroLoss ↔
      AngularMaster.ProfileMaster AngularMaster.actualProfile :=
  CayleyRHAClosure.ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.trans
    AngularMaster.native_RH_iff_actual_profileMaster

/-- Completed-GolPhi zero loss and the actual angular Master are equivalent. -/
theorem golphi_cayley_zero_loss_iff_angular_master :
    CayleyRHAClosure.GolPhiCayleyZeroLoss ↔
      AngularMaster.ProfileMaster AngularMaster.actualProfile :=
  CayleyRHAClosure.GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.trans
    AngularMaster.native_RH_iff_actual_profileMaster

/-- Cayley saturation and the actual angular Master are equivalent. -/
theorem cayley_saturation_iff_angular_master :
    CayleyRHAClosure.GolPhiCayleySaturation ↔
      AngularMaster.ProfileMaster AngularMaster.actualProfile :=
  CayleyRHAClosure.GOLPHI_CAYLEY_SATURATION_IFF_MATHLIB_RH.trans
    AngularMaster.native_RH_iff_actual_profileMaster

/-- Spectral zero loss is equivalent to any positive-parameter frozen log Master. -/
theorem cayley_zero_loss_iff_frozen_log_master {ε : ℝ} (hε : 0 < ε) :
    CayleyRHAClosure.ZetaCayleyZeroLoss ↔ AngularMaster.frozenLogMaster ε :=
  CayleyRHAClosure.ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.trans
    (AngularMaster.native_RH_iff_frozenLogMaster hε)

/-- The fixed one-half normalization uses no auxiliary analytic premise. -/
theorem cayley_zero_loss_iff_frozen_half_master :
    CayleyRHAClosure.ZetaCayleyZeroLoss ↔ AngularMaster.frozenLogMaster (1 / 2) :=
  CayleyRHAClosure.ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.trans
    AngularMaster.FROZEN_RH_MASTER_EQUIVALENCE

end RHMaster
