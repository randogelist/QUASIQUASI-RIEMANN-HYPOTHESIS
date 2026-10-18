import CayleyGolPhi.ZeroEquivalence
import StandardCayleyLoss

namespace CayleyRHAClosure

/-- The constructed, reflection-invariant Cayley loss of a spectral point.
It is defined for every complex point, independently of any zero hypothesis. -/
noncomputable def spectralCayleyLoss (s : ℂ) : ℝ :=
  GPBKQRKernel.cayleyDefect s.re

/-- The corresponding constructed Cayley transmission coefficient. -/
noncomputable def spectralCayleyTransmission (s : ℂ) : ℝ :=
  GPBKQRKernel.cayleyContraction s.re

/-- The concrete unit-state energy loss under the constructed Cayley step. -/
noncomputable def spectralCayleyUnitEnergyLoss (s : ℂ) : ℝ :=
  GPBKQRKernel.scalarEnergy 1 -
    GPBKQRKernel.scalarEnergy (GPBKQRKernel.cayleyStep s.re 1)

/-- Spectral Cayley loss is nonnegative without a premise. -/
theorem spectralCayleyLoss_nonneg (s : ℂ) :
    0 ≤ spectralCayleyLoss s := by
  exact GPBKQRKernel.cayleyDefect_nonneg s.re

/-- The spectral Cayley loss vanishes exactly on the critical line. -/
theorem spectralCayleyLoss_eq_zero_iff_criticalLine (s : ℂ) :
    spectralCayleyLoss s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  exact GPBKQRKernel.cayleyDefect_eq_zero_iff s.re

/-- The constructed transmission saturates exactly on the critical line. -/
theorem spectralCayleyTransmission_eq_one_iff_criticalLine (s : ℂ) :
    spectralCayleyTransmission s = 1 ↔ s.re = (1 / 2 : ℝ) := by
  exact GPBKQRKernel.cayleyContraction_eq_one_iff s.re

/-- The concrete unit-state energy loss is exactly the Cayley defect. -/
theorem spectralCayleyUnitEnergyLoss_eq_loss (s : ℂ) :
    spectralCayleyUnitEnergyLoss s = spectralCayleyLoss s := by
  simpa [spectralCayleyUnitEnergyLoss, spectralCayleyLoss,
    GPBKQRKernel.scalarEnergy] using
      GPBKQRKernel.cayleyStep_energy_defect s.re 1

/-- Unit-state energy preservation is exactly the critical-line condition. -/
theorem spectralCayleyUnitEnergy_preserved_iff_criticalLine (s : ℂ) :
    GPBKQRKernel.scalarEnergy (GPBKQRKernel.cayleyStep s.re 1) =
        GPBKQRKernel.scalarEnergy 1 ↔
      s.re = (1 / 2 : ℝ) := by
  exact GPBKQRKernel.cayleyStep_unit_saturates_iff_center s.re

/-- Every nontrivial completed-GolPhi zero has zero constructed Cayley loss. -/
def GolPhiCayleyZeroLoss : Prop :=
  ∀ s : ℂ, CayleyGolPhi.NontrivialGolPhiZero s → spectralCayleyLoss s = 0

/-- Every literal nontrivial zeta zero has zero constructed Cayley loss. -/
def ZetaCayleyZeroLoss : Prop :=
  ∀ s : ℂ, CayleyGolPhi.NontrivialZetaZero s → spectralCayleyLoss s = 0

/-- Every nontrivial completed-GolPhi zero saturates the Cayley contraction. -/
def GolPhiCayleySaturation : Prop :=
  ∀ s : ℂ, CayleyGolPhi.NontrivialGolPhiZero s →
    spectralCayleyTransmission s = 1

/-- Every nontrivial completed-GolPhi zero preserves unit Cayley energy. -/
def GolPhiCayleyUnitEnergyPreservation : Prop :=
  ∀ s : ℂ, CayleyGolPhi.NontrivialGolPhiZero s →
    GPBKQRKernel.scalarEnergy (GPBKQRKernel.cayleyStep s.re 1) =
      GPBKQRKernel.scalarEnergy 1

/-- Pointwise zero loss is exactly the completed-GolPhi critical-line statement. -/
theorem GOLPHI_CAYLEY_ZERO_LOSS_IFF_GOLPHI_RH :
    GolPhiCayleyZeroLoss ↔ CayleyGolPhi.GolPhiRiemannHypothesis := by
  constructor
  · intro h s hs
    exact (spectralCayleyLoss_eq_zero_iff_criticalLine s).1 (h s hs)
  · intro h s hs
    exact (spectralCayleyLoss_eq_zero_iff_criticalLine s).2 (h s hs)

/-- The actual completed-GolPhi Cayley zero-loss criterion is exactly Mathlib RH. -/
theorem GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH :
    GolPhiCayleyZeroLoss ↔ _root_.RiemannHypothesis := by
  exact GOLPHI_CAYLEY_ZERO_LOSS_IFF_GOLPHI_RH.trans
    CayleyGolPhi.GOLPHI_RH_IFF_MATHLIB_RH

/-- The literal-zeta Cayley zero-loss criterion is exactly Mathlib RH. -/
theorem ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH :
    ZetaCayleyZeroLoss ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h
    unfold _root_.RiemannHypothesis
    intro s hz htriv hs1
    exact (spectralCayleyLoss_eq_zero_iff_criticalLine s).1
      (h s ⟨hz, htriv, hs1⟩)
  · intro hRH s hs
    exact (spectralCayleyLoss_eq_zero_iff_criticalLine s).2
      (hRH s hs.1 hs.2.1 hs.2.2)

/-- GolPhi and zeta Cayley zero-loss criteria are the same actual predicate. -/
theorem GOLPHI_CAYLEY_ZERO_LOSS_IFF_ZETA_CAYLEY_ZERO_LOSS :
    GolPhiCayleyZeroLoss ↔ ZetaCayleyZeroLoss := by
  constructor
  · intro h s hs
    exact h s ((CayleyGolPhi.NONTRIVIAL_GOLPHI_ZERO_IFF_NONTRIVIAL_ZETA_ZERO s).2 hs)
  · intro h s hs
    exact h s ((CayleyGolPhi.NONTRIVIAL_GOLPHI_ZERO_IFF_NONTRIVIAL_ZETA_ZERO s).1 hs)

/-- Cayley contraction saturation is another exact RH formulation. -/
theorem GOLPHI_CAYLEY_SATURATION_IFF_MATHLIB_RH :
    GolPhiCayleySaturation ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h
    apply CayleyGolPhi.GOLPHI_RH_IFF_MATHLIB_RH.mp
    intro s hs
    exact (spectralCayleyTransmission_eq_one_iff_criticalLine s).1 (h s hs)
  · intro hRH s hs
    have hline : s.re = (1 / 2 : ℝ) :=
      (CayleyGolPhi.GOLPHI_RH_IFF_MATHLIB_RH.mpr hRH) s hs
    exact (spectralCayleyTransmission_eq_one_iff_criticalLine s).2 hline

/-- Unit-state energy preservation is another exact RH formulation. -/
theorem GOLPHI_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_MATHLIB_RH :
    GolPhiCayleyUnitEnergyPreservation ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h
    apply CayleyGolPhi.GOLPHI_RH_IFF_MATHLIB_RH.mp
    intro s hs
    exact (spectralCayleyUnitEnergy_preserved_iff_criticalLine s).1 (h s hs)
  · intro hRH s hs
    have hline : s.re = (1 / 2 : ℝ) :=
      (CayleyGolPhi.GOLPHI_RH_IFF_MATHLIB_RH.mpr hRH) s hs
    exact (spectralCayleyUnitEnergy_preserved_iff_criticalLine s).2 hline

/-- A premise-free closure atlas collecting the exact RH equivalences. -/
theorem CAYLEY_RH_A_TIER_CLOSURE_ATLAS :
    (GolPhiCayleyZeroLoss ↔ _root_.RiemannHypothesis) ∧
    (ZetaCayleyZeroLoss ↔ _root_.RiemannHypothesis) ∧
    (GolPhiCayleySaturation ↔ _root_.RiemannHypothesis) ∧
    (GolPhiCayleyUnitEnergyPreservation ↔ _root_.RiemannHypothesis) := by
  exact ⟨GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH,
    ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH,
    GOLPHI_CAYLEY_SATURATION_IFF_MATHLIB_RH,
    GOLPHI_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_MATHLIB_RH⟩

end CayleyRHAClosure
