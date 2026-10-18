import AWPI.PhiRH.CanonicalOneSidedTail

namespace AWPI.PhiRH.ScalarConcreteFrontier

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge

/-- The final scalar passivity core: the canonical plus exact defect is
nonpositive at every nontrivial zeta zero.  This is the one-sided scalar
content extracted from the final exact-to-tail frontier. -/
def PlusPassivityCore : Prop :=
  ∀ rho : ℂ, NontrivialZetaZero rho →
    CanonicalOneSidedTail.canonicalPlusExactDefect rho ≤ 0

/-- The canonical plus jet is nonzero at every nontrivial zeta zero, derived
from the already verified scale and transverse-jet theorems. -/
theorem canonicalPlusJet_nonzero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    CanonicalOneSidedTail.canonicalPlusJet rho ≠ 0 := by
  unfold CanonicalOneSidedTail.canonicalPlusJet
  exact ActivityFrontier.boundJetPlus_nonzero
    CanonicalBindingScales.canonicalPlusJetScale
    CanonicalTransverseJet.canonicalTransverseJet rho
    (CanonicalBindingScales.canonicalPlusJetScale_ne_zero rho)
    (CanonicalTransverseJet.canonicalTransverseJet_ne_zero rho hz)

/-- Scalar factorization of the canonical plus exact defect. -/
theorem canonicalPlusExactDefect_factorization (rho : ℂ) :
    CanonicalOneSidedTail.canonicalPlusExactDefect rho =
      (RocqPortModel.scale2 (2 * (rho.re - (1 / 2 : ℝ))) - 1) *
        (CanonicalOneSidedTail.canonicalPlusJet rho) ^ 2 := by
  unfold CanonicalOneSidedTail.canonicalPlusExactDefect
  ring

/-- The verified exact-to-tail frontier plus the verified canonical tail decay
implies the scalar passivity core. -/
theorem plusPassivityCore_of_exactTailUpper
    (hUpper : CanonicalOneSidedTail.CanonicalPlusExactTailUpper) :
    PlusPassivityCore := by
  intro rho hz
  exact CanonicalOneSidedTail.canonicalPlusExactDefect_nonpos_of_tail_upper
    hUpper rho hz

/-- Scalar passivity excludes nontrivial zeros to the right of 1/2. -/
theorem re_le_half_of_plusPassivityCore
    (hCore : PlusPassivityCore)
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    rho.re ≤ (1 / 2 : ℝ) := by
  have hdef := hCore rho hz
  have hjetNe : CanonicalOneSidedTail.canonicalPlusJet rho ≠ 0 :=
    canonicalPlusJet_nonzero rho hz
  have hjetSqPos : 0 < (CanonicalOneSidedTail.canonicalPlusJet rho) ^ 2 :=
    sq_pos_of_ne_zero hjetNe
  by_contra hhalf
  have hc : 0 < rho.re - (1 / 2 : ℝ) := sub_pos.mpr (lt_of_not_ge hhalf)
  have harg : 0 < 2 * (rho.re - (1 / 2 : ℝ)) := by nlinarith
  have hscale : 1 < RocqPortModel.scale2 (2 * (rho.re - (1 / 2 : ℝ))) := by
    have hs := RocqPortModel.scale2_strictMono_proved harg
    rw [RocqPortModel.scale2_at_zero] at hs
    exact hs
  rw [canonicalPlusExactDefect_factorization] at hdef
  nlinarith

/-- Reflection upgrades the one-sided scalar passivity core to full native RH. -/
theorem MATHLIB_RH_OF_PLUS_PASSIVITY_CORE
    (hCore : PlusPassivityCore) : RiemannHypothesis := by
  unfold RiemannHypothesis
  intro rho hzeta htrivial hneOne
  have hz : NontrivialZetaZero rho := ⟨hzeta, htrivial, hneOne⟩
  have hle : rho.re ≤ (1 / 2 : ℝ) :=
    re_le_half_of_plusPassivityCore hCore rho hz
  have hzRef : NontrivialZetaZero (1 - rho) :=
    CanonicalOneSidedTail.reflectedNontrivialZetaZero rho hz
  have hrefLe : (1 - rho : ℂ).re ≤ (1 / 2 : ℝ) :=
    re_le_half_of_plusPassivityCore hCore (1 - rho) hzRef
  have hge : (1 / 2 : ℝ) ≤ rho.re := by
    simp at hrefLe
    linarith
  exact le_antisymm hle hge

/-- Native RH implies the scalar passivity core, since the canonical exact
plus defect vanishes on the critical line. -/
theorem plusPassivityCore_of_RH
    (hRH : RiemannHypothesis) : PlusPassivityCore := by
  intro rho hz
  have hcrit : rho.re = (1 / 2 : ℝ) :=
    hRH rho hz.1 hz.2.1 hz.2.2
  rw [canonicalPlusExactDefect_factorization]
  simp [hcrit, RocqPortModel.scale2]

/-- The fully reduced scalar frontier is logically equivalent to Mathlib's
native Riemann Hypothesis. -/
theorem plusPassivityCore_iff_RiemannHypothesis :
    PlusPassivityCore ↔ RiemannHypothesis := by
  exact ⟨MATHLIB_RH_OF_PLUS_PASSIVITY_CORE, plusPassivityCore_of_RH⟩

end AWPI.PhiRH.ScalarConcreteFrontier
