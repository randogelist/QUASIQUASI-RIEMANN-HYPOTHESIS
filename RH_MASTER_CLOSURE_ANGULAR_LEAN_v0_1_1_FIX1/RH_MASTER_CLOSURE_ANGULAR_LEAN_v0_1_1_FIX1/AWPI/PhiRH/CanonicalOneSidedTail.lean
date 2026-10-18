import AWPI.PhiRH.CanonicalTailDecay

namespace AWPI.PhiRH.CanonicalOneSidedTail

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.ActivityFrontier
open AWPI.PhiRH.CanonicalBindingScales
open AWPI.PhiRH.CanonicalTransverseJet
open AWPI.PhiRH.CanonicalTailDecay
open AWPI.PhiRH.RocqSourceLayer

/-- The canonical plus jet after the binding scale has been fixed to one. -/
noncomputable def canonicalPlusJet (rho : ℂ) : ℝ :=
  boundJetPlus canonicalPlusJetScale canonicalTransverseJet rho

/-- The canonical exact plus defect. -/
noncomputable def canonicalPlusExactDefect (rho : ℂ) : ℝ :=
  scale2 (2 * (rho.re - (1 / 2 : ℝ))) * (canonicalPlusJet rho) ^ 2 -
    (canonicalPlusJet rho) ^ 2

/-- The final one-sided exact-to-tail frontier, with no auxiliary finite-square
function left in the statement. -/
def CanonicalPlusExactTailUpper : Prop :=
  ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
    canonicalPlusExactDefect rho ≤
      canonicalKQPlusSource n rho.re rho.im *
        canonicalKQPlusSource n rho.re rho.im

/-- Native zero-free support on the other side: every nontrivial zero has real
part strictly below one. -/
theorem nontrivialZetaZero_re_lt_one
    (rho : ℂ) (hz : NontrivialZetaZero rho) : rho.re < 1 := by
  by_contra hlt
  have hge : 1 ≤ rho.re := le_of_not_gt hlt
  exact (riemannZeta_ne_zero_of_one_le_re hge) hz.1

/-- The functional equation sends every nontrivial zero to another nontrivial
zero. -/
theorem reflectedNontrivialZetaZero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    NontrivialZetaZero (1 - rho) := by
  have hcompleted : completedRiemannZeta rho = 0 :=
    NativeZetaSupport.completedRiemannZeta_eq_zero_of_nontrivialZetaZero rho hz
  have hrefCompleted : completedRiemannZeta (1 - rho) = 0 := by
    rw [completedRiemannZeta_one_sub rho, hcompleted]
  have honeSubNe : (1 - rho : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hz.2.2)
  have hrefZero : riemannZeta (1 - rho) = 0 := by
    rw [riemannZeta_def_of_ne_zero honeSubNe, hrefCompleted]
    simp
  have hreflPos : 0 < (1 - rho : ℂ).re := by
    have hlt := nontrivialZetaZero_re_lt_one rho hz
    simp
    linarith
  refine ⟨hrefZero, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hreal := congrArg Complex.re hn
    simp at hreal
    have hpos : 0 < 1 - rho.re := by
      simpa using hreflPos
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.zero_le n
    have hnp1 : 0 ≤ (n : ℝ) + 1 := by
      linarith
    have hrhsNonpos : -(2 * ((n : ℝ) + 1)) ≤ 0 := by
      exact neg_nonpos.mpr (mul_nonneg (by norm_num) hnp1)
    rw [hreal] at hpos
    exact (not_lt_of_ge hrhsNonpos) hpos
  · intro hEqOne
    have hrho0 : rho = 0 := sub_eq_self.mp hEqOne
    exact (TransverseFrontier.nontrivialZetaZero_ne_zero rho hz) hrho0

/-- The plus exact-to-tail upper bound together with the already proved
canonical tail decay forces the exact plus defect to be nonpositive. -/
theorem canonicalPlusExactDefect_nonpos_of_tail_upper
    (hUpper : CanonicalPlusExactTailUpper)
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    canonicalPlusExactDefect rho ≤ 0 := by
  by_contra hnonpos
  have hpos : 0 < canonicalPlusExactDefect rho := lt_of_not_ge hnonpos
  let eps : ℝ := canonicalPlusExactDefect rho / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  obtain ⟨N, hplus, _hminus⟩ :=
    canonicalKQ_jointTailDecay rho.re rho.im eps
      (NativeZetaSupport.nontrivialZetaZero_re_pos rho hz) heps
  have hUpperN := hUpper N rho hz
  dsimp [eps] at hplus
  linarith

/-- One-sided geometric consequence: the plus bound excludes zeros to the
right of the critical line. -/
theorem re_le_half_of_canonicalPlusExactTailUpper
    (hUpper : CanonicalPlusExactTailUpper)
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    rho.re ≤ (1 / 2 : ℝ) := by
  have hdef : canonicalPlusExactDefect rho ≤ 0 :=
    canonicalPlusExactDefect_nonpos_of_tail_upper hUpper rho hz
  have hjetNe : canonicalPlusJet rho ≠ 0 := by
    exact boundJetPlus_nonzero canonicalPlusJetScale canonicalTransverseJet rho
      (canonicalPlusJetScale_ne_zero rho)
      (canonicalTransverseJet_ne_zero rho hz)
  have hjetSqPos : 0 < (canonicalPlusJet rho) ^ 2 :=
    sq_pos_of_ne_zero hjetNe
  by_contra hhalf
  have hc : 0 < rho.re - (1 / 2 : ℝ) := by
    exact sub_pos.mpr (lt_of_not_ge hhalf)
  have harg : 0 < 2 * (rho.re - (1 / 2 : ℝ)) := by
    nlinarith
  have hscale : 1 < scale2 (2 * (rho.re - (1 / 2 : ℝ))) := by
    have hs := scale2_strictMono_proved harg
    rw [scale2_at_zero] at hs
    exact hs
  unfold canonicalPlusExactDefect at hdef
  nlinarith

/-- Reflection turns the one-sided plus bound into the full Mathlib RH. -/
theorem MATHLIB_RH_OF_ONE_PLUS_EXACT_TAIL_FRONTIER
    (hUpper : CanonicalPlusExactTailUpper) :
    RiemannHypothesis := by
  unfold RiemannHypothesis
  intro rho hzeta htrivial hneOne
  have hz : NontrivialZetaZero rho := ⟨hzeta, htrivial, hneOne⟩
  have hle : rho.re ≤ (1 / 2 : ℝ) :=
    re_le_half_of_canonicalPlusExactTailUpper hUpper rho hz
  have hzRef : NontrivialZetaZero (1 - rho) :=
    reflectedNontrivialZetaZero rho hz
  have hrefLe : (1 - rho : ℂ).re ≤ (1 / 2 : ℝ) :=
    re_le_half_of_canonicalPlusExactTailUpper hUpper (1 - rho) hzRef
  have hge : (1 / 2 : ℝ) ≤ rho.re := by
    simp at hrefLe
    linarith
  exact le_antisymm hle hge

/-- Conversely RH makes the one-sided upper bound automatic, because its exact
defect is zero and the canonical KQ tail is a square. -/
theorem canonicalPlusExactTailUpper_of_RH
    (hRH : RiemannHypothesis) : CanonicalPlusExactTailUpper := by
  intro n rho hz
  have hcrit : rho.re = (1 / 2 : ℝ) :=
    hRH rho hz.1 hz.2.1 hz.2.2
  have htail : 0 ≤ canonicalKQPlusSource n rho.re rho.im *
      canonicalKQPlusSource n rho.re rho.im := mul_self_nonneg _
  unfold canonicalPlusExactDefect
  simpa [hcrit, scale2] using htail

/-- At the canonical endpoint, the single remaining plus exact-to-tail bound is
logically equivalent to Mathlib's native Riemann Hypothesis. -/
theorem canonicalPlusExactTailUpper_iff_RiemannHypothesis :
    CanonicalPlusExactTailUpper ↔ RiemannHypothesis := by
  exact ⟨MATHLIB_RH_OF_ONE_PLUS_EXACT_TAIL_FRONTIER,
    canonicalPlusExactTailUpper_of_RH⟩

end AWPI.PhiRH.CanonicalOneSidedTail
