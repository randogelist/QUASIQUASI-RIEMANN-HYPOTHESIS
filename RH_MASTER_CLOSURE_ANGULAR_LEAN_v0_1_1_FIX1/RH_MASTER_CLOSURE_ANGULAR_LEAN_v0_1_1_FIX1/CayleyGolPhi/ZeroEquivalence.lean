import CayleyGolPhi.GolPhiSlice
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace CayleyGolPhi

open Complex
open scoped Real

/--
The standard zero-free half-plane on the left after excluding the trivial
negative-even zeta zeros. This proof is copied down to the stripped package
from the already compiled AWPI zeta-strip actualization layer.
-/
theorem NONTRIVIAL_ZETA_NE_ZERO_OF_RE_LE_ZERO {s : ℂ}
    (hs : s.re ≤ 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) :
    riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero]
    norm_num
  · have hw_re : 1 ≤ (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hw_nat : ∀ n : ℕ, (1 : ℂ) - s ≠ -n := by
      intro n h
      have hreal := congrArg Complex.re h
      rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hreal
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hw_ne_one : (1 : ℂ) - s ≠ 1 := fun h => hs0 (by linear_combination -h)
    have hFE := riemannZeta_one_sub hw_nat hw_ne_one
    rw [show (1 : ℂ) - (1 - s) = s by ring] at hFE
    rw [hFE]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) ?_) ?_
    · exact Complex.cpow_ne_zero_iff.mpr
        (Or.inl (mul_ne_zero two_ne_zero
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · exact Complex.Gamma_ne_zero_of_re_pos (one_pos.trans_le hw_re)
    · intro hcos
      obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
      have hpi : (π : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have h2 : (π : ℂ) * (1 - s) = (2 * (k : ℂ) + 1) * (π : ℂ) := by
        linear_combination 2 * hk
      have h3 : (1 : ℂ) - s = 2 * (k : ℂ) + 1 :=
        mul_left_cancel₀ hpi (by linear_combination h2)
      have hs_eq : s = -2 * (k : ℂ) := by
        linear_combination -h3
      have hk_re : s.re = -2 * (k : ℝ) := by
        rw [hs_eq]
        simp [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
      have hk0 : 0 ≤ k := by
        by_contra hneg
        push_neg at hneg
        have hkR : (k : ℝ) < 0 := by exact_mod_cast hneg
        have hpos : (0 : ℝ) < s.re := by
          rw [hk_re]
          nlinarith
        linarith
      have hkne : k ≠ 0 := by
        rintro rfl
        exact hs0 (by simpa using hs_eq)
      have hk1 : 1 ≤ k := by omega
      refine htriv ⟨(k - 1).toNat, ?_⟩
      rw [hs_eq, show ((((k - 1).toNat : ℕ) : ℂ)) = (k : ℂ) - 1 by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - 1)]
        push_cast
        ring]
      ring
    · exact riemannZeta_ne_zero_of_one_le_re hw_re

/-- Every Mathlib nontrivial zeta zero lies in the open critical strip. -/
theorem NONTRIVIAL_ZETA_ZERO_MEM_CRITICAL_STRIP {s : ℂ}
    (hz : NontrivialZetaZero s) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    exact NONTRIVIAL_ZETA_NE_ZERO_OF_RE_LE_ZERO
      (not_lt.mp h) hz.2.1 hz.1
  · by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz.1

/-- Points in the open critical strip are not the pole point s=1. -/
theorem CRITICAL_STRIP_NE_ONE {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) : s ≠ 1 := by
  intro h
  subst s
  norm_num at hs

/-- Points in the open critical strip are not negative-even trivial zeros. -/
theorem CRITICAL_STRIP_NOT_TRIVIAL {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  rintro ⟨n, hn⟩
  have hre := congrArg Complex.re hn
  simp [Complex.mul_re] at hre
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Gamma completion factor is nonzero throughout the open critical strip. -/
theorem GAMMA_HALF_ADD_ONE_NE_ZERO_OF_CRITICAL_STRIP {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    Complex.Gamma (s / 2 + 1) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  have : 0 < (s / 2 + 1).re := by
    simp
    linarith [hs.1]
  exact this

/-- The pi complex-power factor in the zeta/xi completion never vanishes. -/
theorem PI_CPOW_NE_ZERO (s : ℂ) :
    (Real.pi : ℂ) ^ s ≠ 0 := by
  exact Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

/--
Exact algebraic relation between zeta and the entire completed GolPhi slice.
No RH premise is used.
-/
theorem RIEMANN_ZETA_EQ_COMPLETED_GOLPHI_DIV
    {s : ℂ} (hs1 : s ≠ 1) :
    riemannZeta s =
      completedGolPhiS1 s /
        ((s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))) := by
  rw [riemannZeta_eq_mul_completedRiemannZeta₀]
  have h1ms : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsm1 : s - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hs1
  have hnum :
      s * completedRiemannZeta₀ s - 1 - s / (1 - s) =
        (1 + s * (s - 1) * completedRiemannZeta₀ s) / (s - 1) := by
    field_simp [h1ms, hsm1]
    ring
  rw [hnum]
  unfold completedGolPhiS1
  rw [div_div, div_div]
  congr 1
  ring

/-- The standard completion weight relating zeta to the completed GolPhi slice. -/
noncomputable def golPhiCompletionWeight (s : ℂ) : ℂ :=
  (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))

/-- On Re(s)>1, the completed GolPhi slice is the usual zeta completion weight times zeta. -/
theorem COMPLETED_GOLPHI_EQ_COMPLETION_WEIGHT_MUL_ZETA
    {s : ℂ} (hs : 1 < s.re) :
    completedGolPhiS1 s = golPhiCompletionWeight s * riemannZeta s := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hgamma : Complex.Gamma (s / 2 + 1) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    have : 0 < (s / 2 + 1).re := by
      simp
      linarith
    exact this
  have hD : golPhiCompletionWeight s ≠ 0 := by
    unfold golPhiCompletionWeight
    apply mul_ne_zero
    · exact sub_ne_zero.mpr hs1
    · exact mul_ne_zero (PI_CPOW_NE_ZERO (-s / 2)) hgamma
  have hrel :
      riemannZeta s = completedGolPhiS1 s / golPhiCompletionWeight s := by
    simpa [golPhiCompletionWeight] using RIEMANN_ZETA_EQ_COMPLETED_GOLPHI_DIV hs1
  calc
    completedGolPhiS1 s =
        (completedGolPhiS1 s / golPhiCompletionWeight s) * golPhiCompletionWeight s := by
          exact (div_mul_cancel₀ _ hD).symm
    _ = riemannZeta s * golPhiCompletionWeight s := by rw [← hrel]
    _ = golPhiCompletionWeight s * riemannZeta s := by ring

/--
The raw canonical u=1 GolPhi series and the entire completed GolPhi slice obey
the exact completion cross-identity on Re(s)>1.  This is the rigorous bridge
showing that `completedGolPhiS1` is a completion of the canonical GolPhi slice,
not merely a renamed xi.
-/
theorem GOLPHI_RAW_TO_COMPLETED_CROSS_IDENTITY
    {s : ℂ} (hs : 1 < s.re) :
    golPhiCompletionWeight s * golPhi 1 s =
      golPhiS1Prefactor s * completedGolPhiS1 s := by
  rw [GOLPHI_AT_ONE_EQ_PREFACTOR_MUL_ZETA hs]
  rw [COMPLETED_GOLPHI_EQ_COMPLETION_WEIGHT_MUL_ZETA hs]
  ring

/-- Full zeta/completed-GolPhi denominator is nonzero in the critical strip. -/
theorem COMPLETED_GOLPHI_ZETA_DENOMINATOR_NE_ZERO_OF_CRITICAL_STRIP
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    ((s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))) ≠ 0 := by
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (CRITICAL_STRIP_NE_ONE hs)
  · apply mul_ne_zero
    · exact PI_CPOW_NE_ZERO (-s / 2)
    · exact GAMMA_HALF_ADD_ONE_NE_ZERO_OF_CRITICAL_STRIP hs

/--
Inside the open critical strip, zeros of completed GolPhi are exactly zeros of
zeta. This is the exact zero-set identification needed for RH.
-/
theorem COMPLETED_GOLPHI_ZERO_IFF_ZETA_ZERO_OF_CRITICAL_STRIP
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    completedGolPhiS1 s = 0 ↔ riemannZeta s = 0 := by
  let D : ℂ :=
    (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1))
  have hD : D ≠ 0 := by
    dsimp [D]
    exact COMPLETED_GOLPHI_ZETA_DENOMINATOR_NE_ZERO_OF_CRITICAL_STRIP hs
  have hrel : riemannZeta s = completedGolPhiS1 s / D := by
    simpa [D] using RIEMANN_ZETA_EQ_COMPLETED_GOLPHI_DIV (CRITICAL_STRIP_NE_ONE hs)
  constructor
  · intro hG
    rw [hrel, hG]
    simp
  · intro hz
    have hq : completedGolPhiS1 s / D = 0 := by
      rw [← hrel]
      exact hz
    calc
      completedGolPhiS1 s = (completedGolPhiS1 s / D) * D := by
        exact (div_mul_cancel₀ _ hD).symm
      _ = 0 := by rw [hq]; simp

/--
The stripped Cayley observable is undefined exactly when one of its two Cayley
points maps to a completed-GolPhi zero.  This is a direct object-level bridge,
not an RH-mediated equivalence.
-/
theorem ACTUAL_CAYLEY_OBSERVABLE_NONE_IFF_COMPLETED_GOLPHI_ZERO
    (a r : ℝ) :
    actualCayleyObservable a r = none ↔
      completedGolPhiS1
          ((1 / 2 : ℂ) + Complex.sqrt (cayleyPointPlus a r)) = 0 ∨
      completedGolPhiS1
          ((1 / 2 : ℂ) + Complex.sqrt (cayleyPointMinus a r)) = 0 := by
  change actualCayleyObservable a r = none ↔
    slitTheta (cayleyPointPlus a r) = 0 ∨
      slitTheta (cayleyPointMinus a r) = 0
  by_cases hp : slitTheta (cayleyPointPlus a r) = 0
  · simp [actualCayleyObservable, hp]
  · by_cases hm : slitTheta (cayleyPointMinus a r) = 0
    · simp [actualCayleyObservable, hp, hm]
    · simp [actualCayleyObservable, hp, hm]

/--
A nontrivial GolPhi zero is a zero of the entire completed u=1 GolPhi slice
lying in the open critical strip. This avoids the raw eta-prefactor lattice and
matches the classical nontrivial-zeta-zero notion exactly.
-/
def NontrivialGolPhiZero (s : ℂ) : Prop :=
  completedGolPhiS1 s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- Exact equality of the nontrivial completed-GolPhi and zeta zero predicates. -/
theorem NONTRIVIAL_GOLPHI_ZERO_IFF_NONTRIVIAL_ZETA_ZERO (s : ℂ) :
    NontrivialGolPhiZero s ↔ NontrivialZetaZero s := by
  constructor
  · intro hG
    have hs : 0 < s.re ∧ s.re < 1 := ⟨hG.2.1, hG.2.2⟩
    refine ⟨?_, CRITICAL_STRIP_NOT_TRIVIAL hs, CRITICAL_STRIP_NE_ONE hs⟩
    exact (COMPLETED_GOLPHI_ZERO_IFF_ZETA_ZERO_OF_CRITICAL_STRIP hs).1 hG.1
  · intro hz
    have hs : 0 < s.re ∧ s.re < 1 := NONTRIVIAL_ZETA_ZERO_MEM_CRITICAL_STRIP hz
    refine ⟨?_, hs.1, hs.2⟩
    exact (COMPLETED_GOLPHI_ZERO_IFF_ZETA_ZERO_OF_CRITICAL_STRIP hs).2 hz.1

/-- RH stated purely as a condition on nontrivial zeros of completed GolPhi. -/
def GolPhiRiemannHypothesis : Prop :=
  ∀ s : ℂ, NontrivialGolPhiZero s → s.re = 1 / 2

/--
Main theorem: the nontrivial-zero statement for completed GolPhi is exactly
Mathlib's Riemann Hypothesis.
-/
theorem GOLPHI_RH_IFF_MATHLIB_RH :
    GolPhiRiemannHypothesis ↔ _root_.RiemannHypothesis := by
  constructor
  · intro hG
    unfold _root_.RiemannHypothesis
    intro s hz htriv hs1
    apply hG s
    exact (NONTRIVIAL_GOLPHI_ZERO_IFF_NONTRIVIAL_ZETA_ZERO s).2
      ⟨hz, htriv, hs1⟩
  · intro hRH
    intro s hG
    have hz : NontrivialZetaZero s :=
      (NONTRIVIAL_GOLPHI_ZERO_IFF_NONTRIVIAL_ZETA_ZERO s).1 hG
    exact hRH s hz.1 hz.2.1 hz.2.2

/-- Centered form: all nontrivial completed-GolPhi zeros have zero centered real part. -/
def CenteredGolPhiRiemannHypothesis : Prop :=
  ∀ s : ℂ, NontrivialGolPhiZero s → (s - (1 / 2 : ℂ)).re = 0

/-- Centered GolPhi zero statement is again exactly RH. -/
theorem CENTERED_GOLPHI_RH_IFF_MATHLIB_RH :
    CenteredGolPhiRiemannHypothesis ↔ _root_.RiemannHypothesis := by
  constructor
  · intro hC
    apply GOLPHI_RH_IFF_MATHLIB_RH.mp
    intro s hs
    have h := hC s hs
    simp at h
    linarith
  · intro hRH s hs
    have hline := (GOLPHI_RH_IFF_MATHLIB_RH.mpr hRH) s hs
    simp
    linarith

end CayleyGolPhi
