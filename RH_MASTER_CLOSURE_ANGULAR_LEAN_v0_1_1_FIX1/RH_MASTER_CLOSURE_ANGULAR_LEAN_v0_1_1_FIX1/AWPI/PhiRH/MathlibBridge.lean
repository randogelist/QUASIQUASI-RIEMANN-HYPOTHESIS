import AWPI.PhiRH.Split
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace AWPI.PhiRH.MathlibBridge

open AWPI.PhiRH

universe v
variable {Jet : Type v}
variable {M : Model ℂ Jet}

/-- The literal nontrivial-zero predicate occurring in Mathlib's
    `RiemannHypothesis` definition. This is a definition, not an assumption. -/
def NontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) ∧
    s ≠ 1

/-- Semantic leaf Z→: every abstract model zero is a genuine Mathlib
    nontrivial zero of the Riemann zeta function. -/
def ModelZeroImpliesNontrivialZetaZero (M : Model ℂ Jet) : Prop :=
  ∀ s : ℂ, M.isZero s → NontrivialZetaZero s

/-- Semantic leaf Z←: every genuine Mathlib nontrivial zeta zero is recognized
    by the abstract model's zero predicate. -/
def NontrivialZetaZeroImpliesModelZero (M : Model ℂ Jet) : Prop :=
  ∀ s : ℂ, NontrivialZetaZero s → M.isZero s

/-- Semantic leaf Re: the abstract model's real-coordinate observable is
    literally the complex real part used by Mathlib. -/
def ModelRePartIsComplexRe (M : Model ℂ Jet) : Prop :=
  ∀ s : ℂ, M.rePart s = s.re

/-- The former bundled semantic interface has been disassembled into
    three one-direction semantic leaves. -/
theorem modelRH_iff_mathlibRiemannHypothesis_of_semantic_leaves
    (modelZero_to_zetaZero : ModelZeroImpliesNontrivialZetaZero M)
    (zetaZero_to_modelZero : NontrivialZetaZeroImpliesModelZero M)
    (rePart_is_complexRe : ModelRePartIsComplexRe M) :
    M.RH ↔ RiemannHypothesis := by
  constructor
  · intro hModel
    unfold RiemannHypothesis
    intro s hz htrivial hne1
    have hzero : M.isZero s :=
      zetaZero_to_modelZero s ⟨hz, htrivial, hne1⟩
    have hcrit : M.criticalLine s := hModel s hzero
    unfold Model.criticalLine at hcrit
    rw [rePart_is_complexRe s] at hcrit
    exact hcrit
  · intro hMathlib
    intro s hzero
    have hz : NontrivialZetaZero s := modelZero_to_zetaZero s hzero
    unfold Model.criticalLine
    rw [rePart_is_complexRe s]
    exact hMathlib s hz.1 hz.2.1 hz.2.2

/-- Literal-Mathlib lift of PHIRH286 with the semantic bundle fully split into
    its three leaf obligations. -/
theorem PHIRH286_C_IMPLIES_MATHLIB_RIEMANN_HYPOTHESIS_SEMANTIC_LEAVES
    (modelZero_to_zetaZero : ModelZeroImpliesNontrivialZetaZero M)
    (zetaZero_to_modelZero : NontrivialZetaZeroImpliesModelZero M)
    (rePart_is_complexRe : ModelRePartIsComplexRe M)
    (v23 : NormalizedDyadicMultiplierFacts M)
    (scale : Scale2Facts M)
    (hC : Constructor M) : RiemannHypothesis := by
  apply (modelRH_iff_mathlibRiemannHypothesis_of_semantic_leaves
    modelZero_to_zetaZero zetaZero_to_modelZero rePart_is_complexRe).1
  exact Forward.PHIRH286_C_IMPLIES_RH v23 scale hC

/-- Guarded reverse theorem with only the three semantic leaves exposed. -/
theorem PHIRH287_BACKGROUND_AND_MATHLIB_RH_IMPLIES_C_SEMANTIC_LEAVES
    (modelZero_to_zetaZero : ModelZeroImpliesNontrivialZetaZero M)
    (zetaZero_to_modelZero : NontrivialZetaZeroImpliesModelZero M)
    (rePart_is_complexRe : ModelRePartIsComplexRe M)
    (hB : Background M)
    (hRH : RiemannHypothesis) : Constructor M := by
  apply Reverse.PHIRH287_BACKGROUND_AND_RH_IMPLIES_C hB
  exact (modelRH_iff_mathlibRiemannHypothesis_of_semantic_leaves
    modelZero_to_zetaZero zetaZero_to_modelZero rePart_is_complexRe).2 hRH

/-- Under the existing background package, Constructor is equivalent to
    Mathlib RH using only the three semantic leaf obligations. -/
theorem constructorIffMathlibRiemannHypothesisUnderBackground_semantic_leaves
    (modelZero_to_zetaZero : ModelZeroImpliesNontrivialZetaZero M)
    (zetaZero_to_modelZero : NontrivialZetaZeroImpliesModelZero M)
    (rePart_is_complexRe : ModelRePartIsComplexRe M)
    (v23 : NormalizedDyadicMultiplierFacts M)
    (scale : Scale2Facts M)
    (hB : Background M) :
    Constructor M ↔ RiemannHypothesis := by
  exact (constructorIffRHUnderBackground v23 scale hB).trans
    (modelRH_iff_mathlibRiemannHypothesis_of_semantic_leaves
      modelZero_to_zetaZero zetaZero_to_modelZero rePart_is_complexRe)

end AWPI.PhiRH.MathlibBridge
