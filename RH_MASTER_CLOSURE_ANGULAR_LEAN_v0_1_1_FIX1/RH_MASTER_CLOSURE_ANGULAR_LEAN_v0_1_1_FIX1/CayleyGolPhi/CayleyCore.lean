import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.SqrtDeriv

namespace CayleyGolPhi

open Complex

/-- Actual completed Riemann xi, built only from Mathlib's entire pole-removed completion. -/
noncomputable def mathlibXi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- The actual xi normalization is entire. -/
theorem MATHLIB_XI_DIFFERENTIABLE : Differentiable ℂ mathlibXi := by
  intro s
  have hL : DifferentiableAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀ s
  unfold mathlibXi
  fun_prop

/-- Functional equation xi(1-s)=xi(s), derived from Mathlib Lambda_0. -/
theorem MATHLIB_XI_ONE_SUB (s : ℂ) :
    mathlibXi (1 - s) = mathlibXi s := by
  unfold mathlibXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Centered xi: H(w)=xi(1/2+w). -/
noncomputable def centeredXi (w : ℂ) : ℂ :=
  mathlibXi ((1 / 2 : ℂ) + w)

/-- The centered xi function is entire. -/
theorem CENTERED_XI_DIFFERENTIABLE : Differentiable ℂ centeredXi := by
  intro w
  unfold centeredXi
  exact (MATHLIB_XI_DIFFERENTIABLE ((1 / 2 : ℂ) + w)).comp w (by fun_prop)

/-- Centering turns xi reflection into literal evenness. -/
theorem CENTERED_XI_EVEN (w : ℂ) : centeredXi (-w) = centeredXi w := by
  unfold centeredXi
  have h := MATHLIB_XI_ONE_SUB ((1 / 2 : ℂ) + w)
  convert h using 1 <;> ring

/-- Actual centered theta on the principal-sqrt slit plane. -/
noncomputable def slitTheta (z : ℂ) : ℂ := centeredXi (Complex.sqrt z)

/-- The actual slit theta is analytic on the slit plane. -/
theorem SLIT_THETA_DIFFERENTIABLE_ON :
    DifferentiableOn ℂ slitTheta Complex.slitPlane := by
  intro z hz
  unfold slitTheta
  exact ((CENTERED_XI_DIFFERENTIABLE (Complex.sqrt z)).comp z
    (Complex.differentiableAt_sqrt hz)).differentiableWithinAt

/-- Positive Cayley anchor. -/
def PositiveAnchor (a : ℝ) : Prop := 0 < a

/-- Interior Cayley radius. -/
def InteriorRadius (r : ℝ) : Prop := 0 < r ∧ r < 1

/-- Positive imaginary magnitude of the conjugate Cayley pair. -/
noncomputable def cayleyImagMagnitude (a r : ℝ) : ℝ :=
  2 * Real.sqrt ((a * r) * (a * (1 - r)))

/-- Upper Cayley point. -/
noncomputable def cayleyPointPlus (a r : ℝ) : ℂ :=
  Complex.mk (a * (1 - 2 * r)) (cayleyImagMagnitude a r)

/-- Lower Cayley point. -/
noncomputable def cayleyPointMinus (a r : ℝ) : ℂ :=
  Complex.mk (a * (1 - 2 * r)) (-cayleyImagMagnitude a r)

/-- Exact metric gauge r = sin^2(eta/2). -/
noncomputable def cayleyRadiusAtMetricDepth (eta : ℝ) : ℝ :=
  (Real.sin (eta / 2)) ^ 2

/-- Literal derivative used in the actual logarithmic derivative. -/
noncomputable def slitThetaPrime (z : ℂ) : ℂ := deriv slitTheta z

/--
The stripped actual Cayley observable. It is `none` exactly when at least one
Cayley denominator is a literal theta zero; otherwise it is the dual
logarithmic-derivative Cayley value.
-/
noncomputable def actualCayleyObservable (a r : ℝ) : Option ℂ :=
  let zp := cayleyPointPlus a r
  let zm := cayleyPointMinus a r
  if hzero : slitTheta zp = 0 ∨ slitTheta zm = 0 then
    none
  else
    let Rp := slitThetaPrime zp / slitTheta zp
    let Rm := slitThetaPrime zm / slitTheta zm
    some ((4 * (a : ℂ)) * ((zm * Rm - zp * Rp) / (zm - zp)))

end CayleyGolPhi
