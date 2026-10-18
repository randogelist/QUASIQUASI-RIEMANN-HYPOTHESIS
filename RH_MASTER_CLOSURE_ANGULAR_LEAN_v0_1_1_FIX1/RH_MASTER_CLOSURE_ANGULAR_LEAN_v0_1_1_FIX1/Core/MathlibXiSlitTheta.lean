import Core.ActualThetaCayley
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.SqrtDeriv

namespace NativeSolobolo

open Complex

/--
!!! Actual completed Riemann xi built from mathlib's entire pole-removed
completed zeta Lambda_0.

Since
  Lambda = Lambda_0 - 1/s - 1/(1-s),
the classical xi normalization is
  xi(s) = (1 + s(s-1)Lambda_0(s))/2.
This definition is entire without assigning special cases at 0 or 1.
-/
noncomputable def mathlibXi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- !!! The actual mathlib xi normalization is entire. -/
theorem MATHLIB_XI_DIFFERENTIABLE : Differentiable ℂ mathlibXi := by
  intro s
  have hL : DifferentiableAt ℂ completedRiemannZeta₀ s :=
    differentiable_completedZeta₀ s
  unfold mathlibXi
  fun_prop

/-- !!! Functional equation xi(1-s)=xi(s), derived from mathlib Lambda_0. -/
theorem MATHLIB_XI_ONE_SUB (s : ℂ) :
    mathlibXi (1 - s) = mathlibXi s := by
  unfold mathlibXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- The centered actual xi function H(w)=xi(1/2+w). -/
noncomputable def mathlibCenteredXi (w : ℂ) : ℂ :=
  mathlibXi ((1 / 2 : ℂ) + w)

/-- !! The centered actual xi function is entire. -/
theorem MATHLIB_CENTERED_XI_DIFFERENTIABLE :
    Differentiable ℂ mathlibCenteredXi := by
  intro w
  unfold mathlibCenteredXi
  exact (MATHLIB_XI_DIFFERENTIABLE ((1 / 2 : ℂ) + w)).comp w
    (by fun_prop)

/-- !!! Centering turns the functional equation into literal evenness. -/
theorem MATHLIB_CENTERED_XI_EVEN (w : ℂ) :
    mathlibCenteredXi (-w) = mathlibCenteredXi w := by
  unfold mathlibCenteredXi
  have h := MATHLIB_XI_ONE_SUB ((1 / 2 : ℂ) + w)
  convert h using 1 <;> ring

/--
Actual centered theta on the slit plane.  Global branch independence follows
from the evenness of centered xi; for every strict sub-pi Cayley point the
principal square root is already the canonical local branch.
-/
noncomputable def mathlibSlitTheta (z : ℂ) : ℂ :=
  mathlibCenteredXi (Complex.sqrt z)

/-- !! The actual slit-theta is complex differentiable on the slit plane. -/
theorem MATHLIB_SLIT_THETA_DIFFERENTIABLE_ON :
    DifferentiableOn ℂ mathlibSlitTheta Complex.slitPlane := by
  intro z hz
  unfold mathlibSlitTheta
  exact ((MATHLIB_CENTERED_XI_DIFFERENTIABLE (Complex.sqrt z)).comp z
    (Complex.differentiableAt_sqrt hz)).differentiableWithinAt

/-- !!! Hence the actual slit-theta is analytic on a neighborhood of every slit-plane point. -/
theorem MATHLIB_SLIT_THETA_ANALYTIC_ON_NHD :
    AnalyticOnNhd ℂ mathlibSlitTheta Complex.slitPlane :=
  MATHLIB_SLIT_THETA_DIFFERENTIABLE_ON.analyticOnNhd Complex.isOpen_slitPlane

/-- Positive Cayley anchors lie in the slit plane. -/
theorem POSITIVE_ANCHOR_MEM_SLIT_PLANE
    {a : ℝ} (ha : PositiveAnchor a) :
    (a : ℂ) ∈ Complex.slitPlane := by
  simpa [PositiveAnchor] using ha

/--
!! Every strict interior Cayley pair at a positive anchor lies in the slit
plane.  Thus the actual theta model above is analytic at every point used by a
strict sub-pi Cayley observable.
-/
theorem CAYLEY_PAIR_MEM_SLIT_PLANE
    {a r : ℝ}
    (ha : PositiveAnchor a)
    (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    cayleyPointPlus a r ∈ Complex.slitPlane ∧
      cayleyPointMinus a r ∈ Complex.slitPlane := by
  have ha0 : 0 < a := ha
  by_cases hrz : r = 0
  · subst r
    constructor <;> simp [cayleyPointPlus, cayleyPointMinus, Complex.mem_slitPlane_iff, ha0]
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
    have h1r : 0 < 1 - r := sub_pos.mpr hr1
    have hinside : 0 < (a * r) * (a * (1 - r)) := by positivity
    have himag : 0 < cayleyImagMagnitude a r := by
      unfold cayleyImagMagnitude
      have hsqrt : 0 < Real.sqrt ((a * r) * (a * (1 - r))) :=
        Real.sqrt_pos.2 hinside
      positivity
    constructor
    · rw [Complex.mem_slitPlane_iff]
      right
      simp [cayleyPointPlus, ne_of_gt himag]
    · rw [Complex.mem_slitPlane_iff]
      right
      simp [cayleyPointMinus, ne_of_lt (neg_neg_of_pos himag)]

/-- The literal derivative used for the actual slit-theta logarithmic derivative. -/
noncomputable def mathlibSlitThetaPrime (z : ℂ) : ℂ :=
  deriv mathlibSlitTheta z


/--
!! Actual centered-theta data with the derivative fixed literally to `deriv`.
Only the zero-binding proof is supplied by the chosen centered-zero geometry;
there is no free `thetaPrime` field left in this instantiation.
-/
noncomputable def mathlibSlitThetaData
    (X : CenteredXiGeometry)
    (hzero : ∀ z : X.Zero, mathlibSlitTheta (X.thetaZeroPoint z) = 0) :
    CenteredThetaData where
  geometry := X
  theta := mathlibSlitTheta
  thetaPrime := mathlibSlitThetaPrime
  theta_zero := hzero

/-- !!! In the actual slit-theta data, thetaPrime is definitionally the complex derivative. -/
theorem MATHLIB_SLIT_THETA_DATA_PRIME_IS_DERIV
    (X : CenteredXiGeometry)
    (hzero : ∀ z : X.Zero, mathlibSlitTheta (X.thetaZeroPoint z) = 0)
    (z : ℂ) :
    (mathlibSlitThetaData X hzero).thetaPrime z = deriv mathlibSlitTheta z := rfl

end NativeSolobolo
