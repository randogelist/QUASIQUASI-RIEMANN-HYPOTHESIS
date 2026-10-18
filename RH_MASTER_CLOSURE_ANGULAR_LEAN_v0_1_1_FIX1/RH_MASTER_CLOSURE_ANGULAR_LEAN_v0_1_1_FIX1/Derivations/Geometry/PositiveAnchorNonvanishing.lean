import Core.MathlibXiSlitTheta
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace NativeSolobolo.Derivations.Geometry

open NativeSolobolo
open Complex
open scoped ComplexOrder

/--
!!! Mathlib's nonvanishing theorem for zeta on `re s ≥ 1` transfers to the
literal entire xi normalization used by this project.

The point `s = 1` is handled directly from the entire definition of xi; away
from `1`, a zero of xi forces a zero of zeta through mathlib's exact
`riemannZeta_eq_mul_completedRiemannZeta₀` identity.
-/
theorem MATHLIB_XI_NE_ZERO_OF_ONE_LE_RE
    {s : ℂ} (hs : 1 ≤ s.re) :
    mathlibXi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    norm_num [mathlibXi]
  · have hzeta : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re hs
    intro hxi
    apply hzeta
    rw [riemannZeta_eq_mul_completedRiemannZeta₀]
    have hraw :
        1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
      simpa [mathlibXi] using hxi
    have h1ms : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hnum :
        s * completedRiemannZeta₀ s - 1 - s / (1 - s) = 0 := by
      calc
        s * completedRiemannZeta₀ s - 1 - s / (1 - s)
            = -(1 + s * (s - 1) * completedRiemannZeta₀ s) / (1 - s) := by
                field_simp [h1ms]
                ring
        _ = 0 := by rw [hraw]; simp
    rw [hnum]
    simp

/--
!! On the centered real ray, every point `w ≥ 1/2` is zero-free for the actual
mathlib xi core.
-/
theorem MATHLIB_CENTERED_XI_NE_ZERO_REAL_GE_HALF
    {w : ℝ} (hw : (1 / 2 : ℝ) ≤ w) :
    mathlibCenteredXi (w : ℂ) ≠ 0 := by
  unfold mathlibCenteredXi
  apply MATHLIB_XI_NE_ZERO_OF_ONE_LE_RE
  norm_num
  linarith

/--
!!! Every positive slit-theta anchor `a ≥ 1/4` is zero-free.  Thus the only
remaining positive-axis nonvanishing leaf for the local Cayley jet lies on the
compact interval `0 < a < 1/4`.
-/
theorem MATHLIB_SLIT_THETA_NE_ZERO_ANCHOR_GE_QUARTER
    {a : ℝ}
    (ha : PositiveAnchor a)
    (haq : (1 / 4 : ℝ) ≤ a) :
    mathlibSlitTheta (a : ℂ) ≠ 0 := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    norm_num at ⊢
    exact haq
  have hcenter : mathlibCenteredXi ((Real.sqrt a : ℝ) : ℂ) ≠ 0 :=
    MATHLIB_CENTERED_XI_NE_ZERO_REAL_GE_HALF hsqrt
  have hca : (0 : ℂ) ≤ (a : ℂ) := by
    exact ⟨ha0, by simp⟩
  have hsqrtC : Complex.sqrt (a : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
    simpa using (Complex.sqrt_of_nonneg hca)
  simpa [mathlibSlitTheta, hsqrtC] using hcenter

/--
!! Full positive-anchor nonvanishing is reduced to the compact interval below
`1/4`.
-/
theorem MATHLIB_SLIT_THETA_POSITIVE_ANCHOR_NONVANISHING_REDUCED_TO_LT_QUARTER
    (hcompact : ∀ a : ℝ,
      PositiveAnchor a → a < (1 / 4 : ℝ) → mathlibSlitTheta (a : ℂ) ≠ 0) :
    ∀ a : ℝ, PositiveAnchor a → mathlibSlitTheta (a : ℂ) ≠ 0 := by
  intro a ha
  by_cases hq : a < (1 / 4 : ℝ)
  · exact hcompact a ha hq
  · exact MATHLIB_SLIT_THETA_NE_ZERO_ANCHOR_GE_QUARTER ha (le_of_not_gt hq)

end NativeSolobolo.Derivations.Geometry
