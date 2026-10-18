import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import AngularRegularity.Geometry

/-!
# The angular derivative and its continuous formula

The chart is differentiated only for `-1 < x < 1`.  In particular, these
statements make no claim about the total derivative of the square-root
extension at either endpoint.  The formula contains no division by `f`, and
therefore remains valid at zeros of `f`.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace AngularRegularity

def angularDerivative (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  deriv (profile f r) x

def slopeFormula (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  2 / Real.sqrt (1 - x ^ 2) *
    (circlePoint r x * deriv f (circlePoint r x) *
      star (f (circlePoint r x))).im

/-- The real derivative of the circle chart, expressed in complex coordinates. -/
def circleVelocity (r x : ℝ) : ℂ :=
  (r : ℂ) * (1 + Complex.I * ((-x / Real.sqrt (1 - x ^ 2) : ℝ) : ℂ))

theorem hasDerivAt_circlePoint {r x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (circlePoint r) (circleVelocity r x) x := by
  have hinside := one_sub_sq_pos hx
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (sqrt_one_sub_sq_pos hx)
  have hu : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using! (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
    have hcoef : -(2 * x) / (2 * Real.sqrt (1 - x ^ 2)) =
        -x / Real.sqrt (1 - x ^ 2) := by
      field_simp [hsne]
      <;> ring
    simpa only [hcoef] using! hu.sqrt (ne_of_gt hinside)
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
    simpa using! (hasDerivAt_id x).ofReal_comp
  have hsc : HasDerivAt (fun y : ℝ => (Real.sqrt (1 - y ^ 2) : ℂ))
      ((-x / Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) x := hs.ofReal_comp
  simpa only [circlePoint, circleVelocity] using!
    (hid.add (hsc.const_mul Complex.I)).const_mul (r : ℂ)

/-- Interior differentiability of the profile needs only differentiability
of `f` at the represented point. -/
theorem hasDerivAt_profile {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (profile f r) (slopeFormula f r x) x := by
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (sqrt_one_sub_sq_pos hx)
  have hc : HasDerivAt (fun y : ℝ => f (circlePoint r y))
      (deriv f (circlePoint r x) * circleVelocity r x) x :=
    hf.hasDerivAt.comp x (hasDerivAt_circlePoint hx)
  have hre : HasDerivAt (fun y : ℝ => (f (circlePoint r y)).re)
      (deriv f (circlePoint r x) * circleVelocity r x).re x := by
    simpa only [Function.comp_apply, Complex.reCLM_apply] using!
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hc)
  have him : HasDerivAt (fun y : ℝ => (f (circlePoint r y)).im)
      (deriv f (circlePoint r x) * circleVelocity r x).im x := by
    simpa only [Function.comp_apply, Complex.imCLM_apply] using!
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hc)
  -- Compare real coefficients separately from the derivative structures.
  have hcoef : slopeFormula f r x =
      ((deriv f (circlePoint r x) * circleVelocity r x).re *
          (f (circlePoint r x)).re +
        (f (circlePoint r x)).re *
          (deriv f (circlePoint r x) * circleVelocity r x).re) +
      ((deriv f (circlePoint r x) * circleVelocity r x).im *
          (f (circlePoint r x)).im +
        (f (circlePoint r x)).im *
          (deriv f (circlePoint r x) * circleVelocity r x).im) := by
    simp only [slopeFormula, circleVelocity, circlePoint, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.one_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    field_simp [hsne]
    <;> ring
  rw [hcoef]
  simpa only [profile, Complex.normSq_apply, Pi.add_apply, Pi.mul_apply] using!
    (hre.mul hre).add (him.mul him)

theorem angularDerivative_eq_slopeFormula {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    angularDerivative f r x = slopeFormula f r x :=
  (hasDerivAt_profile hf hx).deriv

theorem differentiableAt_profile {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (profile f r) x :=
  (hasDerivAt_profile hf hx).differentiableAt

theorem angularDerivative_eq_zero_of_value_eq_zero {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hz : f (circlePoint r x) = 0) : angularDerivative f r x = 0 := by
  rw [angularDerivative_eq_slopeFormula hf hx]
  simp [slopeFormula, hz]

theorem angularDerivative_eq_zero_of_profile_eq_zero {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hz : profile f r x = 0) : angularDerivative f r x = 0 :=
  angularDerivative_eq_zero_of_value_eq_zero hf hx
    ((profile_eq_zero_iff f r x).1 hz)

theorem profile_pos_of_angularDerivative_ne_zero {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : angularDerivative f r x ≠ 0) : 0 < profile f r x := by
  apply lt_of_le_of_ne (profile_nonnegative f r x)
  intro hz
  exact hd (angularDerivative_eq_zero_of_profile_eq_zero hf hx hz.symm)

/-- Interoperability with interval-restricted derivatives at interior points.
There is deliberately no claim at the two endpoints. -/
theorem derivWithin_profile_Icc_eq_angularDerivative (f : ℂ → ℂ) (r : ℝ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    derivWithin (profile f r) (Set.Icc (-1 : ℝ) 1) x =
      angularDerivative f r x :=
  derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- The explicit formula is jointly continuous on the open angular domain.
The derivative of `f` is an explicit continuity input in this generic lemma. -/
theorem continuousOn_slopeFormula {f : ℂ → ℂ}
    (hf : Continuous f) (hdf : Continuous (deriv f)) :
    ContinuousOn (fun p : ℝ × ℝ => slopeFormula f p.1 p.2) domain := by
  have hc := continuous_circlePoint_joint
  have hn : Continuous (fun p : ℝ × ℝ =>
      (circlePoint p.1 p.2 * deriv f (circlePoint p.1 p.2) *
        star (f (circlePoint p.1 p.2))).im) := by
    fun_prop
  intro p hp
  have hs : ContinuousAt (fun q : ℝ × ℝ => Real.sqrt (1 - q.2 ^ 2)) p := by
    fun_prop
  have hsne : Real.sqrt (1 - p.2 ^ 2) ≠ 0 :=
    ne_of_gt (sqrt_one_sub_sq_pos hp.2)
  exact ((continuousAt_const.div hs hsne).mul hn.continuousAt).continuousWithinAt

/-- Entire complex differentiability supplies continuity of the complex
derivative; no convergence or positivity premise is present. -/
theorem continuousOn_angularDerivative {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    ContinuousOn (fun p : ℝ × ℝ => angularDerivative f p.1 p.2) domain := by
  apply (continuousOn_slopeFormula hf.continuous hf.deriv.continuous).congr
  intro p hp
  exact angularDerivative_eq_slopeFormula (hf (circlePoint p.1 p.2)) hp.2

end AngularRegularity
