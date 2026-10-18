import AngularRegularity.Calculus

/-!
# The actual angular derivative and its stationary equation

The derivative is derived by the chain rule.  The pointwise hypothesis
`HasDerivAt f f' z` is an ordinary complex differentiability hypothesis, not a
supplied equality for the real profile derivative.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace AngularRegularity

/-- Angular velocity in unsimplified real-square-root coordinates. -/
def circleVelocity (r x : ℝ) : ℂ :=
  (r : ℂ) * (1 + Complex.I * ((-x / Real.sqrt (1 - x ^ 2) : ℝ) : ℂ))

/-- Chain-rule derivative of the semicircle parametrization. -/
theorem circlePoint_hasDerivAt {r x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (circlePoint r) (circleVelocity r x) x := by
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (sqrtArgument_pos hx))
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using! (hasDerivAt_pow 2 x)
    have harg : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x :=
      HasDerivAt.const_sub (1 : ℝ) hsq
    have hsraw := harg.sqrt (sqrtArgument_ne_zero hx)
    have hcoef : -(2 * x) / (2 * Real.sqrt (1 - x ^ 2)) =
        -x / Real.sqrt (1 - x ^ 2) := by
      field_simp [hs0]
      <;> ring
    rw [hcoef] at hsraw
    exact hsraw
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x :=
    (hasDerivAt_id x).ofReal_comp
  have hsC : HasDerivAt
      (fun y : ℝ => (Real.sqrt (1 - y ^ 2) : ℂ))
      ((-x / Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) x :=
    hs.ofReal_comp
  change HasDerivAt
    (fun y : ℝ => (r : ℂ) * ((y : ℂ) + Complex.I * (Real.sqrt (1 - y ^ 2) : ℂ)))
    ((r : ℂ) * (1 + Complex.I * ((-x / Real.sqrt (1 - x ^ 2) : ℝ) : ℂ))) x
  exact (hc.add (hsC.const_mul Complex.I)).const_mul (r : ℂ)

/-- Derivative of the squared modulus of a complex-valued real curve. -/
theorem hasDerivAt_normSq_curve {F : ℝ → ℂ} {w : ℂ} {x : ℝ}
    (hF : HasDerivAt F w x) :
    HasDerivAt (fun y => Complex.normSq (F y))
      (2 * (w * star (F x)).re) x := by
  have hnorm : (fun y => Complex.normSq (F y)) = (fun y => ‖F y‖ ^ 2) := by
    funext y
    exact Complex.normSq_eq_norm_sq _
  have hinner : Inner.inner ℝ (F x) w = (w * star (F x)).re :=
    Complex.inner (F x) w
  rw [hnorm, ← hinner]
  exact hF.norm_sq

/-- Exact derivative with the geometric velocity left explicit. -/
theorem profile_hasDerivAt {f : ℂ → ℂ} {f' : ℂ} {r x : ℝ}
    (hf : HasDerivAt f f' (circlePoint r x))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (profile f r)
      (2 * (f' * circleVelocity r x * star (f (circlePoint r x))).re) x := by
  have hF : HasDerivAt (fun y => f (circlePoint r y))
      (f' * circleVelocity r x) x :=
    hf.comp x (circlePoint_hasDerivAt hx)
  exact hasDerivAt_normSq_curve hF

theorem angularSlope_eq_re {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    angularSlope f r x =
      2 * (deriv f (circlePoint r x) * circleVelocity r x *
        star (f (circlePoint r x))).re :=
  (profile_hasDerivAt hf.hasDerivAt hx).deriv

/-- A zero of the original analytic function is angular-stationary. -/
theorem angularSlope_eq_zero_of_zero {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hz : f (circlePoint r x) = 0) :
    angularSlope f r x = 0 := by
  rw [angularSlope_eq_re hf hx, hz]
  simp

/-- Exact stationary equation, with no division by the profile. -/
theorem angularSlope_eq_zero_iff_re {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    angularSlope f r x = 0 ↔
      (deriv f (circlePoint r x) * circleVelocity r x *
        star (f (circlePoint r x))).re = 0 := by
  rw [angularSlope_eq_re hf hx]
  constructor <;> intro h <;> linarith

/-- The complex derivative of an entire function is continuous. -/
theorem continuous_complex_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Continuous (deriv f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (hf.analyticAt z).deriv.continuousAt

/-- The measured angular derivative is continuous as the radius varies, at
any fixed interior angular coordinate. -/
theorem angularSlope_radial_continuous {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Continuous (fun r : ℝ => angularSlope f r x) := by
  have heq : (fun r : ℝ => angularSlope f r x) =
      (fun r : ℝ => 2 * (deriv f (circlePoint r x) * circleVelocity r x *
        star (f (circlePoint r x))).re) := by
    funext r
    exact angularSlope_eq_re (hf _) hx
  rw [heq]
  have hd := continuous_complex_deriv hf
  have hv : Continuous (fun r : ℝ => circleVelocity r x) := by
    unfold circleVelocity
    fun_prop
  have hc := continuous_circlePoint_radial x
  have hvf := hf.continuous.comp hc
  have hdf := hd.comp hc
  exact continuous_const.mul
    (Complex.reCLM.continuous.comp ((hdf.mul hv).mul hvf.star))

/-- Joint continuity of the angular velocity at an interior point. -/
theorem circleVelocity_continuousAt {p : ℝ × ℝ}
    (hx : p.2 ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun q : ℝ × ℝ => circleVelocity q.1 q.2) p := by
  have hs0 : Real.sqrt (1 - p.2 ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (sqrtArgument_pos hx))
  have hs : ContinuousAt (fun q : ℝ × ℝ => Real.sqrt (1 - q.2 ^ 2)) p := by
    fun_prop
  have hq : ContinuousAt
      (fun q : ℝ × ℝ => -q.2 / Real.sqrt (1 - q.2 ^ 2)) p :=
    continuous_snd.continuousAt.neg.div hs hs0
  unfold circleVelocity
  fun_prop

/-- Joint continuity of the actual angular derivative throughout the interior.
It follows from the proved derivative formula and analyticity of `f`. -/
theorem angularSlope_joint_continuousAt {f : ℂ → ℂ} {p : ℝ × ℝ}
    (hf : Differentiable ℂ f) (hx : p.2 ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun q : ℝ × ℝ => angularSlope f q.1 q.2) p := by
  have hc := continuous_circlePoint_joint.continuousAt (x := p)
  have hv := circleVelocity_continuousAt hx
  have hd := (continuous_complex_deriv hf).continuousAt.comp hc
  have hval := hf.continuous.continuousAt.comp hc
  have hcont : ContinuousAt
      (fun q : ℝ × ℝ => 2 * (deriv f (circlePoint q.1 q.2) *
        circleVelocity q.1 q.2 * star (f (circlePoint q.1 q.2))).re) p := by
    exact continuousAt_const.mul
      (Complex.reCLM.continuous.continuousAt.comp ((hd.mul hv).mul hval.star))
  have hangle : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 ∈ Ioo (-1 : ℝ) 1 :=
    continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds hx)
  have heq :
      (fun q : ℝ × ℝ => 2 * (deriv f (circlePoint q.1 q.2) *
        circleVelocity q.1 q.2 * star (f (circlePoint q.1 q.2))).re)
      =ᶠ[𝓝 p] (fun q : ℝ × ℝ => angularSlope f q.1 q.2) := by
    filter_upwards [hangle] with q hq
    exact (angularSlope_eq_re (hf _) hq).symm
  exact hcont.congr_of_eventuallyEq heq.symm

theorem angularSlope_joint_continuousOn {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ContinuousOn (fun p : ℝ × ℝ => angularSlope f p.1 p.2) interiorDomain := by
  intro p hp
  exact (angularSlope_joint_continuousAt hf ⟨hp.2.1, hp.2.2⟩).continuousWithinAt

/-- Denominator-free form of the angular derivative identity.  It remains
meaningful at zeros of `f`; no logarithmic derivative is used. -/
theorem angularSlope_mul_sqrt_eq {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.sqrt (1 - x ^ 2) * angularSlope f r x =
      2 * (circlePoint r x * deriv f (circlePoint r x) *
        star (f (circlePoint r x))).im := by
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (sqrtArgument_pos hx))
  rw [angularSlope_eq_re hf hx]
  simp only [circlePoint, circleVelocity, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one, sub_zero,
    zero_sub]
  field_simp [hs0]
  <;> ring

/-- The stationary equation expressed directly in the original function and
its complex derivative. -/
theorem angularSlope_eq_zero_iff_im {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    angularSlope f r x = 0 ↔
      (circlePoint r x * deriv f (circlePoint r x) *
        star (f (circlePoint r x))).im = 0 := by
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr (sqrtArgument_pos hx)
  have hid := angularSlope_mul_sqrt_eq hf hx
  constructor
  · intro h
    rw [h, mul_zero] at hid
    linarith
  · intro h
    rw [h, mul_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_left (ne_of_gt hs)

end AngularRegularity
