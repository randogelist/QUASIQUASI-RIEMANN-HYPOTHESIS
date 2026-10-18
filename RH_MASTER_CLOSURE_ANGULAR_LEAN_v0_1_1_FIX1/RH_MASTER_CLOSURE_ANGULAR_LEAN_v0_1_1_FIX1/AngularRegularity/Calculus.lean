import Mathlib

/-!
# The angular profile: elementary regularity

These results concern an arbitrary complex function.  The only hypotheses on
that function are stated continuity or differentiability hypotheses.  In
particular, no positivity conjecture, stationary-point exclusion, or statement
about zeta zeros is assumed.

The profile is defined on all real coordinates, using Lean's total real square
root.  Angular differentiability statements are restricted to `-1 < x < 1`;
no assertion about endpoint derivatives is made.
-/

noncomputable section
open Set

namespace AngularRegularity

/-- The upper semicircle in the square coordinate. -/
def circlePoint (r x : ℝ) : ℂ :=
  (r : ℂ) * ((x : ℂ) + Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ))

/-- The original squared-modulus profile. -/
def profile (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  Complex.normSq (f (circlePoint r x))

/-- Ordinary angular derivative; theorems below use only interior angles. -/
def angularSlope (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  deriv (profile f r) x

/-- Ordinary radial derivative. -/
def radialSlope (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  deriv (fun t => profile f t x) r

/-- Interior angular-coordinate domain. -/
def interiorDomain : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ -1 < p.2 ∧ p.2 < 1}

/-- Strict positivity of the square-root argument on the angular interior. -/
theorem sqrtArgument_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  rcases hx with ⟨hx0, hx1⟩
  nlinarith [mul_pos (by linarith : 0 < 1 - x) (by linarith : 0 < 1 + x)]

theorem sqrtArgument_ne_zero {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    1 - x ^ 2 ≠ 0 := ne_of_gt (sqrtArgument_pos hx)

theorem continuous_circlePoint_joint :
    Continuous (fun p : ℝ × ℝ => circlePoint p.1 p.2) := by
  unfold circlePoint
  fun_prop

theorem continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
  unfold circlePoint
  fun_prop

theorem continuous_circlePoint_radial (x : ℝ) :
    Continuous (fun r : ℝ => circlePoint r x) := by
  unfold circlePoint
  fun_prop

theorem profile_nonnegative (f : ℂ → ℂ) (r x : ℝ) :
    0 ≤ profile f r x := Complex.normSq_nonneg _

@[simp] theorem profile_eq_zero_iff (f : ℂ → ℂ) (r x : ℝ) :
    profile f r x = 0 ↔ f (circlePoint r x) = 0 := by
  exact Complex.normSq_eq_zero

theorem profile_pos_iff (f : ℂ → ℂ) (r x : ℝ) :
    0 < profile f r x ↔ f (circlePoint r x) ≠ 0 := by
  exact Complex.normSq_pos

theorem profile_continuous_joint {f : ℂ → ℂ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => profile f p.1 p.2) :=
  Complex.continuous_normSq.comp (hf.comp continuous_circlePoint_joint)

theorem profile_continuous {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    Continuous (profile f r) :=
  Complex.continuous_normSq.comp (hf.comp (continuous_circlePoint r))

theorem profile_radial_continuous {f : ℂ → ℂ} (hf : Continuous f) (x : ℝ) :
    Continuous (fun r : ℝ => profile f r x) :=
  Complex.continuous_normSq.comp (hf.comp (continuous_circlePoint_radial x))

/-- The coordinate map is differentiable along every interior angular slice. -/
theorem circlePoint_differentiableAt {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (circlePoint r) x := by
  have hsqrt : DifferentiableAt ℝ (fun y : ℝ => Real.sqrt (1 - y ^ 2)) x :=
    (differentiableAt_const (1 : ℝ) |>.sub (differentiableAt_id.pow 2)).sqrt
      (sqrtArgument_ne_zero hx)
  unfold circlePoint
  fun_prop

/-- There is no angular endpoint restriction for radial differentiation. -/
theorem circlePoint_radial_differentiableAt (r x : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => circlePoint t x) r := by
  unfold circlePoint
  fun_prop

/-- Interior differentiability obtained from complex differentiability at the
actual point being evaluated, rather than from a formal derivative symbol. -/
theorem profile_differentiableAt {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x))
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (profile f r) x := by
  have ht : DifferentiableAt ℝ (fun y => f (circlePoint r y)) x :=
    (hf.restrictScalars ℝ).comp x (circlePoint_differentiableAt hx)
  have hprofile : profile f r = fun y => ‖f (circlePoint r y)‖ ^ 2 := by
    funext y
    simp only [profile, Complex.normSq_eq_norm_sq]
  rw [hprofile]
  exact DifferentiableAt.norm_sq ℂ ht

theorem profile_differentiableOn {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (r : ℝ) :
    DifferentiableOn ℝ (profile f r) (Ioo (-1 : ℝ) 1) := by
  intro x hx
  exact (profile_differentiableAt (hf _) hx).differentiableWithinAt

theorem profile_radial_differentiableAt {f : ℂ → ℂ} {r x : ℝ}
    (hf : DifferentiableAt ℂ f (circlePoint r x)) :
    DifferentiableAt ℝ (fun t => profile f t x) r := by
  have ht : DifferentiableAt ℝ (fun t => f (circlePoint t x)) r :=
    (hf.restrictScalars ℝ).comp r (circlePoint_radial_differentiableAt r x)
  simpa only [profile, Complex.normSq_eq_norm_sq] using
    (DifferentiableAt.norm_sq ℂ ht)

/-- Smoothness of the two-coordinate map on the interior. -/
theorem circlePoint_contDiffAt {p : ℝ × ℝ}
    (hx : p.2 ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × ℝ => circlePoint q.1 q.2) p := by
  have hsqrt : ContDiffAt ℝ ⊤
      (fun q : ℝ × ℝ => Real.sqrt (1 - q.2 ^ 2)) p :=
    (Real.contDiffAt_sqrt (sqrtArgument_ne_zero hx)).comp p
      (contDiffAt_const.sub (contDiffAt_snd.pow 2))
  have hr : ContDiffAt ℝ ⊤ (fun q : ℝ × ℝ => (q.1 : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p contDiffAt_fst
  have hxC : ContDiffAt ℝ ⊤ (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p contDiffAt_snd
  have hsC : ContDiffAt ℝ ⊤
      (fun q : ℝ × ℝ => (Real.sqrt (1 - q.2 ^ 2) : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hsqrt
  exact hr.mul (hxC.add (contDiffAt_const.mul hsC))

/-- A smooth complex function has a jointly smooth interior angular profile. -/
theorem profile_contDiffAt {f : ℂ → ℂ} {p : ℝ × ℝ}
    (hf : ContDiff ℝ ⊤ f) (hx : p.2 ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × ℝ => profile f q.1 q.2) p := by
  have ht : ContDiffAt ℝ ⊤
      (fun q : ℝ × ℝ => f (circlePoint q.1 q.2)) p :=
    hf.contDiffAt.comp p (circlePoint_contDiffAt hx)
  simpa only [profile, Complex.normSq_eq_norm_sq] using
    (ContDiffAt.norm_sq ℂ ht)

theorem profile_contDiffOn {f : ℂ → ℂ} (hf : ContDiff ℝ ⊤ f) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => profile f p.1 p.2) interiorDomain := by
  intro p hp
  exact (profile_contDiffAt hf ⟨hp.2.1, hp.2.2⟩).contDiffWithinAt

/-- An entire complex function supplies the smoothness hypothesis above. -/
theorem profile_contDiffAt_of_differentiable {f : ℂ → ℂ} {p : ℝ × ℝ}
    (hf : Differentiable ℂ f) (hx : p.2 ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × ℝ => profile f q.1 q.2) p :=
  profile_contDiffAt (ContDiff.restrict_scalars ℝ (hf.contDiff : ContDiff ℂ ⊤ f)) hx

theorem profile_contDiffOn_of_differentiable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => profile f p.1 p.2) interiorDomain :=
  profile_contDiffOn (ContDiff.restrict_scalars ℝ (hf.contDiff : ContDiff ℂ ⊤ f))

/-- Smoothness along each interior fixed-radius arc. -/
theorem profile_slice_contDiffAt {f : ℂ → ℂ} {r x : ℝ}
    (hf : Differentiable ℂ f) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ⊤ (profile f r) x := by
  have hmap : ContDiffAt ℝ ⊤ (fun y : ℝ => (r, y)) x := by fun_prop
  exact (profile_contDiffAt_of_differentiable (p := (r, x)) hf hx).comp x hmap

/-- Continuity of the actual angular derivative on each interior arc. -/
theorem angularSlope_continuousAt {f : ℂ → ℂ} {r x : ℝ}
    (hf : Differentiable ℂ f) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (angularSlope f r) x := by
  have hs : ContDiffAt ℝ ⊤ (profile f r) x := profile_slice_contDiffAt hf hx
  have hd : ContDiffAt ℝ ⊤ (deriv (profile f r)) x := hs.derivWithin (by simp)
  exact hd.continuousAt

theorem angularSlope_continuousOn {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    ContinuousOn (angularSlope f r) (Ioo (-1 : ℝ) 1) := by
  intro x hx
  exact (angularSlope_continuousAt hf hx).continuousWithinAt

/-- Compatibility with the one-sided closed-interval convention in the
attached angular architecture.  In the interior it is the same derivative. -/
theorem angularSlope_eq_derivWithin {f : ℂ → ℂ} {r x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    angularSlope f r x = derivWithin (profile f r) (Icc (-1 : ℝ) 1) x := by
  change deriv (profile f r) x = _
  exact (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm

end AngularRegularity
