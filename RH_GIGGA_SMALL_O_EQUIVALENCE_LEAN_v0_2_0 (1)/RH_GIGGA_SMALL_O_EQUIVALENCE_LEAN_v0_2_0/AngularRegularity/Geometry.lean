import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# The angular chart and its squared-modulus profile

The radius is the modulus in the descended `theta` plane.  The coordinate
`x` is `cos theta`; the open angular interval parametrizes the upper half-plane.
No assertion about the location of zeros is used in this file.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace AngularRegularity

def circlePoint (r x : ℝ) : ℂ :=
  (r : ℂ) * ((x : ℂ) + Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ))

def profile (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  Complex.normSq (f (circlePoint r x))

def domain : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.2 ∈ Set.Ioo (-1 : ℝ) 1}

@[simp] theorem mem_domain {p : ℝ × ℝ} :
    p ∈ domain ↔ 0 < p.1 ∧ -1 < p.2 ∧ p.2 < 1 := Iff.rfl

theorem isOpen_domain : IsOpen domain := by
  change IsOpen ({p : ℝ × ℝ | 0 < p.1} ∩
    Prod.snd ⁻¹' Set.Ioo (-1 : ℝ) 1)
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_Ioo.preimage continuous_snd)

@[simp] theorem circlePoint_re (r x : ℝ) : (circlePoint r x).re = r * x := by
  simp [circlePoint, Complex.mul_re]

@[simp] theorem circlePoint_im (r x : ℝ) :
    (circlePoint r x).im = r * Real.sqrt (1 - x ^ 2) := by
  simp [circlePoint, Complex.mul_im]

theorem one_sub_sq_pos {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  have hleft : 0 < 1 + x := by linarith [hx.1]
  have hright : 0 < 1 - x := by linarith [hx.2]
  nlinarith [mul_pos hleft hright]

theorem sqrt_one_sub_sq_pos {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 (one_sub_sq_pos hx)

theorem circlePoint_im_pos {r x : ℝ} (hr : 0 < r)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : 0 < (circlePoint r x).im := by
  rw [circlePoint_im]
  exact mul_pos hr (sqrt_one_sub_sq_pos hx)

theorem circlePoint_ne_zero {r x : ℝ} (hr : 0 < r)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : circlePoint r x ≠ 0 := by
  intro hz
  have hi := circlePoint_im_pos hr hx
  simpa only [hz, Complex.zero_im, lt_self_iff_false] using hi

theorem normSq_circlePoint {r x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Complex.normSq (circlePoint r x) = r ^ 2 := by
  have hleft : 0 ≤ 1 + x := by linarith [hx.1]
  have hright : 0 ≤ 1 - x := by linarith [hx.2]
  have hinside : 0 ≤ 1 - x ^ 2 := by
    nlinarith [mul_nonneg hleft hright]
  simp only [Complex.normSq_apply, circlePoint_re, circlePoint_im]
  calc
    _ = r ^ 2 * (x ^ 2 + (Real.sqrt (1 - x ^ 2)) ^ 2) := by ring
    _ = r ^ 2 := by rw [Real.sq_sqrt hinside]; ring

theorem continuous_circlePoint_joint :
    Continuous (fun p : ℝ × ℝ => circlePoint p.1 p.2) := by
  unfold circlePoint
  fun_prop

theorem continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
  unfold circlePoint
  fun_prop

theorem injective_circlePoint {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (circlePoint r) := by
  intro x y h
  have h' := congrArg Complex.re h
  simp only [circlePoint_re] at h'
  exact mul_left_cancel₀ hr h'

theorem profile_nonnegative (f : ℂ → ℂ) (r x : ℝ) : 0 ≤ profile f r x :=
  Complex.normSq_nonneg _

@[simp] theorem profile_eq_zero_iff (f : ℂ → ℂ) (r x : ℝ) :
    profile f r x = 0 ↔ f (circlePoint r x) = 0 :=
  Complex.normSq_eq_zero

theorem profile_pos_iff (f : ℂ → ℂ) (r x : ℝ) :
    0 < profile f r x ↔ f (circlePoint r x) ≠ 0 := by
  constructor
  · intro hp hz
    have heq := (profile_eq_zero_iff f r x).2 hz
    linarith
  · intro hz
    apply lt_of_le_of_ne (profile_nonnegative f r x)
    intro heq
    exact hz ((profile_eq_zero_iff f r x).1 heq.symm)

theorem continuous_profile_joint {f : ℂ → ℂ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => profile f p.1 p.2) :=
  Complex.continuous_normSq.comp (hf.comp continuous_circlePoint_joint)

theorem continuous_profile {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    Continuous (profile f r) :=
  Complex.continuous_normSq.comp (hf.comp (continuous_circlePoint r))

/-- Reconstruction in the closed upper half-plane, including its real boundary. -/
theorem circlePoint_norm_re_div {z : ℂ} (hz : z ≠ 0) (hi : 0 ≤ z.im) :
    circlePoint ‖z‖ (z.re / ‖z‖) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn0 : ‖z‖ ≠ 0 := ne_of_gt hn
  have hsq : 1 - (z.re / ‖z‖) ^ 2 = (z.im / ‖z‖) ^ 2 := by
    have h := Complex.sq_norm_sub_sq_re z
    field_simp [hn0]
    nlinarith
  have hsqrt : Real.sqrt (1 - (z.re / ‖z‖) ^ 2) = z.im / ‖z‖ := by
    rw [hsq, Real.sqrt_sq (div_nonneg hi hn.le)]
  apply Complex.ext
  · simp only [circlePoint_re]
    field_simp [hn0]
  · simp only [circlePoint_im, hsqrt]
    field_simp [hn0]

end AngularRegularity
