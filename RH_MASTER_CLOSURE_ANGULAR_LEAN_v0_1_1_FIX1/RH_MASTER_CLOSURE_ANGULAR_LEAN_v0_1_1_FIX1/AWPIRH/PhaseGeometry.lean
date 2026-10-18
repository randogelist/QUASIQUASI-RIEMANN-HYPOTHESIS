import Mathlib

/-! Explicit phase-disc coverage of the complement of the real ray [1,infinity). -/
set_option autoImplicit false
noncomputable section
namespace AWPIRH

def OffRay (r : ℂ) : Prop := ¬ (r.im = 0 ∧ 1 ≤ r.re)
def unitDisc : Set ℂ := Metric.ball 0 1

def phaseMap (η v : ℂ) : ℂ := (η - 1) * v / (1 - v)

@[simp] theorem phaseMap_zero (η : ℂ) : phaseMap η 0 = 0 := by
  simp [phaseMap]

theorem unitDisc_iff (v : ℂ) : v ∈ unitDisc ↔ ‖v‖ < 1 := by
  simp [unitDisc, Metric.mem_ball, dist_zero_right]

theorem one_sub_ne_zero_of_mem_unitDisc {v : ℂ} (hv : v ∈ unitDisc) :
    (1 : ℂ) - v ≠ 0 := by
  intro h
  have heq : v = 1 := (sub_eq_zero.mp h).symm
  have hn := (unitDisc_iff v).mp hv
  simpa [heq] using hn

private theorem norm_sq_coordinates (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa [Complex.normSq_apply, pow_two] using Complex.sq_norm z

theorem strict_triangle_offRay {r : ℂ} (hr : OffRay r) :
    ‖r‖ < ‖r - 1‖ + 1 := by
  have htri : ‖r‖ ≤ ‖r - 1‖ + 1 := by
    calc
      ‖r‖ = ‖(r - 1) + (1 : ℂ)‖ := by congr 1; ring
      _ ≤ ‖r - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖r - 1‖ + 1 := by simp
  by_contra hstrict
  have heq : ‖r‖ = ‖r - 1‖ + 1 := le_antisymm htri (le_of_not_gt hstrict)
  have h0 := norm_sq_coordinates r
  have h1 := norm_sq_coordinates (r - 1)
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    sub_zero] at h1
  have hre : r.re = ‖r - 1‖ + 1 := by nlinarith [heq]
  have him : r.im = 0 := by nlinarith [sq_nonneg r.im, heq, hre]
  have hre_ge : (1 : ℝ) ≤ r.re := by
    rw [hre]
    linarith [norm_nonneg (r - 1)]
  exact hr ⟨him, hre_ge⟩

theorem phase_cover {r : ℂ} (hr : OffRay r) :
    ∃ η v : ℂ, ‖η‖ = 1 ∧ v ∈ unitDisc ∧ phaseMap η v = r := by
  have hr1 : r ≠ 1 := by
    intro h
    apply hr
    simp [h]
  have hsub : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have hu : 0 < ‖r - 1‖ := norm_pos_iff.mpr hsub
  have hu0 : ‖r - 1‖ ≠ 0 := ne_of_gt hu
  have huC : (‖r - 1‖ : ℂ) ≠ 0 := by exact_mod_cast hu0
  let η : ℂ := (r - 1) / (‖r - 1‖ : ℂ)
  let b : ℂ := r + η - 1
  have hη : ‖η‖ = 1 := by
    dsimp [η]
    rw [norm_div]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hu), hu0]
  have hbform : b = ((1 + (‖r - 1‖)⁻¹ : ℝ) : ℂ) * (r - 1) := by
    dsimp [b, η]
    push_cast
    field_simp [huC]
    <;> ring
  have hbNorm : ‖b‖ = ‖r - 1‖ + 1 := by
    rw [hbform, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < 1 + (‖r - 1‖)⁻¹ by positivity)]
    field_simp [hu0]
    <;> ring
  have hb : b ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hbNorm]
    positivity
  let v : ℂ := r / b
  have hvnorm : ‖v‖ < 1 := by
    dsimp [v]
    rw [norm_div, hbNorm]
    exact (div_lt_one (by positivity)).mpr (strict_triangle_offRay hr)
  have hv : v ∈ unitDisc := (unitDisc_iff v).mpr hvnorm
  have hv1 := one_sub_ne_zero_of_mem_unitDisc hv
  refine ⟨η, v, hη, hv, ?_⟩
  apply (div_eq_iff hv1).mpr
  change (η - 1) * v = r * (1 - v)
  dsimp [v]
  field_simp [hb]
  dsimp [b]
  ring

/-- A reciprocal quadratic over a point on the excluded ray has negative real roots. -/
theorem root_on_ray_is_negative {r z : ℂ}
    (hr : r.im = 0 ∧ 1 ≤ r.re)
    (hz : z ^ 2 - 2 * (1 - 2 * r) * z + 1 = 0) :
    z.im = 0 ∧ z.re < 0 := by
  have hre : z.re ^ 2 - z.im ^ 2 -
      2 * (1 - 2 * r.re) * z.re + 1 = 0 := by
    have hh := congrArg Complex.re hz
    simp [pow_two, Complex.mul_re, Complex.mul_im, hr.1] at hh
    nlinarith [hh]
  have him : 2 * z.im * (z.re - (1 - 2 * r.re)) = 0 := by
    have hh := congrArg Complex.im hz
    simp [pow_two, Complex.mul_re, Complex.mul_im, hr.1] at hh
    nlinarith [hh]
  have him0 : z.im = 0 := by
    by_contra hi
    have htwo : (2 : ℝ) * z.im ≠ 0 := mul_ne_zero (by norm_num) hi
    have hcenter : z.re = 1 - 2 * r.re := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp him).resolve_left htwo)
    have hcenter_le : 1 - 2 * r.re ≤ (-1 : ℝ) := by linarith [hr.2]
    have hcenter_sq : 1 ≤ (1 - 2 * r.re) ^ 2 := by nlinarith
    have hisq : 0 < z.im ^ 2 := sq_pos_of_ne_zero hi
    rw [hcenter] at hre
    nlinarith
  refine ⟨him0, ?_⟩
  by_contra hneg
  have hz0 : 0 ≤ z.re := le_of_not_gt hneg
  have hb : 0 ≤ -(1 - 2 * r.re) := by linarith [hr.2]
  have hm := mul_nonneg hb hz0
  rw [him0] at hre
  nlinarith [sq_nonneg z.re]

/-- No nonzero real part can square to a negative real number. -/
theorem re_eq_zero_of_square_negative {w : ℂ}
    (hi : (w ^ 2).im = 0) (hr : (w ^ 2).re < 0) : w.re = 0 := by
  have him : 2 * w.re * w.im = 0 := by
    have hh : w.re * w.im + w.im * w.re = 0 := by
      simpa [pow_two, Complex.mul_im] using hi
    nlinarith [hh]
  have hre : w.re ^ 2 - w.im ^ 2 < 0 := by
    simpa [pow_two, Complex.mul_re] using hr
  by_contra hw
  have hwi : w.im = 0 :=
    (mul_eq_zero.mp him).resolve_left (mul_ne_zero (by norm_num) hw)
  rw [hwi] at hre
  nlinarith [sq_nonneg w.re]

end AWPIRH
