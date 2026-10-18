import AngularMaster.ConjugateFactor
import AngularMaster.LowHeightGeometry

/-! Full angular monotonicity on a bounded radial interval, transported from
an explicit lower bound for zero heights. No RH or positivity premise is used. -/

set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexConjugate

namespace AngularMaster

/-- The vertex of the quadratic factor lies at or to the left of `-1`. -/
theorem conjugateFactorPolynomial_monotoneOn_full_interval {q c : ℝ}
    (hq : 0 ≤ q) (hvertex : 2 * q + c * (1 + q ^ 2) ≤ 0) :
    MonotoneOn (conjugateFactorPolynomial q c) (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hsum : 0 ≤ x + y + 2 := by linarith [hx.1, hy.1]
  have hv : 0 ≤ -(2 * q + c * (1 + q ^ 2)) := neg_nonneg.mpr hvertex
  have hd : 0 ≤ conjugateFactorPolynomial q c y -
      conjugateFactorPolynomial q c x := by
    calc
      conjugateFactorPolynomial q c y - conjugateFactorPolynomial q c x =
          (y - x) * (4 * q * (q * (x + y + 2) +
            (-(2 * q + c * (1 + q ^ 2))))) := by
              unfold conjugateFactorPolynomial
              ring
      _ ≥ 0 := mul_nonneg (sub_nonneg.mpr hxy) (by positivity)
  exact sub_nonneg.mp hd

/-- Exact rectangular minimum behind the radius `255/7`. -/
theorem height_thirteen_halves_inner_radius_polynomial
    {g h : ℝ} (hg : (13 / 2 : ℝ) ≤ g) (_hh0 : 0 ≤ h)
    (hh : h ≤ (1 / 2 : ℝ)) :
    0 ≤ (g ^ 2 + h ^ 2) * (g - h) - (255 / 7 : ℝ) * (g + h) := by
  have hgh : 0 ≤ g - h := by linarith
  have hg0 : 0 ≤ g + (13 / 2 : ℝ) := by linarith
  have hbase : 0 ≤ (13 / 2 : ℝ) ^ 2 + h ^ 2 - (255 / 7 : ℝ) := by
    nlinarith [sq_nonneg h]
  have hleft : 0 ≤ (g - h) * (g + (13 / 2 : ℝ)) +
      (13 / 2 : ℝ) ^ 2 + h ^ 2 - (255 / 7 : ℝ) := by
    nlinarith [mul_nonneg hgh hg0]
  have hright : 0 ≤ ((13 / 2 : ℝ) - h) *
      ((13 / 2 : ℝ) - (1 / 2 : ℝ)) + h ^ 2 +
      (1 / 2 : ℝ) ^ 2 + (255 / 7 : ℝ) := by
    have : 0 ≤ (13 / 2 : ℝ) - h := by linarith
    positivity
  calc
    (g ^ 2 + h ^ 2) * (g - h) - (255 / 7 : ℝ) * (g + h) =
        (g - (13 / 2 : ℝ)) *
          ((g - h) * (g + (13 / 2 : ℝ)) +
            (13 / 2 : ℝ) ^ 2 + h ^ 2 - (255 / 7 : ℝ)) +
        ((1 / 2 : ℝ) - h) *
          (((13 / 2 : ℝ) - h) * ((13 / 2 : ℝ) - (1 / 2 : ℝ)) +
            h ^ 2 + (1 / 2 : ℝ) ^ 2 + (255 / 7 : ℝ)) := by ring
    _ ≥ 0 := add_nonneg
      (mul_nonneg (sub_nonneg.mpr hg) hleft)
      (mul_nonneg (sub_nonneg.mpr hh) hright)

/-- A purely algebraic radial criterion; denominators are strictly positive. -/
theorem height_thirteen_halves_full_interval_vertex
    {g h r : ℝ} (hg : (13 / 2 : ℝ) ≤ g) (hh0 : 0 ≤ h)
    (hh : h ≤ (1 / 2 : ℝ)) (hr : 0 ≤ r) (hR : r ≤ (255 / 7 : ℝ)) :
    2 * (r / (g ^ 2 + h ^ 2)) +
      ((h ^ 2 - g ^ 2) / (g ^ 2 + h ^ 2)) *
        (1 + (r / (g ^ 2 + h ^ 2)) ^ 2) ≤ 0 := by
  have hA : 0 < g ^ 2 + h ^ 2 := by nlinarith [sq_nonneg h]
  have hA0 : g ^ 2 + h ^ 2 ≠ 0 := ne_of_gt hA
  have hgh : 0 ≤ g + h := by linarith
  have hfirst : 0 ≤ (g - h) * (g ^ 2 + h ^ 2) - (g + h) * r := by
    have hbound := height_thirteen_halves_inner_radius_polynomial hg hh0 hh
    have hadd := mul_nonneg hgh (sub_nonneg.mpr hR)
    nlinarith only [hbound, hadd]
  have hsecond : 0 ≤ (g + h) * (g ^ 2 + h ^ 2) - (g - h) * r := by
    have hadd := mul_nonneg hh0 (by nlinarith : 0 ≤ g ^ 2 + h ^ 2 + r)
    nlinarith only [hfirst, hadd]
  have hprod : 0 ≤ (g ^ 2 - h ^ 2) * ((g ^ 2 + h ^ 2) ^ 2 + r ^ 2) -
      2 * r * (g ^ 2 + h ^ 2) ^ 2 := by
    calc
      (g ^ 2 - h ^ 2) * ((g ^ 2 + h ^ 2) ^ 2 + r ^ 2) -
          2 * r * (g ^ 2 + h ^ 2) ^ 2 =
          ((g - h) * (g ^ 2 + h ^ 2) - (g + h) * r) *
          ((g + h) * (g ^ 2 + h ^ 2) - (g - h) * r) := by ring
      _ ≥ 0 := mul_nonneg hfirst hsecond
  calc
    2 * (r / (g ^ 2 + h ^ 2)) +
        ((h ^ 2 - g ^ 2) / (g ^ 2 + h ^ 2)) *
          (1 + (r / (g ^ 2 + h ^ 2)) ^ 2) =
        -((g ^ 2 - h ^ 2) * ((g ^ 2 + h ^ 2) ^ 2 + r ^ 2) -
          2 * r * (g ^ 2 + h ^ 2) ^ 2) / (g ^ 2 + h ^ 2) ^ 3 := by
            field_simp
            ring
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hprod) (by positivity)

/-- Full `x`-interval monotonicity at radius at most `255/7`, from the
critical-strip half-width and the height bound `13/2`. -/
theorem monotoneOn_normSq_conjugateFactor_circle_of_height {w : ℂ}
    (hre : |w.re| ≤ (1 / 2 : ℝ)) (him : (13 / 2 : ℝ) ≤ |w.im|)
    {r : ℝ} (hr : 0 ≤ r) (hR : r ≤ (255 / 7 : ℝ)) :
    MonotoneOn (fun x => Complex.normSq
      ((1 - circlePoint r x / w ^ 2) *
        (1 - circlePoint r x / conj (w ^ 2)))) (Icc (-1 : ℝ) 1) := by
  have hw : w ≠ 0 := by
    intro hw
    simp only [hw, Complex.zero_im, abs_zero] at him
    norm_num at him
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hn : ‖w ^ 2‖ = |w.im| ^ 2 + |w.re| ^ 2 := by
    rw [norm_square_eq_re_sq_add_im_sq, sq_abs, sq_abs]
    ring
  have hreal : (w ^ 2).re = |w.re| ^ 2 - |w.im| ^ 2 := by
    rw [square_re_eq_re_sq_sub_im_sq, sq_abs, sq_abs]
  have hv : 2 * (r / ‖w ^ 2‖) +
      ((w ^ 2).re / ‖w ^ 2‖) * (1 + (r / ‖w ^ 2‖) ^ 2) ≤ 0 := by
    rw [hn, hreal]
    exact height_thirteen_halves_full_interval_vertex him (abs_nonneg _) hre hr hR
  have hm := conjugateFactorPolynomial_monotoneOn_full_interval
    (div_nonneg hr (norm_nonneg (w ^ 2))) hv
  intro x hx y hy hxy
  change Complex.normSq ((1 - circlePoint r x / w ^ 2) *
      (1 - circlePoint r x / conj (w ^ 2))) ≤
    Complex.normSq ((1 - circlePoint r y / w ^ 2) *
      (1 - circlePoint r y / conj (w ^ 2)))
  rw [normSq_conjugateFactor_circle hw2 r x hx,
    normSq_conjugateFactor_circle hw2 r y hy]
  exact hm hx hy hxy

end AngularMaster
