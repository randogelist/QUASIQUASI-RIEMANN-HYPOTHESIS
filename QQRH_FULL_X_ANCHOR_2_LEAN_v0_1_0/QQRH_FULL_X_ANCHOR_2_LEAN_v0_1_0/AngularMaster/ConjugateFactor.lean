import AngularMaster.ZeroExclusion
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Conjugate zero factors with an arbitrary angular cutoff. These identities
allow off-axis zeros; no Riemann-hypothesis assumption enters.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexConjugate

namespace AngularMaster

/-- Squared modulus of a conjugate pair, in normalized polar coordinates. -/
def conjugateFactorPolynomial (q c x : ℝ) : ℝ :=
  (1 - q ^ 2) ^ 2 + 4 * q ^ 2 * c ^ 2 + 4 * q ^ 2 * x ^ 2 -
    4 * q * c * (1 + q ^ 2) * x

theorem conjugateFactorPolynomial_sum_of_squares (q c x : ℝ) :
    conjugateFactorPolynomial q c x =
      (1 - c ^ 2) * (q ^ 2 - 1) ^ 2 +
        (2 * q * x - c * (1 + q ^ 2)) ^ 2 := by
  unfold conjugateFactorPolynomial
  ring

theorem conjugateFactorPolynomial_nonnegative {q c x : ℝ}
    (hc : |c| ≤ 1) : 0 ≤ conjugateFactorPolynomial q c x := by
  rw [conjugateFactorPolynomial_sum_of_squares]
  have hc2 : 0 ≤ 1 - c ^ 2 := by
    rcases abs_le.mp hc with ⟨hc0, hc1⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - c) (by linarith : 0 ≤ 1 + c)]
  positivity

theorem hasDerivAt_conjugateFactorPolynomial (q c x : ℝ) :
    HasDerivAt (conjugateFactorPolynomial q c)
      (8 * q ^ 2 * (x - c) + 4 * q * (-c) * (q - 1) ^ 2) x := by
  unfold conjugateFactorPolynomial
  convert!
    (((hasDerivAt_const x ((1 - q ^ 2) ^ 2 + 4 * q ^ 2 * c ^ 2)).add
      (((hasDerivAt_id x).pow 2).const_mul (4 * q ^ 2))).sub
      ((hasDerivAt_id x).const_mul (4 * q * c * (1 + q ^ 2)))) using 1
  norm_num
  ring

theorem deriv_conjugateFactorPolynomial (q c x : ℝ) :
    deriv (conjugateFactorPolynomial q c) x =
      8 * q ^ 2 * (x - c) + 4 * q * (-c) * (q - 1) ^ 2 :=
  (hasDerivAt_conjugateFactorPolynomial q c x).deriv

theorem deriv_conjugateFactorPolynomial_nonnegative {q c a x : ℝ}
    (hq : 0 ≤ q) (hca : c ≤ a) (ha0 : a ≤ 0) (hax : a ≤ x) :
    0 ≤ deriv (conjugateFactorPolynomial q c) x := by
  rw [deriv_conjugateFactorPolynomial]
  have hxc : 0 ≤ x - c := sub_nonneg.mpr (hca.trans hax)
  have hc0 : 0 ≤ -c := neg_nonneg.mpr (hca.trans ha0)
  positivity

theorem conjugateFactorPolynomial_difference (q c x y : ℝ) :
    conjugateFactorPolynomial q c y - conjugateFactorPolynomial q c x =
      (y - x) * (4 * q ^ 2 * (x + y - 2 * c) +
        4 * q * (-c) * (q - 1) ^ 2) := by
  unfold conjugateFactorPolynomial
  ring

theorem conjugateFactorPolynomial_monotoneOn {q c a : ℝ}
    (hq : 0 ≤ q) (hca : c ≤ a) (ha0 : a ≤ 0) :
    MonotoneOn (conjugateFactorPolynomial q c) (Ici a) := by
  intro x hx y hy hxy
  have hxc : 0 ≤ x + y - 2 * c := by
    change a ≤ x at hx
    change a ≤ y at hy
    linarith
  have hc0 : 0 ≤ -c := neg_nonneg.mpr (hca.trans ha0)
  have hdiff : 0 ≤ conjugateFactorPolynomial q c y -
      conjugateFactorPolynomial q c x := by
    rw [conjugateFactorPolynomial_difference]
    exact mul_nonneg (sub_nonneg.mpr hxy) (by positivity)
  exact sub_nonneg.mp hdiff

/-- The same pair before division by the squared norm of its root. -/
def conjugateFactorNumerator (N b r x : ℝ) : ℝ :=
  (N - r ^ 2) ^ 2 + 4 * r ^ 2 * b ^ 2 + 4 * r ^ 2 * N * x ^ 2 -
    4 * r * b * (N + r ^ 2) * x

theorem normSq_conjugateFactor_numerator (α z : ℂ) :
    Complex.normSq ((α - z) * (conj α - z)) =
      (Complex.normSq α - Complex.normSq z) ^ 2 +
        4 * Complex.normSq z * α.re ^ 2 +
        4 * Complex.normSq α * z.re ^ 2 -
        4 * α.re * (Complex.normSq α + Complex.normSq z) * z.re := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem normSq_circlePoint_eq_sq (r x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq (circlePoint r x) = r ^ 2 := by
  have hs : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := by
    apply Real.sq_sqrt
    rcases hx with ⟨hx0, hx1⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - x) (by linarith : 0 ≤ 1 + x)]
  rw [Complex.normSq_apply, circlePoint_re, circlePoint_im]
  calc
    _ = r ^ 2 * (x ^ 2 + (Real.sqrt (1 - x ^ 2)) ^ 2) := by ring
    _ = r ^ 2 := by rw [hs]; ring

theorem normSq_conjugateFactor_circle_numerator (α : ℂ) (r x : ℝ)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq ((α - circlePoint r x) * (conj α - circlePoint r x)) =
      conjugateFactorNumerator (Complex.normSq α) α.re r x := by
  rw [normSq_conjugateFactor_numerator, normSq_circlePoint_eq_sq r x hx,
    circlePoint_re]
  unfold conjugateFactorNumerator
  ring

theorem normSq_conjugateFactor_circle {α : ℂ} (hα : α ≠ 0)
    (r x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq ((1 - circlePoint r x / α) *
      (1 - circlePoint r x / conj α)) =
      conjugateFactorPolynomial (r / ‖α‖) (α.re / ‖α‖) x := by
  have hcα : conj α ≠ 0 := by simpa using hα
  have hfactor : (1 - circlePoint r x / α) * (1 - circlePoint r x / conj α) =
      ((α - circlePoint r x) * (conj α - circlePoint r x)) / (α * conj α) := by
    field_simp
  rw [hfactor, Complex.normSq_div,
    normSq_conjugateFactor_circle_numerator α r x hx, map_mul, Complex.normSq_conj]
  unfold conjugateFactorNumerator conjugateFactorPolynomial
  rw [Complex.normSq_eq_norm_sq]
  have hn : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα
  field_simp

/-- Symmetrizing the evaluation variable gives the same squared modulus as
pairing the root with its conjugate. No root-index pairing is required. -/
theorem normSq_symmetricFactor_eq_conjugateFactor (α z : ℂ) :
    Complex.normSq ((1 - z / α) * (1 - conj z / α)) =
      Complex.normSq ((1 - z / α) * (1 - z / conj α)) := by
  rw [map_mul, map_mul]
  congr 1
  have hc : conj (1 - conj z / α) = 1 - z / conj α := by simp
  rw [← hc, Complex.normSq_conj]

theorem monotoneOn_normSq_conjugateFactor_circle {α : ℂ} (hα : α ≠ 0)
    {r a : ℝ} (hr : 0 ≤ r) (ha : -1 ≤ a) (ha0 : a ≤ 0)
    (hca : α.re / ‖α‖ ≤ a) :
    MonotoneOn (fun x => Complex.normSq ((1 - circlePoint r x / α) *
      (1 - circlePoint r x / conj α))) (Icc a 1) := by
  intro x hx y hy hxy
  change Complex.normSq ((1 - circlePoint r x / α) *
      (1 - circlePoint r x / conj α)) ≤
    Complex.normSq ((1 - circlePoint r y / α) *
      (1 - circlePoint r y / conj α))
  rw [normSq_conjugateFactor_circle hα r x ⟨ha.trans hx.1, hx.2⟩,
    normSq_conjugateFactor_circle hα r y ⟨ha.trans hy.1, hy.2⟩]
  exact conjugateFactorPolynomial_monotoneOn
    (div_nonneg hr (norm_nonneg α)) hca ha0 hx.1 hy.1 hxy

end AngularMaster
