import AngularMaster.FullXGeometry
import AngularMaster.SectorPositivity

/-!
Full angular monotonicity on a bounded radial interval. The height hypothesis
is explicit in this transport module; SecondFullXAnchor supplies its analytic
proof for the actual xi function.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators ComplexConjugate

namespace AngularMaster

theorem actualSymmetricFactor_monotoneOn_full_of_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → (13 / 2 : ℝ) < |s.im|)
    (i : ActualPairIndex) {r : ℝ} (hr : 0 ≤ r) (hR : r ≤ 255 / 7) :
    MonotoneOn (actualSymmetricFactor i r) (Icc (-1) 1) := by
  let z := -actualComplexScale i
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z := AWPIRH.complex_sqrt_sq z
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 :=
    actual_theta_neg_complexScale_zero i
  have hstrip := xi_zero_mem_critical_strip hxi
  have hwre : |w.re| ≤ (1 / 2 : ℝ) := by
    apply abs_le.mpr
    norm_num [Complex.add_re] at hstrip
    constructor <;> linarith
  have hwim : (13 / 2 : ℝ) ≤ |w.im| := by
    have h := hheight _ hxi
    simpa using h.le
  have hm := monotoneOn_normSq_conjugateFactor_circle_of_height hwre hwim hr hR
  rw [hsq] at hm
  have heq (x : ℝ) : actualSymmetricFactor i r x =
      Complex.normSq ((1 - circlePoint r x / z) *
        (1 - circlePoint r x / conj z)) := by
    simpa only [actualSymmetricFactor, z, div_neg, sub_neg_eq_add] using
      normSq_symmetricFactor_eq_conjugateFactor z (circlePoint r x)
  intro x hx y hy hxy
  rw [heq, heq]
  exact hm hx hy hxy

theorem actualProfile_monotoneOn_full_of_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → (13 / 2 : ℝ) < |s.im|)
    {r : ℝ} (hr : 0 < r) (hR : r ≤ 255 / 7) :
    MonotoneOn (actualProfile r) (Icc (-1) 1) := by
  obtain ⟨c, hc, hp⟩ := actualProfile_sq_symmetric_product_values
  intro x hx y hy hxy
  have hsq : (actualProfile r x) ^ 2 ≤ (actualProfile r y) ^ 2 := by
    apply le_of_tendsto_of_tendsto' (hp r hr x hx) (hp r hr y hy)
    intro s
    apply mul_le_mul_of_nonneg_left ?_ (hc r hr)
    apply Finset.prod_le_prod
    · intro i hi
      exact actualSymmetricFactor_nonnegative i r x
    · intro i hi
      exact actualSymmetricFactor_monotoneOn_full_of_height hheight i hr.le hR hx hy hxy
  exact (sq_le_sq₀ (actualProfile_nonnegative_all r x)
    (actualProfile_nonnegative_all r y)).mp hsq

theorem actual_deriv_nonnegative_full_of_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → (13 / 2 : ℝ) < |s.im|)
    {r : ℝ} (hr : 0 < r) (hR : r ≤ 255 / 7)
    {x : ℝ} (hx : -1 < x) (hx1 : x < 1) :
    0 ≤ deriv (actualProfile r) x := by
  have hm := actualProfile_monotoneOn_full_of_height hheight hr hR
  have hd : 0 ≤ derivWithin (actualProfile r) (Icc (-1) 1) x :=
    hm.derivWithin_nonneg
  rwa [derivWithin_of_mem_nhds (Icc_mem_nhds hx hx1)] at hd

/-- The usual angular identity-principle argument at each fixed radius. -/
theorem actual_theta_circle_ne_zero_full_of_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → (13 / 2 : ℝ) < |s.im|)
    {r : ℝ} (hr : 0 < r) (hR : r ≤ 255 / 7)
    {x : ℝ} (hx : -1 < x) (hx1 : x ≤ 1) :
    AWPIRH.theta (circlePoint r x) ≠ 0 :=
  circle_ne_zero_of_angular_monotone_cutoff AWPIRH.theta_entire
    ⟨1, AWPIRH.theta_one_ne_zero⟩ hr hx hx1
    (actualProfile_monotoneOn_full_of_height hheight hr hR)

/-- The same height gap also includes the left endpoint and the origin. -/
theorem actual_theta_ne_zero_closed_disk_of_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → (13 / 2 : ℝ) < |s.im|)
    {z : ℂ} (hz : ‖z‖ ≤ 255 / 7) : AWPIRH.theta z ≠ 0 := by
  intro hzero
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z := AWPIRH.complex_sqrt_sq z
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 := hzero
  have him : (13 / 2 : ℝ) < |w.im| := by simpa using hheight _ hxi
  have hn := norm_square_eq_re_sq_add_im_sq w
  rw [hsq] at hn
  nlinarith [sq_abs w.im, sq_nonneg w.re]

theorem actualProfile_pos_closed_of_height
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → (13 / 2 : ℝ) < |s.im|)
    {r : ℝ} (hr : 0 ≤ r) (hR : r ≤ 255 / 7)
    {x : ℝ} (hx : x ∈ Icc (-1) 1) : 0 < actualProfile r x := by
  apply Complex.normSq_pos.mpr
  apply actual_theta_ne_zero_closed_disk_of_height hheight
  rwa [circlePoint_norm r x hr hx]

end AngularMaster
