import AngularMaster.SharperZeroFreeSeed
import AngularMaster.StripProductBound
import AngularMaster.HeightExtension

/-!
# An analytic extension to slope eleven

The sharper Mellin bound is `1/31` on the closed critical strip. Together
with `‖s*(s-1)‖ ≤ (Im s)^2 + 1/2`, this excludes xi zeros up to every
height H with H² + 1/2 < 31. The conjugate-factor construction then proves
angular derivative nonnegativity above the corresponding cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

theorem actual_xi_ne_zero_of_height_sq_lt {s : ℂ} {H : ℝ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1)
    (hcap : H ^ 2 + 1 / 2 < 31) (ht : |s.im| ≤ H) :
    AWPIRH.xi s ≠ 0 := by
  intro hz
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [AWPIRH.xi] using hz
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hraw
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by
    rw [heq, norm_neg, norm_one]
  have hbound : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤
      (H ^ 2 + 1 / 2) * (1 / 31 : ℝ) := by
    rw [norm_mul]
    exact mul_le_mul (norm_mul_sub_one_le_height_sq_add_half hs0 hs1 ht)
      (actual_completedZeta₀_norm_le_one_thirtyone hs0 hs1)
      (norm_nonneg _) (by positivity)
  nlinarith

theorem actual_xi_zero_height_lt {H : ℝ} (hcap : H ^ 2 + 1 / 2 < 31)
    {s : ℂ} (hz : AWPIRH.xi s = 0) : H < |s.im| := by
  have hs := xi_zero_mem_critical_strip hz
  by_contra hn
  exact actual_xi_ne_zero_of_height_sq_lt hs.1.le hs.2.le hcap
    (le_of_not_gt hn) hz

/-- A quantitative family of unconditional angular positivity certificates. -/
theorem actual_cutoff_nonnegative_of_height_sq_lt {H : ℝ}
    (hH : (1 / 2 : ℝ) ≤ H) (hcap : H ^ 2 + 1 / 2 < 31) :
    CutoffDerivativeNonnegative (slopeCutoff (2 * H)) :=
  actual_cutoff_nonnegative_of_zero_height hH
    (fun _ hz => actual_xi_zero_height_lt hcap hz)

theorem QQRH_of_sq_lt_122 {m : ℝ} (hm : 1 ≤ m) (hcap : m ^ 2 < 122) :
    QQRH m := by
  have h := QQRH_of_zero_height (H := m / 2) (by linarith)
    (fun _ hz => actual_xi_zero_height_lt (H := m / 2) (by nlinarith) hz)
  simpa only [show (2 : ℝ) * (m / 2) = m by ring] using h

theorem slopeCutoff_eleven : slopeCutoff 11 = -(60 / 61 : ℝ) := by
  norm_num [slopeCutoff]

theorem actual_cutoff_eleven_nonnegative :
    CutoffDerivativeNonnegative (-(60 / 61 : ℝ)) := by
  have h := actual_cutoff_nonnegative_of_height_sq_lt
    (H := 11 / 2) (by norm_num) (by norm_num)
  simpa only [show (2 : ℝ) * (11 / 2) = 11 by norm_num,
    slopeCutoff_eleven] using h

theorem actual_deriv_nonnegative_above_neg_sixty_sixtyone
    (r : ℝ) (hr : 0 < r) (x : ℝ)
    (hx : -(60 / 61 : ℝ) < x) (hx1 : x < 1) :
    0 ≤ deriv (actualProfile r) x := by
  have h := actual_cutoff_eleven_nonnegative r hr x ⟨hx, hx1⟩
  change 0 ≤ derivWithin (actualProfile r) (Set.Icc (-1) 1) x at h
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith : -1 < x) hx1)] at h
  exact h

/-- The final exclusion uses the proved angular positivity certificate. -/
theorem QQRH_eleven : QQRH 11 := by
  apply QQRH_of_angular_positivity (by norm_num : (0 : ℝ) < 11)
  simpa only [slopeCutoff_eleven] using actual_cutoff_eleven_nonnegative

end AngularMaster
