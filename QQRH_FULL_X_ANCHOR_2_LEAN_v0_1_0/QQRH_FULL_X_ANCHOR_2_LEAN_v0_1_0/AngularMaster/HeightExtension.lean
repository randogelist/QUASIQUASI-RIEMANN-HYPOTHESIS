import AngularMaster.LowHeightGeometry
import AngularMaster.SectorPositivity
import AngularMaster.QQRH

/-!
# Zero-height transport to angular positivity and QQRH

A uniform lower bound `H` for the imaginary parts of actual xi zeros gives
the angular cutoff associated with slope `2 * H`. For `H ≥ 1/2`, this cutoff
is nonpositive, so the existing conjugate-factor argument proves positivity
of the full actual angular profile. The final exclusion uses that positivity.
The zero-height input remains explicit throughout this module.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

theorem theta_zero_angle_le_cutoff_of_height {H : ℝ} (hH : 0 < H)
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → H < |s.im|)
    {z : ℂ} (hz0 : z ≠ 0) (hz : AWPIRH.theta z = 0) :
    z.re / ‖z‖ ≤ slopeCutoff (2 * H) := by
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z := AWPIRH.complex_sqrt_sq z
  have hw : w ≠ 0 := by
    intro h
    apply hz0
    rw [← hsq, h]
    simp
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 := hz
  have hstrip := xi_zero_mem_critical_strip hxi
  have hwre : |w.re| < (1 / 2 : ℝ) := by
    apply abs_lt.mpr
    norm_num [Complex.add_re] at hstrip
    constructor <;> linarith
  have hwim : H < |w.im| := by
    simpa using hheight _ hxi
  have hsmall : 2 * H * |w.re| < H := by
    nlinarith [mul_pos hH (sub_pos.mpr hwre)]
  have hangle := square_angle_le_cutoff_of_le_abs_im
    (by positivity : (0 : ℝ) < 2 * H) hw
    (by linarith : (2 * H) * |w.re| ≤ |w.im|)
  simpa only [hsq] using hangle

theorem actualComplexScale_sector_of_height {H : ℝ} (hH : 0 < H)
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → H < |s.im|)
    (i : ActualPairIndex) :
    -(actualComplexScale i).re / ‖actualComplexScale i‖ ≤ slopeCutoff (2 * H) := by
  have h := theta_zero_angle_le_cutoff_of_height hH hheight
    (neg_ne_zero.mpr (actualComplexScale_ne_zero i))
    (actual_theta_neg_complexScale_zero i)
  simpa only [Complex.neg_re, norm_neg] using h

theorem slopeCutoff_twice_nonpositive {H : ℝ} (hH : (1 / 2 : ℝ) ≤ H) :
    slopeCutoff (2 * H) ≤ 0 := by
  unfold slopeCutoff
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith
  · positivity

/-- A uniform actual-zero height bound yields positivity of the full actual
profile at every positive radius. No RH hypothesis is used. -/
theorem actual_cutoff_nonnegative_of_zero_height {H : ℝ}
    (hH : (1 / 2 : ℝ) ≤ H)
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → H < |s.im|) :
    CutoffDerivativeNonnegative (slopeCutoff (2 * H)) := by
  have hH0 : 0 < H := by linarith
  have hm : 0 < 2 * H := by positivity
  exact actual_cutoffDerivativeNonnegative_of_complexScale_sector
    (slopeCutoff_mem_Ioo hm).1.le (slopeCutoff_twice_nonpositive hH)
    (actualComplexScale_sector_of_height hH0 hheight)

/-- The zero-height extension reaches QQRH through the angular-positivity
criterion, retaining the height theorem as its explicit analytic input. -/
theorem QQRH_of_zero_height {H : ℝ}
    (hH : (1 / 2 : ℝ) ≤ H)
    (hheight : ∀ s : ℂ, AWPIRH.xi s = 0 → H < |s.im|) :
    QQRH (2 * H) := by
  have hm : 0 < 2 * H := by linarith
  exact QQRH_of_angular_positivity hm
    (actual_cutoff_nonnegative_of_zero_height hH hheight)

theorem slopeCutoff_ten : slopeCutoff 10 = -(99 / 101 : ℝ) := by
  norm_num [slopeCutoff]

end AngularMaster
