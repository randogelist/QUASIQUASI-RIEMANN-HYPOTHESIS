import Derivations.Negativity.UniformChannelBounds
import Mathlib

namespace NativeSoloboloNegativity

open Complex
open Filter
open scoped Topology

noncomputable section

/-- r=|beta/gamma| and R=|t| parameterize the chosen conjugate pair. -/
def skewChannel (R r : ℝ) : ℂ :=
  (R : ℂ) * (1 - (r : ℂ) * I) / (1 + (r : ℂ) * I)

def rationalAnchor (R v : ℝ) : ℝ := R * (1 + v) / (1 - v)

def phaseAmplitude (r v : ℝ) : ℝ :=
  (1 + r ^ 2) * (1 - v ^ 2) / (1 + (r * v) ^ 2)

def phaseFactor (x : ℝ) : ℂ :=
  (1 - (x : ℂ) * I) / (1 + (x : ℂ) * I)

theorem ONE_ADD_IMAGINARY_NE_ZERO (x : ℝ) :
    (1 + (x : ℂ) * I) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem RATIONAL_ANCHOR_POSITIVE
    (R v : ℝ) (hR : 0 < R) (hv0 : -1 < v) (hv1 : v < 1) :
    0 < rationalAnchor R v := by
  unfold rationalAnchor
  exact div_pos (mul_pos hR (by linarith)) (by linarith)

/-- The exact denominator-clearing identity avoids any complex square root. -/
theorem SKEW_CHANNEL_DENOMINATOR_IDENTITY
    (R r v : ℝ) (hv : v ≠ 1) :
    (((rationalAnchor R v : ℝ) : ℂ) + skewChannel R r) *
        ((1 - (v : ℂ)) * (1 + (r : ℂ) * I)) =
      2 * (R : ℂ) * (1 + ((r * v : ℝ) : ℂ) * I) := by
  have hvC : 1 - (v : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hv))
  have hir := ONE_ADD_IMAGINARY_NE_ZERO r
  unfold rationalAnchor skewChannel
  push_cast
  field_simp [hvC, hir] <;> ring

/-- Exact rational formula for the moving-anchor Cayley value. -/
theorem CAYLEY_AT_RATIONAL_ANCHOR
    (R r v : ℝ) (hR : R ≠ 0) (hv : v ≠ 1) :
    channelQ (rationalAnchor R v) (skewChannel R r) =
      (((1 + r ^ 2) * (1 - v ^ 2) : ℝ) : ℂ) /
        (1 + ((r * v : ℝ) : ℂ) * I) ^ 2 := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hvC : 1 - (v : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hv))
  have hir := ONE_ADD_IMAGINARY_NE_ZERO r
  have hiv := ONE_ADD_IMAGINARY_NE_ZERO (r * v)
  have hat : ((rationalAnchor R v : ℝ) : ℂ) + skewChannel R r ≠ 0 := by
    intro h
    have hid := SKEW_CHANNEL_DENOMINATOR_IDENTITY R r v hv
    rw [h, zero_mul] at hid
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hRC) hiv) hid.symm
  unfold channelQ NativeSolobolo.Derivations.Geometry.cayleyChannelQ
  -- Use the cleared denominator as an equation before substituting the channel.
  apply (div_eq_div_iff (pow_ne_zero 2 hat) (pow_ne_zero 2 hiv)).2
  unfold rationalAnchor skewChannel
  push_cast
  field_simp [hvC, hir]
  apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- Clear the conjugate factors before taking any components or inverses.
    This is a polynomial identity; no denominator hypothesis is required. -/
theorem ONE_MINUS_MUL_ONE_PLUS_IMAGINARY (x : ℝ) :
    (1 - (x : ℂ) * I) * (1 + (x : ℂ) * I) =
      ((1 + x ^ 2 : ℝ) : ℂ) := by
  calc
    (1 - (x : ℂ) * I) * (1 + (x : ℂ) * I) =
        1 - (x : ℂ) ^ 2 * I ^ 2 := by ring
    _ = ((1 + x ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.I_sq, Complex.ofReal_add,
        Complex.ofReal_one, Complex.ofReal_pow] <;> ring

/-- A convenient polar-free phase decomposition of the same rational value. -/
theorem RATIONAL_CHANNEL_EQUALS_AMPLITUDE_TIMES_PHASE
    (R r v : ℝ) (hR : R ≠ 0) (hv : v ≠ 1) :
    channelQ (rationalAnchor R v) (skewChannel R r) =
      (phaseAmplitude r v : ℂ) * phaseFactor (r * v) := by
  rw [CAYLEY_AT_RATIONAL_ANCHOR R r v hR hv]
  have hiv := ONE_ADD_IMAGINARY_NE_ZERO (r * v)
  have hreal : (1 + (r * v) ^ 2 : ℝ) ≠ 0 := by positivity
  have hC : ((1 + (r * v) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
  have hproduct := ONE_MINUS_MUL_ONE_PLUS_IMAGINARY (r * v)
  -- Keep each real-to-complex cast intact until both denominators are cleared.
  unfold phaseAmplitude phaseFactor
  rw [Complex.ofReal_div, div_mul_div_comm]
  apply (div_eq_div_iff (pow_ne_zero 2 hiv) (mul_ne_zero hC hiv)).2
  rw [← hproduct]
  ring

/-- Generic phase rule: once the phase is an mth root of -1, its channel
    power is exactly negative, with no real-part approximation. -/
theorem AMPLITUDE_PHASE_POWER
    (q z : ℂ) (b : ℝ) (m : ℕ)
    (hq : q = (b : ℂ) * z) (hz : z ^ m = -1) :
    q ^ m = -((b ^ m : ℝ) : ℂ) := by
  rw [hq, mul_pow, hz]
  simp

/-- A concrete mth root of -1. The remaining geometric use of this root must
    be proved by matching it to the rational Cayley phase. -/
def negativeUnitPhase (m : ℕ) : ℂ :=
  Complex.exp (((Real.pi : ℝ) : ℂ) * I / (m : ℂ))

theorem NEGATIVE_UNIT_PHASE_POW (m : ℕ) (hm : 0 < m) :
    negativeUnitPhase m ^ m = -1 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold negativeUnitPhase
  rw [← Complex.exp_nat_mul]
  have hexp : (m : ℂ) * (((Real.pi : ℝ) : ℂ) * I / (m : ℂ)) =
      ((Real.pi : ℝ) : ℂ) * I := by field_simp [hmC]
  rw [hexp]
  exact Complex.exp_pi_mul_I

/-- A tuned displacement tending to zero makes its amplitude tend to 1+r^2.
No O(1/N) threshold is asserted. -/
theorem PHASE_AMPLITUDE_TENDS_TO_PEAK
    (r : ℝ) (v : ℕ → ℝ) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => phaseAmplitude r (v n)) atTop (𝓝 (1 + r ^ 2)) := by
  have hnum :
      Tendsto (fun n => (1 + r ^ 2) * (1 - (v n) ^ 2)) atTop
        (𝓝 ((1 + r ^ 2) * (1 - (0 : ℝ) ^ 2))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub (hv.pow 2))
  have hden :
      Tendsto (fun n => 1 + (r * v n) ^ 2) atTop
        (𝓝 (1 + (r * (0 : ℝ)) ^ 2)) :=
    tendsto_const_nhds.add ((tendsto_const_nhds.mul hv).pow 2)
  have hden0 : (1 + (r * (0 : ℝ)) ^ 2 : ℝ) ≠ 0 := by norm_num
  have hquot :
      Tendsto
        (fun n => ((1 + r ^ 2) * (1 - (v n) ^ 2)) /
          (1 + (r * v n) ^ 2)) atTop
        (𝓝 (((1 + r ^ 2) * (1 - (0 : ℝ) ^ 2)) /
          (1 + (r * (0 : ℝ)) ^ 2))) :=
    hnum.div hden hden0
  simpa [phaseAmplitude] using hquot

end
end NativeSoloboloNegativity
