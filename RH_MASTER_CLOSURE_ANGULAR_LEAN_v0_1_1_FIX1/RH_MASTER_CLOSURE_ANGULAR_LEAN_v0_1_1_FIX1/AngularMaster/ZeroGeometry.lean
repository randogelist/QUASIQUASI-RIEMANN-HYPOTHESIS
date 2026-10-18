import AWPIRH.ThetaEntire

/-!
Actual zero geometry for the angular Master.

All functions here are the literal Mathlib-backed xi and its entire descent
from AWPIRH.XiCore.  No abstract zero predicate or analytic bridge is assumed.
The endpoint is Mathlib's native `_root_.RiemannHypothesis`.
-/

set_option autoImplicit false
noncomputable section

namespace AngularMaster

open AWPIRH
open ComplexConjugate

/-- Every zero of the actual completed xi lies on the critical line. -/
def XiZerosCritical : Prop :=
  ∀ s : ℂ, xi s = 0 → s.re = 1 / 2

/-- The actual entire theta has zeros only on the nonpositive real axis. -/
def ThetaZerosNonpositive : Prop :=
  ∀ z : ℂ, theta z = 0 → z.im = 0 ∧ z.re ≤ 0

theorem xi_zero_mem_critical_strip {s : ℂ} (hs : xi s = 0) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hn
    have hle : s.re ≤ 0 := le_of_not_gt hn
    have hre : 1 ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    apply xi_ne_zero_of_one_le_re hre
    rw [xi_reflection]
    exact hs
  · by_contra hn
    exact xi_ne_zero_of_one_le_re (le_of_not_gt hn) hs

theorem nontrivialZero_of_xi_zero {s : ℂ} (hs : xi s = 0) :
    NontrivialZero s := by
  have hstrip := xi_zero_mem_critical_strip hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hstrip
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [xi] using hs
  have h1ms : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hnum : s * completedRiemannZeta₀ s - 1 - s / (1 - s) = 0 := by
    calc
      _ = -(1 + s * (s - 1) * completedRiemannZeta₀ s) / (1 - s) := by
        field_simp [h1ms]
        <;> ring
      _ = 0 := by rw [hraw]; simp
  refine ⟨?_, ?_, hs1⟩
  · rw [riemannZeta_eq_mul_completedRiemannZeta₀, hnum]
    simp
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp [Complex.mul_re] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hstrip.1]

theorem xi_zero_iff_nontrivialZero (s : ℂ) :
    xi s = 0 ↔ NontrivialZero s :=
  ⟨nontrivialZero_of_xi_zero, xi_zero_of_nontrivialZero⟩

/-- Only zero symmetry is needed for angular zero exclusion. -/
theorem xi_zero_conj {s : ℂ} (hs : xi s = 0) : xi (conj s) = 0 := by
  have hstrip := xi_zero_mem_critical_strip hs
  have hz := nontrivialZero_of_xi_zero hs
  apply xi_zero_of_nontrivialZero
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj, hz.1, map_zero]
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp [Complex.mul_re] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hstrip.1]
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hstrip.2]

theorem theta_zero_conj {z : ℂ} (hz : theta z = 0) : theta (conj z) = 0 := by
  have hx : xi ((1 / 2 : ℂ) + Complex.sqrt z) = 0 := hz
  have hxc := xi_zero_conj hx
  have hsq : (conj (Complex.sqrt z)) ^ 2 = conj z := by
    rw [← map_pow, complex_sqrt_sq]
  rw [← hsq, theta_square]
  change xi ((1 / 2 : ℂ) + conj (Complex.sqrt z)) = 0
  have htwo : conj (2 : ℂ) = (2 : ℂ) := Complex.conj_ofNat 2
  simpa [htwo] using hxc

theorem native_RH_iff_xi_zeros_critical :
    _root_.RiemannHypothesis ↔ XiZerosCritical := by
  constructor
  · intro hRH s hs
    have hz := nontrivialZero_of_xi_zero hs
    exact hRH s hz.1 hz.2.1 hz.2.2
  · intro hXi s hz htriv hs1
    exact hXi s (xi_zero_of_nontrivialZero ⟨hz, htriv, hs1⟩)

/-- Squaring converts the imaginary axis to the nonpositive real axis. -/
theorem square_nonpositive_iff_re_zero (w : ℂ) :
    ((w ^ 2).im = 0 ∧ (w ^ 2).re ≤ 0) ↔ w.re = 0 := by
  have him : (w ^ 2).im = 2 * w.re * w.im := by
    simp [pow_two, Complex.mul_im]
    <;> ring
  have hre : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [him, hre]
  constructor
  · rintro ⟨hi, hr⟩
    rcases mul_eq_zero.mp hi with h | h
    · rcases mul_eq_zero.mp h with htwo | hw
      · norm_num at htwo
      · exact hw
    · have hr' : w.re ^ 2 ≤ 0 := by simpa [h] using hr
      exact sq_eq_zero_iff.mp (le_antisymm hr' (sq_nonneg w.re))
  · intro hw
    rw [hw]
    constructor
    · ring
    · simpa using neg_nonpos.mpr (sq_nonneg w.im)

theorem xi_zeros_critical_iff_theta_zeros_nonpositive :
    XiZerosCritical ↔ ThetaZerosNonpositive := by
  constructor
  · intro hXi z hz
    have hs : xi ((1 / 2 : ℂ) + Complex.sqrt z) = 0 := hz
    have hline := hXi _ hs
    have hroot : (Complex.sqrt z).re = 0 := by
      have hhalf : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
      rw [Complex.add_re, hhalf] at hline
      linarith
    have hsq := (square_nonpositive_iff_re_zero (Complex.sqrt z)).2 hroot
    simpa only [complex_sqrt_sq] using hsq
  · intro hTheta s hs
    have hzero : theta ((s - (1 / 2 : ℂ)) ^ 2) = 0 := by
      rw [theta_square]
      have hshift : (1 / 2 : ℂ) + (s - 1 / 2) = s := by ring
      simpa only [centeredXi, hshift] using hs
    have hcenter :=
      (square_nonpositive_iff_re_zero (s - (1 / 2 : ℂ))).1
        (hTheta _ hzero)
    norm_num [Complex.sub_re] at hcenter
    linarith

theorem native_RH_iff_theta_zeros_nonpositive :
    _root_.RiemannHypothesis ↔ ThetaZerosNonpositive :=
  native_RH_iff_xi_zeros_critical.trans
    xi_zeros_critical_iff_theta_zeros_nonpositive

end AngularMaster
