import AWPIRH.ThetaEntire

/-! Actual xi strip membership and conjugation symmetry used by QQRH. -/

set_option autoImplicit false
noncomputable section
namespace AngularMaster
open AWPIRH
open ComplexConjugate

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

end AngularMaster
