import AWPI.PhiRH.ShiftedSliceFrontier
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace AWPI.PhiRH.NativeZetaSupport

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.TransverseFrontier

/-- At a nontrivial Mathlib zeta zero, Deligne's real gamma factor is nonzero.
The only zeros of `Gammaℝ` are the nonpositive even integers; `0` is excluded
by `riemannZeta_zero`, and the negative even integers are exactly the trivial
zeros excluded by `NontrivialZetaZero`. -/
theorem gammaR_ne_zero_of_nontrivialZetaZero
    (rho : ℂ) (hz : NontrivialZetaZero rho) : rho.Gammaℝ ≠ 0 := by
  intro hGamma
  rcases (Complex.Gammaℝ_eq_zero_iff.mp hGamma) with ⟨n, hn⟩
  cases n with
  | zero =>
      have hrho0 : rho = 0 := by simpa using hn
      exact nontrivialZetaZero_ne_zero rho hz hrho0
  | succ n =>
      apply hz.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ, neg_mul] using hn

/-- A nontrivial zeta zero is also a zero of Mathlib's completed zeta. -/
theorem completedRiemannZeta_eq_zero_of_nontrivialZetaZero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    completedRiemannZeta rho = 0 := by
  have hrho0 : rho ≠ 0 := nontrivialZetaZero_ne_zero rho hz
  have hGamma : rho.Gammaℝ ≠ 0 := gammaR_ne_zero_of_nontrivialZetaZero rho hz
  have hdiv : completedRiemannZeta rho / rho.Gammaℝ = 0 := by
    calc
      completedRiemannZeta rho / rho.Gammaℝ = riemannZeta rho :=
        (riemannZeta_def_of_ne_zero hrho0).symm
      _ = 0 := hz.1
  exact (div_eq_zero_iff.mp hdiv).resolve_right hGamma

/-- Native Mathlib support theorem: every nontrivial zero in our literal
predicate lies strictly in the right half-plane.  This uses only the completed
zeta reflection and Mathlib's zero-free closed half-plane `Re(s) >= 1`. -/
theorem nontrivialZetaZero_re_pos
    (rho : ℂ) (hz : NontrivialZetaZero rho) : 0 < rho.re := by
  by_contra hpos
  have hre_le : rho.re ≤ 0 := le_of_not_gt hpos
  have hcompleted : completedRiemannZeta rho = 0 :=
    completedRiemannZeta_eq_zero_of_nontrivialZetaZero rho hz
  have hreflected : completedRiemannZeta (1 - rho) = 0 := by
    rw [completedRiemannZeta_one_sub rho, hcompleted]
  have hone_sub_ne : (1 - rho : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hz.2.2)
  have hz_reflected : riemannZeta (1 - rho) = 0 := by
    rw [riemannZeta_def_of_ne_zero hone_sub_ne, hreflected]
    simp
  have hre_reflected : 1 ≤ (1 - rho : ℂ).re := by
    simp
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hre_reflected) hz_reflected

/-- Hence the shifted point `rho + 1` lies in Mathlib's zero-free half-plane. -/
theorem shiftedRiemannZeta_ne_zero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    riemannZeta (rho + 1) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  have hpos : 0 < rho.re := nontrivialZetaZero_re_pos rho hz
  simp
  linarith

/-- Once a shifted Phi value is factorized as a nonzero prefactor times the
shifted Riemann zeta value, its nonvanishing follows natively.  Thus the zeta
factor itself is no longer part of the shifted-slice frontier. -/
theorem shiftedSlice_nonzero_of_factorization
    (phiS1 s1Prefactor : ℂ → ℂ)
    (rho : ℂ) (hz : NontrivialZetaZero rho)
    (hfactor :
      phiS1 (rho + 1) = s1Prefactor (rho + 1) * riemannZeta (rho + 1))
    (hprefactor : s1Prefactor (rho + 1) ≠ 0) :
    phiS1 (rho + 1) ≠ 0 := by
  rw [hfactor]
  exact mul_ne_zero hprefactor (shiftedRiemannZeta_ne_zero rho hz)

end AWPI.PhiRH.NativeZetaSupport
