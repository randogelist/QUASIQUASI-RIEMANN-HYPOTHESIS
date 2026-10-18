import AWPI.PhiRH.NativeZetaSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AWPI.PhiRH.S1Prefactor

open AWPI.PhiRH
open AWPI.PhiRH.MathlibBridge
open AWPI.PhiRH.NativeZetaSupport
open AWPI.PhiRH.ShiftedSliceFrontier
open AWPI.PhiRH.TransverseFrontier
open AWPI.PhiRH.RocqPortModel
open AWPI.PhiRH.ActivityFrontier

/-- Native complex version of the explicit Rocq S₁ prefactor

    4 * 2^(-s) * (1 - 2^(1-s)).

The Rocq development represented complex numbers by real pairs; here we use
Mathlib's actual complex power. -/
noncomputable def s1Prefactor (s : ℂ) : ℂ :=
  (4 : ℂ) * ((2 : ℂ) ^ (-s)) * (1 - (2 : ℂ) ^ (1 - s))

/-- The dyadic complex-power factor is never zero because the base 2 is nonzero. -/
theorem two_cpow_ne_zero (s : ℂ) : (2 : ℂ) ^ s ≠ 0 := by
  exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num))

/-- For a nontrivial zeta zero rho, |2^(-rho)| < 1 because Re rho > 0.
Hence the Euler factor `1 - 2^(-rho)` is nonzero. -/
theorem one_sub_two_cpow_neg_ne_zero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    1 - (2 : ℂ) ^ (-rho) ≠ 0 := by
  have hre : 0 < rho.re := nontrivialZetaZero_re_pos rho hz
  have hnormNat : ‖(((2 : ℕ) : ℂ) ^ (-rho))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (n := 2) (by norm_num) (-rho)]
    change (2 : ℝ) ^ (-rho.re) < 1
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hre)
  have hnorm : ‖(2 : ℂ) ^ (-rho)‖ < 1 := by
    simpa using hnormNat
  intro hzero
  have hone : (2 : ℂ) ^ (-rho) = 1 := (sub_eq_zero.mp hzero).symm
  rw [hone] at hnorm
  norm_num at hnorm

/-- The explicit S₁ prefactor is nonzero at the shifted point rho+1 of every
nontrivial zeta zero.  No project hypothesis is used here. -/
theorem s1Prefactor_shifted_ne_zero
    (rho : ℂ) (hz : NontrivialZetaZero rho) :
    s1Prefactor (rho + 1) ≠ 0 := by
  unfold s1Prefactor
  apply mul_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact two_cpow_ne_zero (-(rho + 1))
  · have hEuler := one_sub_two_cpow_neg_ne_zero rho hz
    have hexp : (1 : ℂ) - (rho + 1) = -rho := by ring
    simpa [hexp] using hEuler

/-- The shifted-slice nonvanishing frontier is therefore reduced to the single
actual Phi-zeta value identity.  The prefactor and shifted zeta factors are
both proved nonzero natively. -/
theorem shiftedSlice_nonzero_of_phi_zeta_value_identity
    (phiS1 : ℂ → ℂ)
    (rho : ℂ) (hz : NontrivialZetaZero rho)
    (hfactor :
      phiS1 (rho + 1) =
        s1Prefactor (rho + 1) * riemannZeta (rho + 1)) :
    phiS1 (rho + 1) ≠ 0 := by
  exact shiftedSlice_nonzero_of_factorization
    phiS1 s1Prefactor rho hz hfactor (s1Prefactor_shifted_ne_zero rho hz)

/-- Native RH closure with shifted-slice nonvanishing no longer assumed.
The shifted-slice branch now exposes only the actual S₁ Phi-zeta value identity. -/
theorem MATHLIB_RH_OF_SEVEN_PHI_ZETA_FRONTIER_LEAVES
    (phiS1 : ℂ → ℂ)
    (phiTransverseJet plusJetScale minusJetScale : ℂ → ℝ)
    (actualKQPlusSource actualKQMinusSource : ℕ → ℝ → ℝ → ℝ)
    (finitePlusSquare finiteMinusSquare : ℕ → ℂ → ℝ)
    (phiZetaValueIdentity :
      ∀ rho : ℂ, NontrivialZetaZero rho →
        phiS1 (rho + 1) =
          s1Prefactor (rho + 1) * riemannZeta (rho + 1))
    (transverseNorm2_identity :
      ∀ rho : ℂ, NontrivialZetaZero rho →
        phiTransverseJet rho = rhoNorm2 rho * shiftedPhiNorm2 phiS1 rho)
    (plusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → plusJetScale rho ≠ 0)
    (minusBindingScale_nonzero :
      ∀ rho : ℂ, NontrivialZetaZero rho → minusJetScale rho ≠ 0)
    (plusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetPlus plusJetScale phiTransverseJet rho) ^ 2 -
            (boundJetPlus plusJetScale phiTransverseJet rho) ^ 2 ≤
          -(finitePlusSquare n rho) ^ 2 +
            actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im)
    (minusExactToNegativeSquareTailUpper :
      ∀ (n : ℕ) (rho : ℂ), NontrivialZetaZero rho →
        scale2 (-2 * (rho.re - (1 / 2 : ℝ))) *
              (boundJetMinus minusJetScale phiTransverseJet rho) ^ 2 -
            (boundJetMinus minusJetScale phiTransverseJet rho) ^ 2 ≤
          -(finiteMinusSquare n rho) ^ 2 +
            actualKQMinusSource n rho.re rho.im *
              actualKQMinusSource n rho.re rho.im)
    (jointTailDecay :
      ∀ (rho : ℂ) (eps : ℝ), NontrivialZetaZero rho → 0 < eps →
        ∃ n : ℕ,
          actualKQPlusSource n rho.re rho.im *
              actualKQPlusSource n rho.re rho.im ≤ eps ∧
          actualKQMinusSource n rho.re rho.im *
              actualKQMinusSource n rho.re rho.im ≤ eps) :
    RiemannHypothesis := by
  apply MATHLIB_RH_OF_SEVEN_SHIFTED_SLICE_FRONTIER_LEAVES
    phiS1 phiTransverseJet plusJetScale minusJetScale
    actualKQPlusSource actualKQMinusSource
    finitePlusSquare finiteMinusSquare
  · intro rho hz
    exact shiftedSlice_nonzero_of_phi_zeta_value_identity
      phiS1 rho hz (phiZetaValueIdentity rho hz)
  · exact transverseNorm2_identity
  · exact plusBindingScale_nonzero
  · exact minusBindingScale_nonzero
  · exact plusExactToNegativeSquareTailUpper
  · exact minusExactToNegativeSquareTailUpper
  · exact jointTailDecay

end AWPI.PhiRH.S1Prefactor
