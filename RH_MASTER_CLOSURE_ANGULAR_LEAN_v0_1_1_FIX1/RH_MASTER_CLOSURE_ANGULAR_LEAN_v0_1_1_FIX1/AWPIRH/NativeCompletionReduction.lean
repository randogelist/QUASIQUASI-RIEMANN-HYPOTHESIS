import AWPIRH.NativeGermReduction

/-!
Reduction of `NativeXiAnchorGerm` to the literal Mellin identity for the fixed
native density.  No zeta/Mellin identity is assumed inside `US_AWPI`.
The completion algebra is proved separately so the remaining integral theorem
has exactly one mathematical content:

  nativeMellin(s) = Gamma(s) * (s-1) * zeta(s)

near the real anchor s = 3/2.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology Real
open Filter
namespace AWPIRH

/-- The literal Mellin identity, restricted to the fixed log-anchor germ. -/
def NativeMellinAnchorGerm : Prop :=
  (fun y : ℝ => nativeMellin (anchorPoint y)) =ᶠ[𝓝 (0 : ℝ)]
    (fun y : ℝ =>
      Complex.Gamma (anchorPoint y) * (anchorPoint y - 1) *
        riemannZeta (anchorPoint y))

private theorem two_sqrt_pi_pos : 0 < 2 * Real.sqrt Real.pi := by
  positivity

/-- The exponential denominator used in `nativeCompletion` is exactly the
positive-real complex power `(2*sqrt(pi))^s`. -/
theorem nativeCompletion_exp_eq_cpow (s : ℂ) :
    Complex.exp
        (s * (Real.log (2 * Real.sqrt Real.pi) : ℂ)) =
      ((2 * Real.sqrt Real.pi : ℝ) : ℂ) ^ s := by
  have hR : (0 : ℝ) < 2 * Real.sqrt Real.pi := two_sqrt_pi_pos
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne')]
  rw [← Complex.ofReal_log hR.le]
  congr 1
  ring

/-- Split the positive base in the native completion into the powers occurring
in the standard completed-zeta normalization. -/
theorem two_sqrt_pi_cpow (s : ℂ) :
    ((2 * Real.sqrt Real.pi : ℝ) : ℂ) ^ s =
      (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hsqrt : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hmul :
      ((2 * Real.sqrt Real.pi : ℝ) : ℂ) ^ s =
        (((2 : ℝ) : ℂ) ^ s) *
          (((Real.sqrt Real.pi : ℝ) : ℂ) ^ s) := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg h2 hsqrt s
  have hsqrtpow :
      (((Real.sqrt Real.pi : ℝ) : ℂ) ^ s) =
        (Real.pi : ℂ) ^ (s / 2) := by
    have hsqrt0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hpi0 : (Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    rw [Complex.cpow_def_of_ne_zero hsqrt0,
      Complex.cpow_def_of_ne_zero hpi0]
    rw [← Complex.ofReal_log (Real.sqrt_nonneg Real.pi),
      ← Complex.ofReal_log Real.pi_pos.le]
    rw [Real.log_sqrt Real.pi_pos.le]
    congr 1
    push_cast
    ring
  calc
    ((2 * Real.sqrt Real.pi : ℝ) : ℂ) ^ s =
        (((2 : ℝ) : ℂ) ^ s) *
          (((Real.sqrt Real.pi : ℝ) : ℂ) ^ s) := hmul
    _ = (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) := by
      rw [hsqrtpow]
      norm_num

private theorem div_two_re (s : ℂ) :
    (s / 2).re = s.re / 2 := by
  norm_num [Complex.div_re, Complex.normSq_apply]

private theorem add_one_div_two_re (s : ℂ) :
    ((s + 1) / 2).re = (s.re + 1) / 2 := by
  norm_num [Complex.div_re, Complex.normSq_apply]

/-- The native prefactor was chosen so that, after multiplying by Gamma(s),
it is exactly `s/2` times the standard archimedean Gamma factor. -/
theorem nativeCompletion_mul_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    nativeCompletion s * Complex.Gamma s =
      (s / 2) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
  have hs2 : 0 < (s / 2).re := by
    rw [div_two_re]
    linarith
  have hsp : 0 < ((s + 1) / 2).re := by
    rw [add_one_div_two_re]
    linarith
  have hG2 : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs2
  have hGp : Complex.Gamma ((s + 1) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hsp
  have hdup :
      Complex.Gamma (s / 2) * Complex.Gamma ((s + 1) / 2) =
        Complex.Gamma s * (2 : ℂ) ^ (1 - s) *
          (Real.sqrt Real.pi : ℂ) := by
    convert Complex.Gamma_mul_Gamma_add_half (s / 2) using 1 <;> ring
  have h2pow : (2 : ℂ) ^ s ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  have hpipow : (Real.pi : ℂ) ^ (s / 2) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
  have hpiNeg : (Real.pi : ℂ) ^ (-s / 2) =
      ((Real.pi : ℂ) ^ (s / 2))⁻¹ := by
    rw [show -s / 2 = -(s / 2) by ring, Complex.cpow_neg]
  have htwo :
      (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ s = 2 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    norm_num
  rw [nativeCompletion, nativeCompletion_exp_eq_cpow,
    two_sqrt_pi_cpow, hpiNeg]
  field_simp [hGp, h2pow, hpipow]
  calc
    s * (Real.sqrt Real.pi : ℂ) * 2 * Complex.Gamma s =
        s * (Real.sqrt Real.pi : ℂ) *
          ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ s) * Complex.Gamma s := by
      rw [htwo]
    _ = s * (2 : ℂ) ^ s *
        (Complex.Gamma s * (2 : ℂ) ^ (1 - s) *
          (Real.sqrt Real.pi : ℂ)) := by ring
    _ = s * (2 : ℂ) ^ s *
        (Complex.Gamma (s / 2) * Complex.Gamma ((s + 1) / 2)) := by
      rw [hdup]
    _ = s * (2 : ℂ) ^ s * Complex.Gamma ((s + 1) / 2) *
        Complex.Gamma (s / 2) := by ring

/-- Completion algebra: once the Mellin transform has the classical zeta value,
the literal native object is Mathlib's actual xi. -/
theorem nativeXi_eq_xi_of_mellin_eq
    {s : ℂ} (hs : 1 < s.re)
    (hM : nativeMellin s =
      Complex.Gamma s * (s - 1) * riemannZeta s) :
    nativeXi s = xi s := by
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  have hcomp := nativeCompletion_mul_Gamma (s := s) hspos
  have hcompleted :
      completedRiemannZeta s =
        (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
          riemannZeta s := by
    rw [completedZeta_eq_tsum_of_one_lt_re hs,
      ← zeta_eq_tsum_one_div_nat_cpow hs]
  rw [nativeXi, hM]
  calc
    nativeCompletion s *
        (Complex.Gamma s * (s - 1) * riemannZeta s) =
      (nativeCompletion s * Complex.Gamma s) *
        (s - 1) * riemannZeta s := by ring
    _ = ((s / 2) * (Real.pi : ℂ) ^ (-s / 2) *
          Complex.Gamma (s / 2)) * (s - 1) * riemannZeta s := by
        rw [hcomp]
    _ = (s * (s - 1) / 2) * completedRiemannZeta s := by
        rw [hcompleted]
        ring
    _ = xi s := (xi_eq_completed hs0 hs1).symm

/-- The anchor remains in the absolute-convergence half-plane on a neighbourhood
of zero. -/
theorem anchorPoint_re_gt_one_eventually :
    ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), 1 < (anchorPoint y).re := by
  have hcont : ContinuousAt (fun y : ℝ => (anchorPoint y).re) 0 := by
    unfold anchorPoint
    fun_prop
  have h0 : 1 < (anchorPoint 0).re := by norm_num [anchorPoint]
  exact (hcont.eventually (eventually_gt_nhds h0))

/-- The first of the two v0.9 germs is reduced to the literal Mellin identity. -/
theorem NATIVE_XI_ANCHOR_GERM_OF_MELLIN_GERM
    (hM : NativeMellinAnchorGerm) : NativeXiAnchorGerm := by
  filter_upwards [hM, anchorPoint_re_gt_one_eventually] with y hMy hy
  exact nativeXi_eq_xi_of_mellin_eq hy hMy

/-- Forward assembly after replacing the native-xi germ by the exact Mellin
identity.  This is still NOT the final one-premise theorem. -/
theorem MATHLIB_RH_OF_US_MELLIN_GERM_AND_PRODUCT_GERM
    (hUS : US_AWPI)
    (hM : NativeMellinAnchorGerm)
    (hProd : XiWidderProductCoefficientIdentity) :
    _root_.RiemannHypothesis := by
  exact MATHLIB_RH_OF_US_AND_NATIVE_GERMS hUS
    (NATIVE_XI_ANCHOR_GERM_OF_MELLIN_GERM hM) hProd

end AWPIRH
