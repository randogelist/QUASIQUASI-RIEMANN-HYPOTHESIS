import AngularMaster.Chain
import AngularMaster.QQRH

/-!
The unbounded-slope step is explicit. A fixed QQRH slope is a restricted
zero-free wedge; QQRH at every positive slope is equivalent to native RH.
No assertion of the all-slope premise is made here.
-/

set_option autoImplicit false
noncomputable section
namespace RHMaster

def AllSlopeQQRH : Prop :=
  ∀ m : ℝ, 0 < m → AngularMaster.QQRH m

def CofinalSlopeQQRH : Prop :=
  ∀ M : ℝ, 0 < M → ∃ m : ℝ, M ≤ m ∧ AngularMaster.QQRH m

def AllSlopePositivity : Prop :=
  ∀ m : ℝ, 0 < m →
    AngularMaster.CutoffDerivativeNonnegative (AngularMaster.slopeCutoff m)

theorem qqrh_mono {m n : ℝ} (hmn : m ≤ n)
    (hn : AngularMaster.QQRH n) : AngularMaster.QQRH m := by
  intro s hs0 hs1 hwedge
  exact hn s hs0 hs1
    (lt_of_lt_of_le hwedge (mul_le_mul_of_nonneg_right hmn (abs_nonneg _)))

theorem allSlopeQQRH_of_cofinal (h : CofinalSlopeQQRH) : AllSlopeQQRH := by
  intro M hM
  obtain ⟨m, hMm, hm⟩ := h M hM
  exact qqrh_mono hMm hm

theorem cofinalSlopeQQRH_of_all (h : AllSlopeQQRH) : CofinalSlopeQQRH := by
  intro M hM
  exact ⟨M, le_rfl, h M hM⟩

theorem rh_of_allSlopeQQRH (h : AllSlopeQQRH) : _root_.RiemannHypothesis := by
  apply AngularMaster.native_RH_iff_xi_zeros_critical.mpr
  intro s hs
  by_contra hline
  have hstrip := AngularMaster.xi_zero_mem_critical_strip hs
  have hz := AngularMaster.nontrivialZero_of_xi_zero hs
  have hd : 0 < |s.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hline)
  let m : ℝ := (|s.im| + 1) / |s.re - 1 / 2|
  have hm : 0 < m := div_pos (by linarith [abs_nonneg s.im]) hd
  have hwedge : |s.im| < m * |s.re - 1 / 2| := by
    dsimp [m]
    rw [div_mul_cancel₀ _ (ne_of_gt hd)]
    linarith
  exact h m hm s hstrip.1 hstrip.2 hwedge hz.1

theorem allSlopeQQRH_of_rh (hRH : _root_.RiemannHypothesis) : AllSlopeQQRH := by
  intro m hm s hs0 hs1 hwedge hzeta
  have hnontrivial : AWPIRH.NontrivialZero s := by
    refine ⟨hzeta, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp [Complex.mul_re] at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
  have hline := hRH s hnontrivial.1 hnontrivial.2.1 hnontrivial.2.2
  rw [hline, sub_self, abs_zero, mul_zero] at hwedge
  exact (not_lt_of_ge (abs_nonneg s.im)) hwedge

theorem rh_iff_allSlopeQQRH : _root_.RiemannHypothesis ↔ AllSlopeQQRH :=
  ⟨allSlopeQQRH_of_rh, rh_of_allSlopeQQRH⟩

theorem rh_iff_cofinalSlopeQQRH : _root_.RiemannHypothesis ↔ CofinalSlopeQQRH :=
  ⟨fun h => cofinalSlopeQQRH_of_all (allSlopeQQRH_of_rh h),
    fun h => rh_of_allSlopeQQRH (allSlopeQQRH_of_cofinal h)⟩

theorem allSlopeQQRH_of_allSlopePositivity (h : AllSlopePositivity) : AllSlopeQQRH := by
  intro m hm
  exact AngularMaster.QQRH_of_angular_positivity hm (h m hm)

theorem rh_of_allSlopePositivity (h : AllSlopePositivity) : _root_.RiemannHypothesis :=
  rh_of_allSlopeQQRH (allSlopeQQRH_of_allSlopePositivity h)

theorem allSlopePositivity_of_rh (hRH : _root_.RiemannHypothesis) :
    AllSlopePositivity := by
  have hd := AngularMaster.derivativeNonnegative_of_profileMaster
    (AngularMaster.native_RH_iff_actual_profileMaster.mp hRH)
  intro m hm r hr x hx
  exact hd r hr x
    ⟨(lt_trans (AngularMaster.slopeCutoff_mem_Ioo hm).1 hx.1).le, hx.2.le⟩

theorem rh_iff_allSlopePositivity :
    _root_.RiemannHypothesis ↔ AllSlopePositivity :=
  ⟨allSlopePositivity_of_rh, rh_of_allSlopePositivity⟩

end RHMaster
