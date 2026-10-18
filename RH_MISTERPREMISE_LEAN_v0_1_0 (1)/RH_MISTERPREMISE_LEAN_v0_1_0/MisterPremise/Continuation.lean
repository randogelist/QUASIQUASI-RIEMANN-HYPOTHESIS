import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive continuation from a one-sided differential bound

The derivative bound is required only at points where the function is positive.
The proof takes a greatest nonpositive point and applies an exponential
integrating factor on the positive interval to its right. No nonvanishing
hypothesis is assumed on the interval being continued across.
-/

noncomputable section

open Set

namespace MisterPremise

set_option backward.isDefEq.respectTransparency false in
/-- A positive right endpoint cannot be reached from a nonpositive value if
`f' ≤ K f` holds wherever `f` is positive. -/
theorem positive_on_Icc_of_deriv_le_mul_on_pos
    {f : ℝ → ℝ} {a b K : ℝ}
    (_hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hpos : 0 < f b)
    (hbound : ∀ t ∈ Ioo a b, 0 < f t → deriv f t ≤ K * f t) :
    ∀ x ∈ Icc a b, 0 < f x := by
  intro x hx
  by_contra hn
  have hxnonpos : f x ≤ 0 := le_of_not_gt hn
  have hcont' : ContinuousOn f (Icc x b) :=
    hcont.mono (fun t ht => ⟨hx.1.trans ht.1, ht.2⟩)
  let S : Set ℝ := Icc x b ∩ f ⁻¹' Iic 0
  have hcompact : IsCompact S :=
    hcont'.lowerSemicontinuousOn.isCompact_inter_preimage_Iic isCompact_Icc 0
  have hnonempty : S.Nonempty := ⟨x, ⟨⟨le_rfl, hx.2⟩, hxnonpos⟩⟩
  obtain ⟨c, hc⟩ := hcompact.exists_isGreatest hnonempty
  have hcinterval : c ∈ Icc x b := hc.1.1
  have hcnonpos : f c ≤ 0 := hc.1.2
  have hcb : c < b := by
    apply lt_of_le_of_ne hcinterval.2
    intro heq
    subst c
    exact (not_le_of_gt hpos) hcnonpos
  have hpositive : ∀ t ∈ Ioo c b, 0 < f t := by
    intro t ht
    by_contra htpos
    have htS : t ∈ S :=
      ⟨⟨hcinterval.1.trans ht.1.le, ht.2.le⟩, le_of_not_gt htpos⟩
    exact (not_le_of_gt ht.1) (hc.2 htS)
  let g : ℝ → ℝ := fun t => Real.exp (-K * t) * f t
  have hgcont : ContinuousOn g (Icc c b) := by
    have he : Continuous (fun t : ℝ => Real.exp (-K * t)) := by fun_prop
    exact he.continuousOn.mul
      (hcont.mono (fun t ht => ⟨(hx.1.trans hcinterval.1).trans ht.1, ht.2⟩))
  have hgderiv : ∀ t ∈ Ioo c b,
      HasDerivAt g (Real.exp (-K * t) * (deriv f t - K * f t)) t := by
    intro t ht
    have htf : DifferentiableAt ℝ f t :=
      hdiff t ⟨lt_of_le_of_lt (hx.1.trans hcinterval.1) ht.1, ht.2⟩
    have he := ((hasDerivAt_id t).const_mul (-K)).exp
    have hgraw : HasDerivAt g
        (Real.exp (-K * t) * deriv f t + Real.exp (-K * t) * (-K) * f t) t := by
      convert! he.smul htf.hasDerivAt using 1
      simp only [id_eq, smul_eq_mul]
      ring
    have hcoef : Real.exp (-K * t) * deriv f t + Real.exp (-K * t) * (-K) * f t =
        Real.exp (-K * t) * (deriv f t - K * f t) := by ring
    rwa [hcoef] at hgraw
  have hganti : AntitoneOn g (Icc c b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc c b) hgcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hgderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hgderiv t ht).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      exact sub_nonpos.mpr
        (hbound t ⟨lt_of_le_of_lt (hx.1.trans hcinterval.1) ht.1, ht.2⟩
          (hpositive t ht))
  have hgb : g b ≤ 0 :=
    (hganti ⟨le_rfl, hcb.le⟩ ⟨hcb.le, le_rfl⟩ hcb.le).trans
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hcnonpos)
  have hgbpos : 0 < g b := mul_pos (Real.exp_pos _) hpos
  exact (not_le_of_gt hgbpos) hgb

/-- A weight vanishing at the excluded endpoint still prevents every interior
zero. The constant need only be fixed for this one interval/radius. -/
theorem positive_on_Ioc_of_weighted_deriv_upper_bound
    {f : ℝ → ℝ} {b M : ℝ}
    (_hb : -1 < b)
    (hcont : ContinuousOn f (Ioc (-1) b))
    (hdiff : ∀ t ∈ Ioo (-1) b, DifferentiableAt ℝ f t)
    (hpos : 0 < f b)
    (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Ioc (-1) b, 0 < f t →
      (1 + t) * deriv f t ≤ M * f t) :
    ∀ x ∈ Ioc (-1) b, 0 < f x := by
  intro x hx
  have hxweight : 0 < 1 + x := by linarith [hx.1]
  have hcont' : ContinuousOn f (Icc x b) :=
    hcont.mono (fun t ht => ⟨lt_of_lt_of_le hx.1 ht.1, ht.2⟩)
  have hdiff' : ∀ t ∈ Ioo x b, DifferentiableAt ℝ f t := by
    intro t ht
    exact hdiff t ⟨hx.1.trans ht.1, ht.2⟩
  have hbound' : ∀ t ∈ Ioo x b, 0 < f t →
      deriv f t ≤ (M / (1 + x)) * f t := by
    intro t ht htpos
    have htweight : 0 < 1 + t := by linarith [hx.1, ht.1]
    have hw := hbound t ⟨hx.1.trans ht.1, ht.2.le⟩ htpos
    calc
      deriv f t ≤ (M * f t) / (1 + t) := by
        apply (le_div_iff₀ htweight).mpr
        simpa only [mul_comm] using hw
      _ ≤ (M * f t) / (1 + x) :=
        div_le_div_of_nonneg_left (mul_nonneg hM htpos.le) hxweight
          (by linarith [ht.1])
      _ = (M / (1 + x)) * f t := by ring
  exact positive_on_Icc_of_deriv_le_mul_on_pos hx.2 hcont' hdiff' hpos hbound'
    x ⟨le_rfl, hx.2⟩

end MisterPremise
