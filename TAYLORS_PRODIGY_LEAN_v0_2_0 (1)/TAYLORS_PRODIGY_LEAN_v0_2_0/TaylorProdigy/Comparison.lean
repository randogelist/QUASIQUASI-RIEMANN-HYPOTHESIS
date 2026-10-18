import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory
open scoped Topology

namespace TaylorsProdigy

/-- A one-sided logarithmic comparison.  The rate need only be Lebesgue
integrable; no continuity or bound on the rate is assumed. -/
theorem log_lower_bound_of_positive
    {f rate : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hpos : ∀ t ∈ Icc a b, 0 < f t)
    (hi : IntegrableOn rate (Icc a b))
    (hr : ∀ t ∈ Ioo a b, -rate t * f t ≤ deriv f t) :
    Real.log (f a) - (∫ t in a..b, rate t) ≤ Real.log (f b) := by
  have hlog : ContinuousOn (fun t => -Real.log (f t)) (Icc a b) :=
    (hf.log (fun t ht => ne_of_gt (hpos t ht))).neg
  have hlogd : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun t => -Real.log (f t))
        (-(deriv f t / f t)) (Ioi t) t := by
    intro t ht
    exact ((hd t ht).hasDerivAt.log (ne_of_gt (hpos t ⟨ht.1.le, ht.2.le⟩))).neg.hasDerivWithinAt
  have hrate : ∀ t ∈ Ioo a b, -(deriv f t / f t) ≤ rate t := by
    intro t ht
    have hp := hpos t ⟨ht.1.le, ht.2.le⟩
    have hb := hr t ht
    apply (neg_le_iff_add_nonneg).2
    have hdiv : -rate t ≤ deriv f t / f t :=
      (le_div_iff₀ hp).2 (by simpa only [neg_mul] using hb)
    linarith
  have hbound := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hab hlog hlogd hi hrate
  linarith

/-- An integrable nonnegative relative decay rate prevents a first zero.
The differential inequality is required only while the signal is positive. -/
theorem positive_of_integrable_relative_decay
    {f rate : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hseed : 0 < f a)
    (hi : IntegrableOn rate (Icc a b))
    (hn : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hr : ∀ t ∈ Ioo a b, 0 < f t → -rate t * f t ≤ deriv f t) :
    0 < f b := by
  by_contra hlast
  have hlast : f b ≤ 0 := le_of_not_gt hlast
  let bad : Set ℝ := Icc a b ∩ f ⁻¹' Iic 0
  have hbadclosed : IsClosed bad :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hbadcompact : IsCompact bad :=
    isCompact_Icc.of_isClosed_subset hbadclosed inter_subset_left
  obtain ⟨z, hz⟩ := hbadcompact.exists_isLeast ⟨b, ⟨⟨hab, le_rfl⟩, hlast⟩⟩
  have haz : a < z := by
    have hza := hz.1.1.1
    have hne : a ≠ z := by
      intro heq
      have hzero := hz.1.2
      rw [← heq] at hzero
      change f a ≤ 0 at hzero
      linarith
    exact lt_of_le_of_ne hza hne
  have hzb : z ≤ b := hz.1.1.2
  have hbefore : ∀ t ∈ Ico a z, 0 < f t := by
    intro t ht
    by_contra h
    have hft : f t ≤ 0 := le_of_not_gt h
    have hzt : z ≤ t := hz.2 ⟨⟨ht.1, ht.2.le.trans hzb⟩, hft⟩
    linarith [ht.2]
  let K : ℝ := Real.exp (Real.log (f a) - ∫ t in a..b, rate t)
  have hK : 0 < K := Real.exp_pos _
  have hbound : ∀ t ∈ Ico a z, K ≤ f t := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b :=
      Icc_subset_Icc le_rfl (ht.2.le.trans hzb)
    have hp : ∀ u ∈ Icc a t, 0 < f u := by
      intro u hu
      exact hbefore u ⟨hu.1, hu.2.trans_lt ht.2⟩
    have hiat : IntegrableOn rate (Icc a t) := hi.mono_set hsub
    have hlog := log_lower_bound_of_positive ht.1 (hf.mono hsub)
      (fun u hu => hd u ⟨hu.1, hu.2.trans_le (ht.2.le.trans hzb)⟩)
      hp hiat (fun u hu => hr u ⟨hu.1, hu.2.trans_le (ht.2.le.trans hzb)⟩ (hp u ⟨hu.1.le, hu.2.le⟩))
    have htotal : (∫ u in a..t, rate u) ≤ ∫ u in a..b, rate u := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 (ht.2.le.trans hzb)
      · exact (ae_restrict_iff' measurableSet_Ioc).2
          (ae_of_all _ (fun u hu => hn u ⟨hu.1.le, hu.2⟩))
      · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hi
    apply (Real.le_log_iff_exp_le (hp t ⟨ht.1, le_rfl⟩)).1
    exact le_trans (sub_le_sub_left htotal _) hlog
  have hfaz : ContinuousOn f (Icc a z) :=
    hf.mono (Icc_subset_Icc le_rfl hzb)
  have hclosed : IsClosed (Icc a z ∩ f ⁻¹' Ici K) :=
    hfaz.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsubset : Ico a z ⊆ Icc a z ∩ f ⁻¹' Ici K := by
    intro t ht
    exact ⟨⟨ht.1, ht.2.le⟩, hbound t ht⟩
  have hclosure : closure (Ico a z) ⊆ Icc a z ∩ f ⁻¹' Ici K :=
    hclosed.closure_subset_iff.2 hsubset
  rw [closure_Ico haz.ne] at hclosure
  have hend : K ≤ f z := (hclosure ⟨haz.le, le_rfl⟩).2
  have hzero : f z ≤ 0 := hz.1.2
  linarith

/-- Quantitative form of the finite-rate positivity theorem. -/
theorem lower_bound_of_integrable_relative_decay
    {f rate : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hseed : 0 < f a)
    (hi : IntegrableOn rate (Icc a b))
    (hn : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hr : ∀ t ∈ Ioo a b, 0 < f t → -rate t * f t ≤ deriv f t) :
    f a * Real.exp (-(∫ t in a..b, rate t)) ≤ f b := by
  have hpos : ∀ t ∈ Icc a b, 0 < f t := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    exact positive_of_integrable_relative_decay ht.1 (hf.mono hsub)
      (fun u hu => hd u ⟨hu.1, hu.2.trans_le ht.2⟩) hseed
      (hi.mono_set hsub) (fun u hu => hn u (hsub hu))
      (fun u hu => hr u ⟨hu.1, hu.2.trans_le ht.2⟩)
  have hlog := log_lower_bound_of_positive hab hf hd hpos hi
    (fun t ht => hr t ht (hpos t ⟨ht.1.le, ht.2.le⟩))
  have hexp := (Real.le_log_iff_exp_le (hpos b ⟨hab, le_rfl⟩)).1 hlog
  simpa only [sub_eq_add_neg, Real.exp_add, Real.exp_log hseed] using hexp

end TaylorsProdigy
