import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace TaylorsProdigy

/-- A positive continuously differentiable extension at the starting endpoint
supplies an integrable relative-decay rate. The original signal is allowed an
arbitrary value at the endpoint itself. -/
theorem relative_decay_rate_of_positive_extension
    {f g : ℝ → ℝ} {B : ℝ}
    (hg : ContinuousOn g (Ico (0 : ℝ) B))
    (hdg : ContinuousOn (deriv g) (Ico (0 : ℝ) B))
    (hpos : ∀ t ∈ Ico (0 : ℝ) B, 0 < g t)
    (heq : ∀ t ∈ Ioo (0 : ℝ) B, f t = g t) :
    ∃ rate : ℝ → ℝ,
      (∀ b : ℝ, 0 < b → b < B → IntervalIntegrable rate volume 0 b) ∧
      (∀ t ∈ Ioo (0 : ℝ) B, 0 ≤ rate t) ∧
      ∀ t ∈ Ioo (0 : ℝ) B,
        0 < f t → -rate t * f t ≤ deriv f t := by
  let rate : ℝ → ℝ := fun t => max 0 (-deriv g t / g t)
  have hrate : ContinuousOn rate (Ico (0 : ℝ) B) :=
    continuousOn_const.sup (hdg.neg.div hg (fun t ht => ne_of_gt (hpos t ht)))
  refine ⟨rate, ?_, ?_, ?_⟩
  · intro b hb hbB
    have hsub : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) B := by
      intro t ht
      exact ⟨ht.1, ht.2.trans_lt hbB⟩
    exact (hrate.mono hsub).intervalIntegrable_of_Icc hb.le
  · intro t ht
    exact le_max_left _ _
  · intro t ht _
    have hloc : f =ᶠ[𝓝 t] g := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact heq u hu
    have hd : deriv f t = deriv g t := hloc.deriv_eq
    rw [heq t ht, hd]
    have hp : 0 < g t := hpos t ⟨ht.1.le, ht.2⟩
    have hbound : -deriv g t / g t ≤ rate t := le_max_right _ _
    have hmul : -deriv g t ≤ rate t * g t := (div_le_iff₀ hp).1 hbound
    linarith

end TaylorsProdigy
