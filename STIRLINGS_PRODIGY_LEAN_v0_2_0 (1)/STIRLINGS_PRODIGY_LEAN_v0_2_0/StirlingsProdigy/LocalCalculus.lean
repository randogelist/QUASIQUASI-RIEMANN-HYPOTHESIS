import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Local first-order angular certificates

The increment condition permits an arbitrarily small negative linear error.
It does not assert the global affine bound on the angular derivative used by
the original `STIRLINGS_PRODIGY` premise.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

noncomputable section

namespace StirlingsProdigy

/-- A local right-increment lower bound, restricted to the physical interval. -/
def LocalFirstOrderAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
    ∀ h : ℝ, 0 < h → h < η → x + h ≤ 1 →
      -ε * h ≤ f (x + h) - f x

/-- The local first-order certificate forces a nonnegative derivative. -/
theorem derivative_nonnegative_of_localFirstOrderAt
    {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hx : x < 1) (hlocal : LocalFirstOrderAt f x) :
    0 ≤ deriv f x := by
  by_contra hn
  have hd : deriv f x < 0 := lt_of_not_ge hn
  have hε : 0 < -(deriv f x) / 2 := by linarith
  obtain ⟨η, hη, hbound⟩ := hlocal (-(deriv f x) / 2) hε
  have hlim : Tendsto (fun h : ℝ => (f (x + h) - f x) / h)
      (𝓝[>] 0) (𝓝 (deriv f x)) := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using
      hf.hasDerivAt.tendsto_slope_zero_right
  have hslope : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (f (x + h) - f x) / h < deriv f x / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith : deriv f x < deriv f x / 2))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < η :=
    (gt_mem_nhds hη).filter_mono nhdsWithin_le_nhds
  have hphysical : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 - x :=
    (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - x)).filter_mono
      nhdsWithin_le_nhds
  have hfalse : ∀ᶠ h : ℝ in 𝓝[>] 0, False := by
    filter_upwards [self_mem_nhdsWithin, hslope, hsmall, hphysical]
      with h hh hs hη' hp
    have hhpos : 0 < h := hh
    have hlower := hbound h hhpos hη' (by linarith)
    have hupper : f (x + h) - f x < deriv f x / 2 * h :=
      (div_lt_iff₀ hhpos).mp hs
    nlinarith
  obtain ⟨_h, hcontradiction⟩ := hfalse.exists
  exact hcontradiction

/-- A monotone profile satisfies the local certificate with zero increment loss. -/
theorem localFirstOrderAt_of_monotoneOn
    {f : ℝ → ℝ} {x : ℝ} (hm : MonotoneOn f (Icc (-1 : ℝ) 1))
    (hx : x ∈ Ioo (-1 : ℝ) 1) : LocalFirstOrderAt f x := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro h hh _hsmall hphysical
  have hfx : f x ≤ f (x + h) :=
    hm ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      ⟨by linarith [hx.1], hphysical⟩ (by linarith)
  have hprod : 0 < ε * h := mul_pos hε hh
  nlinarith

end StirlingsProdigy
