import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
A general analytic zero-exclusion theorem behind angular monotonicity.
No assertion about the location of zeros is assumed: the proof uses the identity
principle for analytic functions and the real part of the circle parameter.
-/

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

namespace AngularMaster

/-- Upper semicircle, parametrized by the normalized real coordinate. -/
def circlePoint (r x : ℝ) : ℂ :=
  (r : ℂ) * ((x : ℂ) + Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ))

/-- Squared modulus on a circle, in angular coordinate `x = cos θ`. -/
def angularNormSq (f : ℂ → ℂ) (r x : ℝ) : ℝ :=
  Complex.normSq (f (circlePoint r x))

@[simp] theorem circlePoint_re (r x : ℝ) : (circlePoint r x).re = r * x := by
  simp [circlePoint, Complex.mul_re]

@[simp] theorem circlePoint_im (r x : ℝ) :
    (circlePoint r x).im = r * Real.sqrt (1 - x ^ 2) := by
  simp [circlePoint, Complex.mul_im]

theorem continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
  unfold circlePoint
  continuity

theorem injective_circlePoint {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (circlePoint r) := by
  intro x y h
  have h' := congrArg Complex.re h
  simp only [circlePoint_re] at h'
  exact mul_left_cancel₀ hr h'

/-- A nonconstant continuous injective arc of zeros forces an entire function
    to vanish identically. This is the only analytic uniqueness input. -/
theorem entire_eq_zero_of_zero_arc {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hinj : Function.Injective γ) {a b : ℝ} (hab : a < b)
    (hz : ∀ x ∈ Icc a b, f (γ x) = 0) : f = 0 := by
  have ht : Tendsto γ (𝓝[>] a) (𝓝[≠] γ a) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    change γ x ≠ γ a
    exact fun h => (ne_of_gt hx) (hinj h)
  have he : ∀ᶠ x in 𝓝[>] a, f (γ x) = 0 := by
    have hb : ∀ᶠ x in 𝓝[>] a, x < b :=
      nhdsWithin_le_nhds (eventually_lt_nhds hab)
    filter_upwards [self_mem_nhdsWithin, hb] with x hx hxb
    exact hz x ⟨le_of_lt hx, le_of_lt hxb⟩
  exact hf.eq_of_frequently_eq analyticOnNhd_const (ht.frequently he.frequently)

/-- Every point of the closed upper half-plane except zero has this circle
    representation. -/
theorem circlePoint_norm_re_div {z : ℂ} (hz : z ≠ 0) (hi : 0 ≤ z.im) :
    circlePoint ‖z‖ (z.re / ‖z‖) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn0 : ‖z‖ ≠ 0 := ne_of_gt hn
  have hsq : 1 - (z.re / ‖z‖) ^ 2 = (z.im / ‖z‖) ^ 2 := by
    have h := Complex.sq_norm_sub_sq_re z
    field_simp [hn0]
    nlinarith
  have hsqrt : Real.sqrt (1 - (z.re / ‖z‖) ^ 2) = z.im / ‖z‖ := by
    rw [hsq, Real.sqrt_sq (div_nonneg hi hn.le)]
  apply Complex.ext
  · simp only [circlePoint_re]
    field_simp [hn0]
  · simp only [circlePoint_im, hsqrt]
    field_simp [hn0]

end AngularMaster
