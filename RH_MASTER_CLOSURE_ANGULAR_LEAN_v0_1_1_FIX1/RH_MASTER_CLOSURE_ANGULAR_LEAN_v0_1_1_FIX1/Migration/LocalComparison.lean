import Core.MigrationProfiles

namespace Merger04.Migration

open Filter Merger04.Regularization
open scoped Topology

/-- Local equality is preserved by log-scale differentiation. -/
theorem SCALE_D_EVENTUALLY_EQ
    {f g : ℝ → ℝ} {a : ℝ} (h : f =ᶠ[𝓝 a] g) :
    scaleD f =ᶠ[𝓝 a] scaleD g := by
  filter_upwards [h.deriv] with x hx
  change x * deriv f x = x * deriv g x
  rw [hx]

theorem SCALE_D2_EVENTUALLY_EQ
    {f g : ℝ → ℝ} {a : ℝ} (h : f =ᶠ[𝓝 a] g) :
    scaleD2 f =ᶠ[𝓝 a] scaleD2 g := by
  exact SCALE_D_EVENTUALLY_EQ (SCALE_D_EVENTUALLY_EQ h)

theorem STEP_EVENTUALLY_EQ
    (n : ℕ) {f g : ℝ → ℝ} {a : ℝ} (h : f =ᶠ[𝓝 a] g) :
    step n f =ᶠ[𝓝 a] step n g := by
  filter_upwards [h, SCALE_D2_EVENTUALLY_EQ h] with x hx hd
  simp only [step, hx, hd]

/-- All depths, with equality of germs rather than only function values. -/
theorem TOWER_EVENTUALLY_EQ
    {f g : ℝ → ℝ} {a : ℝ} (h : f =ᶠ[𝓝 a] g) (n : ℕ) :
    tower f n =ᶠ[𝓝 a] tower g n := by
  induction n with
  | zero => exact h
  | succ n ih => exact STEP_EVENTUALLY_EQ n ih

/-- The raw and regularized centered slices agree locally off s=0,1. -/
theorem REAL_SLICE_EVENTUALLY_EQ
    (x : ℝ) (h0 : x + (1 / 2 : ℝ) ≠ 0)
    (h1 : x + (1 / 2 : ℝ) ≠ 1) :
    realSlice rawXi =ᶠ[𝓝 x] realSlice entireXi := by
  have hc : ContinuousAt (fun t : ℝ => t + (1 / 2 : ℝ)) x := by
    fun_prop
  filter_upwards [hc.eventually_ne h0, hc.eventually_ne h1] with t ht0 ht1
  have hc0 : ((t + (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ht0
  have hc1 : ((t + (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 1 := by
    exact_mod_cast ht1
  exact congrArg Complex.re
    (RAW_EQ_ENTIRE_AWAY_FROM_ENDPOINTS
      ((t + (1 / 2 : ℝ) : ℝ) : ℂ) hc0 hc1)

/-- On a>0, the only excluded centered anchor is a=1/4. -/
theorem CENTERED_R_EVENTUALLY_EQ
    (a : ℝ) (ha : 0 < a) (haq : a ≠ (1 / 4 : ℝ)) :
    centeredR rawXi =ᶠ[𝓝 a] centeredR entireXi := by
  have hspos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have h0 : Real.sqrt a + (1 / 2 : ℝ) ≠ 0 := by linarith
  have h1 : Real.sqrt a + (1 / 2 : ℝ) ≠ 1 := by
    intro h
    apply haq
    have hs := Real.sq_sqrt (le_of_lt ha)
    nlinarith
  have he := REAL_SLICE_EVENTUALLY_EQ (Real.sqrt a) h0 h1
  have hsqrt : Tendsto Real.sqrt (𝓝 a) (𝓝 (Real.sqrt a)) :=
    Real.continuous_sqrt.continuousAt
  have he0 := he.comp_tendsto hsqrt
  have he1 := he.deriv.comp_tendsto hsqrt
  filter_upwards [he0, he1] with t ht0 ht1
  have ht0' : realSlice rawXi (Real.sqrt t) =
      realSlice entireXi (Real.sqrt t) := by
    simpa only [Function.comp_apply] using ht0
  have ht1' : deriv (realSlice rawXi) (Real.sqrt t) =
      deriv (realSlice entireXi) (Real.sqrt t) := by
    simpa only [Function.comp_apply] using ht1
  change deriv (realSlice rawXi) (Real.sqrt t) /
      (2 * Real.sqrt t * realSlice rawXi (Real.sqrt t)) =
    deriv (realSlice entireXi) (Real.sqrt t) /
      (2 * Real.sqrt t * realSlice entireXi (Real.sqrt t))
  rw [ht0', ht1']

theorem BASE_MOMENT_EVENTUALLY_EQ
    (a : ℝ) (ha : 0 < a) (haq : a ≠ (1 / 4 : ℝ)) :
    baseMoment rawXi =ᶠ[𝓝 a] baseMoment entireXi := by
  have hr := CENTERED_R_EVENTUALLY_EQ a ha haq
  have hp : (fun t : ℝ => t * centeredR rawXi t) =ᶠ[𝓝 a]
      (fun t : ℝ => t * centeredR entireXi t) := by
    filter_upwards [hr] with t ht
    rw [ht]
  filter_upwards [hp.deriv] with t ht
  change 4 * t * deriv (fun u : ℝ => u * centeredR rawXi u) t =
    4 * t * deriv (fun u : ℝ => u * centeredR entireXi u) t
  rw [ht]

/-- No differentiability of the raw totalized formula is assumed at 1/4. -/
theorem MOMENT_EQ_AWAY_FROM_QUARTER
    (a : ℝ) (ha : 0 < a) (haq : a ≠ (1 / 4 : ℝ)) (n : ℕ) :
    moment rawXi a n = moment entireXi a n := by
  exact (TOWER_EVENTUALLY_EQ (BASE_MOMENT_EVENTUALLY_EQ a ha haq) n).eq_of_nhds

end Merger04.Migration
