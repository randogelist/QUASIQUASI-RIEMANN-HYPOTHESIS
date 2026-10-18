import Core.EntireXiWidder
import Mathlib

namespace NativeSoloboloNegativity

open Filter
open scoped Topology

noncomputable section

/-- Euler differentiation in the positive-anchor coordinate. -/
def eulerD (f : ℝ → ℝ) (a : ℝ) : ℝ := a * deriv f a

/-- Local equalities can be differentiated without asserting a global extension. -/
theorem LOCAL_DERIV_CONGR
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g U) {a : ℝ} (ha : a ∈ U) :
    deriv f a = deriv g a := by
  have hlocal : f =ᶠ[𝓝 a] g := by
    filter_upwards [hU.mem_nhds ha] with b hb
    exact hfg hb
  exact hlocal.deriv_eq

/-- Analyticity supplies every actual iterated derivative on the same open set. -/
theorem ANALYTIC_ITERATED_DERIV_ON
    {U : Set ℝ} {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f U) (n : ℕ) :
    AnalyticOnNhd ℝ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

/-- Multiplication by the coordinate has only two nonzero Leibniz terms. -/
theorem ITERATED_DERIV_COORDINATE_MUL
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (n : ℕ) {a : ℝ} (ha : a ∈ U) :
    iteratedDeriv (n + 1) (fun t : ℝ => t * f t) a =
      a * iteratedDeriv (n + 1) f a + ((n + 1 : ℕ) : ℝ) * iteratedDeriv n f a := by
  induction n generalizing a with
  | zero =>
      have hd : deriv (fun t : ℝ => t * f t) a =
          f a + a * deriv f a := by
        simpa only [id_eq, one_mul] using
          ((hasDerivAt_id a).fun_mul (hf a ha).differentiableAt.hasDerivAt).deriv
      -- Normalize the natural-number index before applying derivative lemmas.
      change iteratedDeriv 1 (fun t : ℝ => t * f t) a =
        a * iteratedDeriv 1 f a + ((1 : ℕ) : ℝ) * iteratedDeriv 0 f a
      simp only [iteratedDeriv_one, iteratedDeriv_zero, Nat.cast_one, one_mul]
      exact hd.trans (add_comm (f a) (a * deriv f a))
  | succ n ih =>
      have hEq : Set.EqOn
          (iteratedDeriv (n + 1) (fun t : ℝ => t * f t))
          (fun t : ℝ => t * iteratedDeriv (n + 1) f t +
            ((n + 1 : ℕ) : ℝ) * iteratedDeriv n f t) U := by
        intro b hb
        exact ih hb
      have hdEq := LOCAL_DERIV_CONGR hU hEq ha
      have hdn := (ANALYTIC_ITERATED_DERIV_ON hf n a ha).differentiableAt.hasDerivAt
      have hdn1 := (ANALYTIC_ITERATED_DERIV_ON hf (n + 1) a ha).differentiableAt.hasDerivAt
      -- Eta-expanded rules keep the function under `deriv` identical to the goal.
      have hcalc :
          deriv (fun t : ℝ => t * iteratedDeriv (n + 1) f t +
            ((n + 1 : ℕ) : ℝ) * iteratedDeriv n f t) a =
          iteratedDeriv (n + 1) f a +
            a * deriv (iteratedDeriv (n + 1) f) a +
            ((n + 1 : ℕ) : ℝ) * deriv (iteratedDeriv n f) a := by
        simpa only [id_eq, one_mul] using
          (((hasDerivAt_id a).fun_mul hdn1).fun_add
            (hdn.const_mul ((n + 1 : ℕ) : ℝ))).deriv
      calc
        iteratedDeriv (n + 1 + 1) (fun t : ℝ => t * f t) a =
            deriv (iteratedDeriv (n + 1) (fun t : ℝ => t * f t)) a := by
          rw [iteratedDeriv_succ]
        _ = deriv (fun t : ℝ => t * iteratedDeriv (n + 1) f t +
            ((n + 1 : ℕ) : ℝ) * iteratedDeriv n f t) a := hdEq
        _ = a * iteratedDeriv (n + 1 + 1) f a +
            ((n + 1 + 1 : ℕ) : ℝ) * iteratedDeriv (n + 1) f a := by
          rw [hcalc]
          simp only [← iteratedDeriv_succ]
          push_cast
          ring

/-- First derivative of a constant times a literal derivative jet. -/
theorem DERIV_SCALED_JET (c : ℝ) (f : ℝ → ℝ) (n : ℕ) (a : ℝ) :
    deriv (fun t : ℝ => c * iteratedDeriv n f t) a =
      c * iteratedDeriv (n + 1) f a := by
  rw [deriv_const_mul_field, iteratedDeriv_succ]

/-- Second derivative of a scaled jet; no change of the underlying function. -/
theorem SECOND_DERIV_SCALED_JET (c : ℝ) (f : ℝ → ℝ) (n : ℕ) (a : ℝ) :
    deriv (deriv (fun t : ℝ => c * iteratedDeriv n f t)) a =
      c * iteratedDeriv (n + 1 + 1) f a := by
  have hfun : deriv (fun t : ℝ => c * iteratedDeriv n f t) =
      (fun t : ℝ => c * iteratedDeriv (n + 1) f t) := by
    funext t
    exact DERIV_SCALED_JET c f n t
  rw [hfun]
  exact DERIV_SCALED_JET c f (n + 1) a

/-- Euler differentiation preserves local analyticity. -/
theorem EULER_D_ANALYTIC_AT {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) : AnalyticAt ℝ (eulerD f) a := by
  exact analyticAt_id.mul hf.deriv

theorem EULER_D_ADD {f g : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) (hg : AnalyticAt ℝ g a) :
    eulerD (fun t => f t + g t) a = eulerD f a + eulerD g a := by
  have hd : deriv (fun t : ℝ => f t + g t) a = deriv f a + deriv g a :=
    (hf.differentiableAt.hasDerivAt.fun_add hg.differentiableAt.hasDerivAt).deriv
  unfold eulerD
  rw [hd]
  ring

theorem EULER_D_CONST_MUL (c : ℝ) {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) :
    eulerD (fun t => c * f t) a = c * eulerD f a := by
  have hd : deriv (fun t : ℝ => c * f t) a = c * deriv f a :=
    (hf.differentiableAt.hasDerivAt.const_mul c).deriv
  unfold eulerD
  rw [hd]
  ring

/-- The Euler product rule avoids negative powers and is valid even at a=0. -/
theorem EULER_D_POWER_MUL (m : ℕ) {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) :
    eulerD (fun t : ℝ => t ^ m * f t) a =
      a ^ m * ((m : ℝ) * f a + eulerD f a) := by
  cases m with
  | zero => simp
  | succ m =>
      have hp : HasDerivAt (fun t : ℝ => t ^ (m + 1))
          (((m + 1 : ℕ) : ℝ) * a ^ m) a := by
        simpa only [Nat.succ_sub_one] using
          (hasDerivAt_pow (𝕜 := ℝ) (m + 1) a)
      have hd : deriv (fun t : ℝ => t ^ (m + 1) * f t) a =
          (((m + 1 : ℕ) : ℝ) * a ^ m) * f a +
            a ^ (m + 1) * deriv f a :=
        (hp.fun_mul hf.differentiableAt.hasDerivAt).deriv
      unfold eulerD
      rw [hd]
      simp only [pow_succ]
      ring

/-- D^2 f = a f' + a^2 f'', with derivatives justified locally. -/
theorem EULER_D_SQUARE {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) :
    eulerD (eulerD f) a = a * deriv f a + a ^ 2 * deriv (deriv f) a := by
  have hd : deriv (fun t : ℝ => t * deriv f t) a =
      deriv f a + a * deriv (deriv f) a := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id a).fun_mul hf.deriv.differentiableAt.hasDerivAt).deriv
  unfold eulerD
  rw [hd]
  ring

/-- Exact conjugation of D^2 by a power of the anchor. -/
theorem EULER_D_SQUARE_POWER_MUL
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (m : ℕ) {a : ℝ} (ha : a ∈ U) :
    eulerD (eulerD (fun t : ℝ => t ^ m * f t)) a =
      a ^ m * ((m : ℝ)^2 * f a + 2 * (m : ℝ) * eulerD f a +
        eulerD (eulerD f) a) := by
  have heq : Set.EqOn
      (eulerD (fun t : ℝ => t ^ m * f t))
      (fun t : ℝ => t ^ m * ((m : ℝ) * f t + eulerD f t)) U := by
    intro b hb
    exact EULER_D_POWER_MUL m (hf b hb)
  have hdeq := LOCAL_DERIV_CONGR hU heq ha
  have hfa := hf a ha
  have hEa := EULER_D_ANALYTIC_AT (f := f) hfa
  have hscaled : AnalyticAt ℝ (fun t : ℝ => (m : ℝ) * f t) a :=
    analyticAt_const.mul hfa
  have hnew : AnalyticAt ℝ (fun t : ℝ => (m : ℝ) * f t + eulerD f t) a :=
    hscaled.add hEa
  -- Fix the function arguments before creating either Euler equality.
  have hadd :
      eulerD (fun t : ℝ => (m : ℝ) * f t + eulerD f t) a =
        eulerD (fun t : ℝ => (m : ℝ) * f t) a + eulerD (eulerD f) a :=
    EULER_D_ADD (f := fun t : ℝ => (m : ℝ) * f t)
      (g := eulerD f) (a := a) hscaled hEa
  have hscale : eulerD (fun t : ℝ => (m : ℝ) * f t) a =
      (m : ℝ) * eulerD f a :=
    EULER_D_CONST_MUL (m : ℝ) (f := f) (a := a) hfa
  calc
    eulerD (eulerD (fun t : ℝ => t ^ m * f t)) a =
        eulerD (fun t : ℝ => t ^ m * ((m : ℝ) * f t + eulerD f t)) a :=
      congrArg (fun z : ℝ => a * z) hdeq
    _ = a ^ m * ((m : ℝ) * ((m : ℝ) * f a + eulerD f a) +
        eulerD (fun t : ℝ => (m : ℝ) * f t + eulerD f t) a) :=
      EULER_D_POWER_MUL m hnew
    _ = a ^ m * ((m : ℝ)^2 * f a + 2 * (m : ℝ) * eulerD f a +
        eulerD (eulerD f) a) := by
      rw [hadd, hscale]
      ring

/-- Conjugating the actual Widder step, with no sign or spectral assumption. -/
theorem WIDDER_STEP_POWER_MUL
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (n : ℕ) {a : ℝ} (ha : a ∈ U) :
    widderStep n (fun t : ℝ => t ^ (n + 1) * f t) a =
      -(2 / (((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) + 1))) *
        a ^ (n + 2) *
        ((2 * ((n + 1 : ℕ) : ℝ) + 1) * deriv f a + a * deriv (deriv f) a) := by
  have hfa := hf a ha
  have hprod : AnalyticAt ℝ (fun t : ℝ => t ^ (n + 1) * f t) a :=
    (analyticAt_id.pow (n + 1)).mul hfa
  calc
    widderStep n (fun t : ℝ => t ^ (n + 1) * f t) a =
        2 / (((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) + 1)) *
          (((n + 1 : ℕ) : ℝ)^2 * (a ^ (n + 1) * f a) -
            eulerD (eulerD (fun t : ℝ => t ^ (n + 1) * f t)) a) := by
      rw [EULER_D_SQUARE (f := fun t : ℝ => t ^ (n + 1) * f t) hprod]
      unfold widderStep
      ring
    _ = _ := by
      rw [EULER_D_SQUARE_POWER_MUL hU (f := f) hf (n + 1) ha,
        EULER_D_SQUARE (f := f) hfa]
      unfold eulerD
      simp only [pow_succ]
      ring

/-- Widder differentiation respects equality on an open set. -/
theorem WIDDER_STEP_CONGR_ON_OPEN
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g U) (n : ℕ) :
    Set.EqOn (widderStep n f) (widderStep n g) U := by
  have hd : Set.EqOn (deriv f) (deriv g) U := fun _ ha => LOCAL_DERIV_CONGR hU hfg ha
  have hdd : Set.EqOn (deriv (deriv f)) (deriv (deriv g)) U :=
    fun _ ha => LOCAL_DERIV_CONGR hU hd ha
  intro a ha
  unfold widderStep
  rw [hfg ha, hd ha, hdd ha]

end
end NativeSoloboloNegativity
