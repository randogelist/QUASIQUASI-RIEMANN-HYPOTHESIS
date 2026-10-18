import Derivations.Widder.LocalCalculus

namespace NativeSoloboloNegativity

noncomputable section

/-- Constant part of the normalized Rodrigues/Widder coefficient. -/
def widderWeight (n : ℕ) : ℝ :=
  (-1 : ℝ)^n * 4^(n + 1) / ((2 * n + 1).factorial : ℝ)

/-- The direct unscaled derivative jet; it is not recursively defined. -/
def widderRodriguesJet (R : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  iteratedDeriv (2 * n + 1) (fun t : ℝ => t^(n + 1) * R t)

/-- Direct high-derivative expression with its scalar weight factored out. -/
def widderDirectScaled (R : ℝ → ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  a^(n + 1) * (widderWeight n * widderRodriguesJet R n a)

/-- Base moment belonging to an arbitrary R-channel. -/
def widderBaseOf (R : ℝ → ℝ) (a : ℝ) : ℝ :=
  4 * a * deriv (fun t : ℝ => t * R t) a

/-- The scalar recurrence is purely factorial arithmetic. -/
theorem WIDDER_WEIGHT_SUCC (n : ℕ) :
    widderWeight (n + 1) =
      -(2 / (((n + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) + 1))) * widderWeight n := by
  have hfac : ((2 * (n + 1) + 1).factorial : ℝ) =
      (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 2) * ((2 * n + 1).factorial : ℝ) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hf0 : ((2 * n + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n + 1)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  have hn3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have hstep : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  unfold widderWeight
  rw [hfac]
  simp only [pow_succ]
  push_cast
  field_simp [hf0, hn1, hn2, hn3, hstep] <;> ring

/-- This is exactly the original direct formula, not a replacement definition. -/
theorem WIDDER_DIRECT_SCALED_EQ_FORMULA (R : ℝ → ℝ) (n : ℕ) (a : ℝ) :
    widderDirectScaled R n a =
      (-1 : ℝ)^n * (4 * a)^(n + 1) / ((2 * n + 1).factorial : ℝ) *
        iteratedDeriv (2 * n + 1) (fun t : ℝ => t^(n + 1) * R t) a := by
  unfold widderDirectScaled widderWeight widderRodriguesJet
  rw [mul_pow]
  ring

@[simp] theorem WIDDER_DIRECT_SCALED_ZERO (R : ℝ → ℝ) (a : ℝ) :
    widderDirectScaled R 0 a = widderBaseOf R a := by
  simp [widderDirectScaled, widderWeight, widderRodriguesJet, widderBaseOf,
    iteratedDeriv_one]
  <;> ring

/-- All-depth recurrence for the direct Rodrigues formula.  The proof uses
    the two-term coordinate Leibniz rule and Euler conjugation. -/
theorem WIDDER_DIRECT_SCALED_STEP
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) {a : ℝ} (ha : a ∈ U) :
    widderDirectScaled R (n + 1) a =
      widderStep n (widderDirectScaled R n) a := by
  let h : ℝ → ℝ := fun t : ℝ => t^(n + 1) * R t
  have hh : AnalyticOnNhd ℝ h U := by
    intro b hb
    exact (analyticAt_id.pow (n + 1)).mul (hR b hb)
  have hk : AnalyticOnNhd ℝ
      (fun t : ℝ => widderWeight n * iteratedDeriv (2 * n + 1) h t) U := by
    intro b hb
    exact analyticAt_const.mul (ANALYTIC_ITERATED_DERIV_ON hh (2 * n + 1) b hb)
  have hpower : (fun t : ℝ => t^((n + 1) + 1) * R t) =
      (fun t : ℝ => t * h t) := by
    funext t
    dsimp [h]
    rw [pow_succ]
    ring
  have hindex1 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by omega
  have hindex2 : 2 * n + 2 = (2 * n + 1) + 1 := by omega
  have hjet : widderRodriguesJet R (n + 1) a =
      a * iteratedDeriv ((2 * n + 1) + 1 + 1) h a +
        (2 * ((n + 1 : ℕ) : ℝ) + 1) * iteratedDeriv ((2 * n + 1) + 1) h a := by
    unfold widderRodriguesJet
    rw [hpower, hindex1, ITERATED_DERIV_COORDINATE_MUL hU hh (2 * n + 2) ha]
    simp only [hindex2]
    push_cast
    ring
  calc
    widderDirectScaled R (n + 1) a =
        a^(n + 2) * (widderWeight (n + 1) *
          (a * iteratedDeriv ((2 * n + 1) + 1 + 1) h a +
            (2 * ((n + 1 : ℕ) : ℝ) + 1) * iteratedDeriv ((2 * n + 1) + 1) h a)) := by
      unfold widderDirectScaled
      rw [hjet]
    _ = widderStep n (widderDirectScaled R n) a := by
      change _ = widderStep n (fun t : ℝ => t^(n + 1) *
        (widderWeight n * iteratedDeriv (2 * n + 1) h t)) a
      rw [WIDDER_STEP_POWER_MUL hU hk n ha,
        DERIV_SCALED_JET, SECOND_DERIV_SCALED_JET, WIDDER_WEIGHT_SUCC]
      ring

/-- Exact direct-formula/recursive-tower equality on every open analytic domain. -/
theorem WIDDER_DIRECT_EQUALS_TOWER_ON_OPEN
    {U : Set ℝ} (hU : IsOpen U) {R : ℝ → ℝ}
    (hR : AnalyticOnNhd ℝ R U) (n : ℕ) :
    Set.EqOn (widderDirectScaled R n) (widderTower (widderBaseOf R) n) U := by
  induction n with
  | zero =>
      intro a ha
      exact WIDDER_DIRECT_SCALED_ZERO R a
  | succ n ih =>
      intro a ha
      calc
        widderDirectScaled R (n + 1) a = widderStep n (widderDirectScaled R n) a :=
          WIDDER_DIRECT_SCALED_STEP hU hR n ha
        _ = widderStep n (widderTower (widderBaseOf R) n) a :=
          WIDDER_STEP_CONGR_ON_OPEN hU ih n ha
        _ = widderTower (widderBaseOf R) (n + 1) a := rfl

end
end NativeSoloboloNegativity
