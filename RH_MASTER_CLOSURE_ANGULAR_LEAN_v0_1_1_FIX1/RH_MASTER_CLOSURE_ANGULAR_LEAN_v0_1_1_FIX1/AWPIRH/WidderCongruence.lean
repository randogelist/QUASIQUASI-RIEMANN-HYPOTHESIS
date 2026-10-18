import AWPIRH.LocalRowTransport

/-!
Generic germ-congruence for the exact log-anchor Widder recurrence used by
NativeInput.  No analyticity, xi identity, positivity, or RH statement is assumed.
The only input is equality on a neighbourhood, which Mathlib propagates through
ordinary derivatives.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter
namespace AWPIRH

/-- The same recurrence as `nativeWidder`, abstracted over its base function. -/
def logWidderTower (base : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => base
  | n + 1 => fun y =>
      2 / (((n : ℝ) + 1) * (2 * (n : ℝ) + 3)) *
        (((n : ℝ) + 1) ^ 2 * logWidderTower base n y -
          deriv (deriv (logWidderTower base n)) y)

@[simp] theorem logWidderTower_zero (base : ℝ → ℝ) :
    logWidderTower base 0 = base := rfl

@[simp] theorem logWidderTower_succ (base : ℝ → ℝ) (n : ℕ) (y : ℝ) :
    logWidderTower base (n + 1) y =
      2 / (((n : ℝ) + 1) * (2 * (n : ℝ) + 3)) *
        (((n : ℝ) + 1) ^ 2 * logWidderTower base n y -
          deriv (deriv (logWidderTower base n)) y) := rfl

/-- Equality of base germs propagates through the whole Widder tower. -/
theorem logWidderTower_eventuallyEq {f g : ℝ → ℝ} {x : ℝ}
    (hfg : f =ᶠ[𝓝 x] g) (n : ℕ) :
    logWidderTower f n =ᶠ[𝓝 x] logWidderTower g n := by
  induction n with
  | zero =>
      simpa only [logWidderTower_zero] using hfg
  | succ n ih =>
      have hd1 : deriv (logWidderTower f n) =ᶠ[𝓝 x]
          deriv (logWidderTower g n) := ih.deriv
      have hd2 : deriv (deriv (logWidderTower f n)) =ᶠ[𝓝 x]
          deriv (deriv (logWidderTower g n)) := hd1.deriv
      filter_upwards [ih, hd2] with y hy hdy
      simp only [logWidderTower_succ]
      rw [hy, hdy]

/-- The native recurrence is literally the generic tower at `nativeBase`. -/
theorem nativeWidder_eq_logWidderTower (n : ℕ) :
    nativeWidder n = logWidderTower nativeBase n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext y
      rw [nativeWidder_succ, logWidderTower_succ, ih]

end AWPIRH
