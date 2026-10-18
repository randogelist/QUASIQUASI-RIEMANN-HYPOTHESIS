import AngularMaster.ActualProfile

/-!
# STIRLINGS_PRODIGY: the conditional first-order Taylor closure

The sole input is the named proposition `STIRLINGS_PRODIGY` below. It contains
the global one-sided Taylor-remainder bound, the endpoint slope inequality,
and positivity of that slope. None of those clauses is asserted as a theorem.

The functions are the actual Mathlib-backed theta profile. Endpoint derivatives
are taken within [-1, 1], never across the truncated real square root outside
that interval. No Taylor-integral identity or endpoint regularity assertion is
silently added to the input: `taylorRemainder` is an exact algebraic difference.

This is a conditional implication, not an unconditional RH proof. The motivating
analysis already shows that the global slope inequality is false at sufficiently
large radii. Formalizing its implication does not establish the premise.
-/

set_option autoImplicit false

noncomputable section

namespace StirlingsProdigy

/-- Actual angular derivative, using the established one-sided endpoint convention. -/
def U (r x : ℝ) : ℝ :=
  AngularMaster.angularDerivative AngularMaster.actualProfile r x

/-- The value of the angular derivative at the right endpoint. -/
def A (r : ℝ) : ℝ := U r 1

/-- The one-sided angular derivative of U at the right endpoint. -/
def B (r : ℝ) : ℝ :=
  derivWithin (U r) AngularMaster.angularInterval 1

/-- Exact difference from the affine approximation at x = 1. -/
def taylorRemainder (r x : ℝ) : ℝ :=
  U r x - (A r - B r * (1 - x))

/-- The requested sole, explicitly conditional input. -/
def STIRLINGS_PRODIGY : Prop :=
  ∀ r : ℝ, 0 < r →
    (∀ x : ℝ, -1 < x → x < 1 → 0 ≤ taylorRemainder r x) ∧
    2 * B r ≤ A r ∧ 0 < B r

/-- The remainder definition is an exact decomposition, not an approximation. -/
theorem taylor_decomposition (r x : ℝ) :
    U r x = A r - B r * (1 - x) + taylorRemainder r x := by
  unfold taylorRemainder
  ring

/-- The within derivative is the ordinary derivative at an interior angle. -/
theorem U_eq_deriv {r x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    U r x = deriv (AngularMaster.actualProfile r) x := by
  unfold U AngularMaster.angularDerivative AngularMaster.angularInterval
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx₀ hx₁)

/-- A single scalar instance of the Taylor premise gives its quantitative bound. -/
theorem affine_lower_bound
    {u a b x : ℝ} (hrem : 0 ≤ u - (a - b * (1 - x)))
    (hslope : 2 * b ≤ a) :
    b * (1 + x) ≤ u := by
  nlinarith

/-- Quantitative interior lower bound from the sole named input. -/
theorem U_lower_bound_of_STIRLINGS_PRODIGY
    (h : STIRLINGS_PRODIGY) {r x : ℝ}
    (hr : 0 < r) (hx₀ : -1 < x) (hx₁ : x < 1) :
    B r * (1 + x) ≤ U r x := by
  rcases h r hr with ⟨hrem, hslope, _hB⟩
  exact affine_lower_bound (hrem x hx₀ hx₁) hslope

/-- The conditional conclusion is strict at every physical interior point. -/
theorem U_positive_of_STIRLINGS_PRODIGY
    (h : STIRLINGS_PRODIGY) {r x : ℝ}
    (hr : 0 < r) (hx₀ : -1 < x) (hx₁ : x < 1) :
    0 < U r x := by
  have hB : 0 < B r := (h r hr).2.2
  have hfactor : 0 < 1 + x := by linarith
  exact lt_of_lt_of_le (mul_pos hB hfactor)
    (U_lower_bound_of_STIRLINGS_PRODIGY h hr hx₀ hx₁)

/-- Positivity also holds for the ordinary derivative in the interior. -/
theorem actual_deriv_positive_of_STIRLINGS_PRODIGY
    (h : STIRLINGS_PRODIGY) {r x : ℝ}
    (hr : 0 < r) (hx₀ : -1 < x) (hx₁ : x < 1) :
    0 < deriv (AngularMaster.actualProfile r) x := by
  rw [← U_eq_deriv hx₀ hx₁]
  exact U_positive_of_STIRLINGS_PRODIGY h hr hx₀ hx₁

/-- Endpoint continuity and interior differentiation are already proved for theta. -/
theorem actual_profile_monotone_of_STIRLINGS_PRODIGY
    (h : STIRLINGS_PRODIGY) (r : ℝ) (hr : 0 < r) :
    MonotoneOn (AngularMaster.actualProfile r) AngularMaster.angularInterval := by
  apply monotoneOn_of_deriv_nonneg
    (convex_Icc (-1 : ℝ) 1) (AngularMaster.actualProfile_continuousOn r hr)
  · simpa only [AngularMaster.angularInterval, interior_Icc] using
      AngularMaster.actualProfile_interior_differentiable r hr
  · intro x hx
    have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      simpa only [AngularMaster.angularInterval, interior_Icc] using hx
    exact le_of_lt (actual_deriv_positive_of_STIRLINGS_PRODIGY h hr hxi.1 hxi.2)

/-- Native Mathlib RH, with exactly one explicit input and no new analytic bridge. -/
theorem RH_of_STIRLINGS_PRODIGY
    (h : STIRLINGS_PRODIGY) : _root_.RiemannHypothesis :=
  AngularMaster.native_RH_of_actual_angular_monotone
    (actual_profile_monotone_of_STIRLINGS_PRODIGY h)

/-- The requested implication displayed as a closed proposition. -/
theorem STIRLINGS_PRODIGY_IMP_RH :
    STIRLINGS_PRODIGY → _root_.RiemannHypothesis :=
  RH_of_STIRLINGS_PRODIGY

end StirlingsProdigy
