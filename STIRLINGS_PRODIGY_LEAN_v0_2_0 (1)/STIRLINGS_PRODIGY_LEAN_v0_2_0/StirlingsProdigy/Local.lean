import StirlingsProdigy.Closure
import StirlingsProdigy.LocalCalculus

/-!
# A distinct local first-order premise

This does not redefine the original global affine `STIRLINGS_PRODIGY`.
At each interior point, all sufficiently small forward increments of P have
first-order lower error at most epsilon*h, for every epsilon > 0.
-/

set_option autoImplicit false

noncomputable section

namespace StirlingsProdigy

/-- The local first-order criterion, named separately from the original premise. -/
def STIRLINGS_PRODIGY_LOCAL : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x : ℝ, -1 < x → x < 1 →
    LocalFirstOrderAt (AngularMaster.actualProfile r) x

/-- Its pointwise content is nonnegativity of the actual ordinary derivative. -/
theorem actual_deriv_nonnegative_of_STIRLINGS_PRODIGY_LOCAL
    (h : STIRLINGS_PRODIGY_LOCAL) {r x : ℝ}
    (hr : 0 < r) (hx₀ : -1 < x) (hx₁ : x < 1) :
    0 ≤ deriv (AngularMaster.actualProfile r) x := by
  have hwithin :=
    AngularMaster.actualProfile_interior_differentiable r hr x ⟨hx₀, hx₁⟩
  have hf : DifferentiableAt ℝ (AngularMaster.actualProfile r) x :=
    hwithin.differentiableAt (isOpen_Ioo.mem_nhds ⟨hx₀, hx₁⟩)
  exact derivative_nonnegative_of_localFirstOrderAt hf hx₁ (h r hr x hx₀ hx₁)

/-- Local first-order lower bounds give angular monotonicity by the mean value theorem. -/
theorem actual_profile_monotone_of_STIRLINGS_PRODIGY_LOCAL
    (h : STIRLINGS_PRODIGY_LOCAL) (r : ℝ) (hr : 0 < r) :
    MonotoneOn (AngularMaster.actualProfile r) AngularMaster.angularInterval := by
  apply monotoneOn_of_deriv_nonneg
    (convex_Icc (-1 : ℝ) 1) (AngularMaster.actualProfile_continuousOn r hr)
  · simpa only [AngularMaster.angularInterval, interior_Icc] using
      AngularMaster.actualProfile_interior_differentiable r hr
  · intro x hx
    have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      simpa only [AngularMaster.angularInterval, interior_Icc] using hx
    exact actual_deriv_nonnegative_of_STIRLINGS_PRODIGY_LOCAL h hr hxi.1 hxi.2

/-- The local criterion implies native RH with no extra hypothesis. -/
theorem RH_of_STIRLINGS_PRODIGY_LOCAL
    (h : STIRLINGS_PRODIGY_LOCAL) : _root_.RiemannHypothesis :=
  AngularMaster.native_RH_of_actual_angular_monotone
    (actual_profile_monotone_of_STIRLINGS_PRODIGY_LOCAL h)

/-- The original, stronger global premise implies the new local criterion. -/
theorem STIRLINGS_PRODIGY_LOCAL_of_STIRLINGS_PRODIGY
    (h : STIRLINGS_PRODIGY) : STIRLINGS_PRODIGY_LOCAL := by
  intro r hr x hx₀ hx₁
  exact localFirstOrderAt_of_monotoneOn
    (actual_profile_monotone_of_STIRLINGS_PRODIGY h r hr) ⟨hx₀, hx₁⟩

end StirlingsProdigy
