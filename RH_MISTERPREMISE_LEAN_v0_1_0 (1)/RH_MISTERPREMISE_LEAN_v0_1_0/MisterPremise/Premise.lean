import MisterPremise.Cutoff
import AngularRegularity.Actual

/-!
# The frozen MISTERPREMISE

The only research statement is existence, for each residual radius, of a finite
constant uniform over the remaining angular interval. The inequality is needed
only where the original ordinary angular derivative is strictly positive.
No lower bound on its second derivative is included in this minimal premise.
-/

set_option autoImplicit false
noncomputable section

namespace MisterPremise

/-- The literal squared-modulus profile from the retained angular package. -/
abbrev P : ℝ → ℝ → ℝ := AngularRegularity.actualProfile

/-- The original unnormalized angular slope `P_x`. -/
abbrev A : ℝ → ℝ → ℝ := AngularRegularity.actualAngularSlope

/-- The exact finite-bound input named by the user. The constant is allowed
to depend arbitrarily on the radius; no uniform bound in the radius is assumed. -/
def MISTERPREMISE : Prop :=
  ∀ r : ℝ, (255 / 7 : ℝ) < r →
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Ioc (-1 : ℝ) (-kappa r),
      0 < A r x → (1 + x) * deriv (A r) x ≤ M * A r x

theorem MISTERPREMISE_iff_expanded : MISTERPREMISE ↔
    ∀ r : ℝ, (255 / 7 : ℝ) < r →
      ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
        -1 < x → x ≤ -kappa r → 0 < A r x →
        (1 + x) * deriv (A r) x ≤ M * A r x := by
  constructor
  · intro h r hr
    obtain ⟨M, hM, hbound⟩ := h r hr
    exact ⟨M, hM, fun x hx hxb hp => hbound x ⟨hx, hxb⟩ hp⟩
  · intro h r hr
    obtain ⟨M, hM, hbound⟩ := h r hr
    exact ⟨M, hM, fun x hx hp => hbound x hx.1 hx.2 hp⟩

end MisterPremise
