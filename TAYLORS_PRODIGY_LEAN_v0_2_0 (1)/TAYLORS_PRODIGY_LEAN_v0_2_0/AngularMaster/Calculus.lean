import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Angular Master: actual within derivatives and positive rescaling

All angular derivatives are taken **within** `[-1,1]`.  This convention matters at
both endpoints: the literal real-square-root formula for an angular profile need
not have the intended derivative when extended outside that interval.

The theorems in this file are unconditional generic calculus facts.  Application
to a particular completed L-function still requires its stated regularity facts.
-/

noncomputable section

namespace AngularMaster

/-- The angular coordinate is `x = cos θ`. -/
def angularInterval : Set ℝ := Set.Icc (-1) 1

@[simp] theorem neg_one_mem_angularInterval : (-1 : ℝ) ∈ angularInterval := by
  norm_num [angularInterval]

@[simp] theorem one_mem_angularInterval : (1 : ℝ) ∈ angularInterval := by
  norm_num [angularInterval]

/-- The derivative of the profile, including the one-sided endpoint values. -/
def angularDerivative (P : ℝ → ℝ → ℝ) (r x : ℝ) : ℝ :=
  derivWithin (P r) angularInterval x

/-- The bounded logarithmic Master object. -/
def masterLog (ε : ℝ) (S : ℝ → ℝ) (P : ℝ → ℝ → ℝ) (r x : ℝ) : ℝ :=
  Real.log (1 + ε * P r x / (S r) ^ 2)

/-- The exponential times the angular derivative of the logarithmic Master. -/
def masterFlux (ε : ℝ) (S : ℝ → ℝ) (P : ℝ → ℝ → ℝ) (r x : ℝ) : ℝ :=
  Real.exp (masterLog ε S P r x) *
    derivWithin (masterLog ε S P r) angularInterval x

/-- Regularity on every positive-radius angular slice. -/
def ProfileRegular (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → DifferentiableOn ℝ (P r) angularInterval

/-- Nonnegativity of an angular squared-modulus profile. -/
def ProfileNonnegative (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ x ∈ angularInterval, 0 ≤ P r x

/-- A normalizing quantity is strictly positive at positive radii. -/
def NormalizerPositive (S : ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → 0 < S r

/-- Angular derivative nonnegativity. -/
def DerivativeNonnegative (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ x ∈ angularInterval, 0 ≤ angularDerivative P r x

/-- Sub_1: the angular derivative attains its minimum at the left endpoint. -/
def AngularMinimum (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ x ∈ angularInterval,
    angularDerivative P r (-1) ≤ angularDerivative P r x

/-- Sub_2: the left endpoint angular derivative is nonnegative. -/
def BoundaryNonnegative (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → 0 ≤ angularDerivative P r (-1)

/-- Both subconditions on the original squared-modulus profile. -/
def ProfileMaster (P : ℝ → ℝ → ℝ) : Prop :=
  AngularMinimum P ∧ BoundaryNonnegative P

/-- Both subconditions written using the single logarithmic Master object. -/
def LogMaster (ε : ℝ) (S : ℝ → ℝ) (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ x ∈ angularInterval,
    masterFlux ε S P r (-1) ≤ masterFlux ε S P r x ∧
    0 ≤ masterFlux ε S P r (-1)

/-- Exact cancellation of the log and exp, proved for actual within derivatives. -/
theorem masterFlux_eq_scaledDerivative
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ} {r x : ℝ}
    (hε : 0 < ε) (hS : 0 < S r) (hP : 0 ≤ P r x)
    (hx : x ∈ angularInterval)
    (hreg : DifferentiableWithinAt ℝ (P r) angularInterval x) :
    masterFlux ε S P r x = ε / (S r) ^ 2 * angularDerivative P r x := by
  have harg : 0 < 1 + ε * P r x / (S r) ^ 2 := by positivity
  have hu : UniqueDiffWithinAt ℝ angularInterval x :=
    uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1) x hx
  have hd : HasDerivWithinAt
      (fun y => 1 + ε * P r y / (S r) ^ 2)
      (ε * angularDerivative P r x / (S r) ^ 2) angularInterval x := by
    simpa only [angularDerivative] using
      ((hreg.hasDerivWithinAt.const_mul ε).div_const ((S r) ^ 2)).const_add 1
  have hlog := (hd.log (ne_of_gt harg)).derivWithin hu
  unfold masterFlux masterLog
  rw [Real.exp_log harg, hlog]
  rw [mul_div_cancel₀ _ (ne_of_gt harg)]
  ring

/-- The same exact identity for Lean's total derivative.  If the profile is
    not differentiable at the point, its logarithmic transform is not either,
    and both total within derivatives are zero.  This theorem does not claim
    differentiability at an endpoint. -/
theorem masterFlux_eq_scaledDerivative_total
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ} {r x : ℝ}
    (hε : 0 < ε) (hS : 0 < S r) (hPall : ∀ y, 0 ≤ P r y)
    (hx : x ∈ angularInterval) :
    masterFlux ε S P r x = ε / (S r) ^ 2 * angularDerivative P r x := by
  by_cases hreg : DifferentiableWithinAt ℝ (P r) angularInterval x
  · exact masterFlux_eq_scaledDerivative hε hS (hPall x) hx hreg
  · have hnotlog : ¬DifferentiableWithinAt ℝ (masterLog ε S P r) angularInterval x := by
      intro hlog
      apply hreg
      have hinv :
          (fun y => (Real.exp (masterLog ε S P r y) - 1) * (S r) ^ 2 / ε) = P r := by
        funext y
        have harg : 0 < 1 + ε * P r y / (S r) ^ 2 := by
          have hy := hPall y
          positivity
        rw [masterLog, Real.exp_log harg]
        field_simp [ne_of_gt hε, ne_of_gt hS]
        ring
      have hd := ((hlog.exp.sub_const 1).mul_const ((S r) ^ 2)).div_const ε
      rw [hinv] at hd
      exact hd
    simp only [masterFlux, angularDerivative,
      derivWithin_zero_of_not_differentiableWithinAt hreg,
      derivWithin_zero_of_not_differentiableWithinAt hnotlog, mul_zero]

/-- The flux itself is a positive rescaling of the profile derivative. -/
theorem masterFlux_nonnegative_iff
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ} {r x : ℝ}
    (hε : 0 < ε) (hS : 0 < S r) (hP : 0 ≤ P r x)
    (hx : x ∈ angularInterval)
    (hreg : DifferentiableWithinAt ℝ (P r) angularInterval x) :
    0 ≤ masterFlux ε S P r x ↔ 0 ≤ angularDerivative P r x := by
  rw [masterFlux_eq_scaledDerivative hε hS hP hx hreg]
  exact mul_nonneg_iff_of_pos_left (by positivity)

/-- Sub_1 and Sub_2 are unchanged by the positive logarithmic normalization. -/
theorem logMaster_iff_profileMaster
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ}
    (hε : 0 < ε) (hS : NormalizerPositive S)
    (hP : ProfileNonnegative P) (hreg : ProfileRegular P) :
    LogMaster ε S P ↔ ProfileMaster P := by
  have hscale (r : ℝ) (hr : 0 < r) (x : ℝ) (hx : x ∈ angularInterval) :=
    masterFlux_eq_scaledDerivative hε (hS r hr) (hP r hr x hx) hx (hreg r hr x hx)
  constructor
  · intro h
    constructor
    · intro r hr x hx
      have hm := (h r hr x hx).1
      rw [hscale r hr (-1) neg_one_mem_angularInterval, hscale r hr x hx] at hm
      exact (mul_le_mul_iff_right₀ (div_pos hε (sq_pos_of_pos (hS r hr)))).mp hm
    · intro r hr
      have hb := (h r hr (-1) neg_one_mem_angularInterval).2
      rw [hscale r hr (-1) neg_one_mem_angularInterval] at hb
      exact (mul_nonneg_iff_of_pos_left (div_pos hε (sq_pos_of_pos (hS r hr)))).mp hb
  · rintro ⟨hmin, hboundary⟩ r hr x hx
    rw [hscale r hr (-1) neg_one_mem_angularInterval, hscale r hr x hx]
    exact ⟨mul_le_mul_of_nonneg_left (hmin r hr x hx) (by positivity),
      mul_nonneg (by positivity) (hboundary r hr)⟩

/-- Normalization invariance for total within derivatives.  Global
    nonnegativity makes the logarithmic transform smoothly invertible wherever
    a profile derivative exists; no regularity assumption is hidden here. -/
theorem logMaster_iff_profileMaster_total
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ}
    (hε : 0 < ε) (hS : NormalizerPositive S)
    (hPall : ∀ r, 0 < r → ∀ x, 0 ≤ P r x) :
    LogMaster ε S P ↔ ProfileMaster P := by
  have hscale (r : ℝ) (hr : 0 < r) (x : ℝ) (hx : x ∈ angularInterval) :=
    masterFlux_eq_scaledDerivative_total hε (hS r hr) (hPall r hr) hx
  constructor
  · intro h
    constructor
    · intro r hr x hx
      have hm := (h r hr x hx).1
      rw [hscale r hr (-1) neg_one_mem_angularInterval, hscale r hr x hx] at hm
      exact (mul_le_mul_iff_right₀ (div_pos hε (sq_pos_of_pos (hS r hr)))).mp hm
    · intro r hr
      have hb := (h r hr (-1) neg_one_mem_angularInterval).2
      rw [hscale r hr (-1) neg_one_mem_angularInterval] at hb
      exact (mul_nonneg_iff_of_pos_left (div_pos hε (sq_pos_of_pos (hS r hr)))).mp hb
  · rintro ⟨hmin, hboundary⟩ r hr x hx
    rw [hscale r hr (-1) neg_one_mem_angularInterval, hscale r hr x hx]
    exact ⟨mul_le_mul_of_nonneg_left (hmin r hr x hx) (by positivity),
      mul_nonneg (by positivity) (hboundary r hr)⟩

/-- The two Master inequalities imply nonnegative derivative everywhere. -/
theorem derivativeNonnegative_of_profileMaster
    {P : ℝ → ℝ → ℝ} (h : ProfileMaster P) : DerivativeNonnegative P := by
  intro r hr x hx
  exact (h.2 r hr).trans (h.1 r hr x hx)

/-- Monotonicity of the derivative is a sufficient condition for Sub_1. -/
theorem angularMinimum_of_monotoneDerivative
    {P : ℝ → ℝ → ℝ}
    (hmono : ∀ r, 0 < r → MonotoneOn (angularDerivative P r) angularInterval) :
    AngularMinimum P := by
  intro r hr x hx
  exact hmono r hr neg_one_mem_angularInterval hx hx.1

/-- A stronger sufficient condition: increasing derivative and boundary positivity. -/
theorem profileMaster_of_monotoneDerivative
    {P : ℝ → ℝ → ℝ}
    (hmono : ∀ r, 0 < r → MonotoneOn (angularDerivative P r) angularInterval)
    (hboundary : BoundaryNonnegative P) : ProfileMaster P :=
  ⟨angularMinimum_of_monotoneDerivative hmono, hboundary⟩

/-- The weaker regularity sufficient for the mean-value theorem: continuity at
    both endpoints and differentiability in the open angular interval. -/
def InteriorRegular (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → ContinuousOn (P r) angularInterval ∧
    DifferentiableOn ℝ (P r) (Set.Ioo (-1) 1)

/-- Nonnegative derivative implies angular monotonicity without requiring an
    endpoint differentiability theorem. -/
theorem profile_monotone_of_derivativeNonnegative_interior
    {P : ℝ → ℝ → ℝ}
    (hcont : ∀ r, 0 < r → ContinuousOn (P r) angularInterval)
    (hint : ∀ r, 0 < r → DifferentiableOn ℝ (P r) (Set.Ioo (-1) 1))
    (hderiv : DerivativeNonnegative P) (r : ℝ) (hr : 0 < r) :
    MonotoneOn (P r) angularInterval := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (-1 : ℝ) 1) (hcont r hr)
  · simpa only [angularInterval, interior_Icc] using hint r hr
  · intro x hx
    have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      simpa only [angularInterval, interior_Icc] using hx
    have hd := hderiv r hr x ⟨hxi.1.le, hxi.2.le⟩
    change 0 ≤ derivWithin (P r) (Set.Icc (-1) 1) x at hd
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hxi.1 hxi.2)] at hd
    exact hd

/-- The logarithmic Master implies angular monotonicity using only interior
    differentiability.  No endpoint derivative identification is used here. -/
theorem profile_monotone_of_logMaster_interior
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ}
    (hε : 0 < ε) (hS : NormalizerPositive S) (hP : ProfileNonnegative P)
    (hcont : ∀ r, 0 < r → ContinuousOn (P r) angularInterval)
    (hint : ∀ r, 0 < r → DifferentiableOn ℝ (P r) (Set.Ioo (-1) 1))
    (hmaster : LogMaster ε S P) (r : ℝ) (hr : 0 < r) :
    MonotoneOn (P r) angularInterval := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (-1 : ℝ) 1) (hcont r hr)
  · simpa only [angularInterval, interior_Icc] using hint r hr
  · intro x hx
    have hxi : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      simpa only [angularInterval, interior_Icc] using hx
    have hxc : x ∈ angularInterval := ⟨hxi.1.le, hxi.2.le⟩
    have hdiff : DifferentiableWithinAt ℝ (P r) angularInterval x :=
      ((hint r hr x hxi).differentiableAt (isOpen_Ioo.mem_nhds hxi)).differentiableWithinAt
    have hflux : 0 ≤ masterFlux ε S P r x :=
      (hmaster r hr x hxc).2.trans (hmaster r hr x hxc).1
    have hd := (masterFlux_nonnegative_iff hε (hS r hr) (hP r hr x hxc) hxc hdiff).mp hflux
    change 0 ≤ derivWithin (P r) (Set.Icc (-1) 1) x at hd
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hxi.1 hxi.2)] at hd
    exact hd

/-- Nonnegative within derivatives imply monotonicity of the angular profile. -/
theorem profile_monotone_of_derivativeNonnegative
    {P : ℝ → ℝ → ℝ} (hreg : ProfileRegular P)
    (hderiv : DerivativeNonnegative P) (r : ℝ) (hr : 0 < r) :
    MonotoneOn (P r) angularInterval := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-1 : ℝ) 1)
      (hreg r hr).continuousOn
  · intro x hx
    exact ((hreg r hr x (interior_subset hx)).hasDerivWithinAt).mono
      interior_subset
  · intro x hx
    exact hderiv r hr x (interior_subset hx)

/-- Master positivity gives monotonicity, the input for angular zero exclusion. -/
theorem profile_monotone_of_logMaster
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ}
    (hε : 0 < ε) (hS : NormalizerPositive S)
    (hP : ProfileNonnegative P) (hreg : ProfileRegular P)
    (hmaster : LogMaster ε S P) (r : ℝ) (hr : 0 < r) :
    MonotoneOn (P r) angularInterval :=
  profile_monotone_of_derivativeNonnegative hreg
    (derivativeNonnegative_of_profileMaster
      ((logMaster_iff_profileMaster hε hS hP hreg).mp hmaster)) r hr

/-- The logarithmic object is bounded whenever the squared modulus is normalized. -/
theorem masterLog_bounds
    {ε : ℝ} {S : ℝ → ℝ} {P : ℝ → ℝ → ℝ} {r x : ℝ}
    (hε : 0 ≤ ε) (hS : 0 < S r) (hP : 0 ≤ P r x)
    (hbound : P r x ≤ (S r) ^ 2) :
    0 ≤ masterLog ε S P r x ∧ masterLog ε S P r x ≤ Real.log (1 + ε) := by
  have hS2 : 0 < (S r) ^ 2 := sq_pos_of_pos hS
  have hratio : ε * P r x / (S r) ^ 2 ≤ ε := by
    apply (div_le_iff₀ hS2).mpr
    exact mul_le_mul_of_nonneg_left hbound hε
  have harg : 0 < 1 + ε * P r x / (S r) ^ 2 := by positivity
  constructor
  · apply Real.log_nonneg
    have hnonneg : 0 ≤ ε * P r x / (S r) ^ 2 := by positivity
    linarith
  · exact Real.log_le_log harg (by linarith)

end AngularMaster
