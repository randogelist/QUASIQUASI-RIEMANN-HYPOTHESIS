import AngularMaster.Calculus
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.OrderClosed

/-!
# Positive genus-zero angular factors and limits

The elementary factor is
`(1 - r / a)^2 + (2 * r / a) * (x + 1)`.
For `a > 0`, it is nonnegative on `x >= -1` and increasing in `x`.
Its finite products have nonnegative increasing angular derivatives.

`ProductDerivativeLimit P` is an explicit **analytic input**: the actual within
derivative of `P` must be the limit of the displayed finite-product derivatives.
This file proves that such a limit satisfies both Master inequalities.  It does
not assert a Hadamard factorization, derivative convergence for the Riemann xi
function, or RH.  The radial multiplier allows central factors `z^m`.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AngularMaster

/-- Squared modulus of a negative-real-zero factor on the circle of radius `r`. -/
def genusZeroFactor (a r x : ℝ) : ℝ :=
  (1 - r / a) ^ 2 + (2 * r / a) * (x + 1)

/-- A finite angular product with negative zeros `-α i`. -/
def finiteProductProfile (α : ℕ → ℝ) (r : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.range N, genusZeroFactor (α i) r x

/-- The explicitly differentiated finite angular product. -/
def finiteProductFlux (α : ℕ → ℝ) (r : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (2 * r / α j) * ∏ i ∈ (Finset.range N).erase j, genusZeroFactor (α i) r x

theorem genusZeroFactor_nonnegative {a r x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hx : -1 ≤ x) :
    0 ≤ genusZeroFactor a r x := by
  unfold genusZeroFactor
  exact add_nonneg (sq_nonneg _)
    (mul_nonneg (by positivity) (by linarith))

theorem genusZeroFactor_mono {a r x y : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hxy : x ≤ y) :
    genusZeroFactor a r x ≤ genusZeroFactor a r y := by
  unfold genusZeroFactor
  have hc : 0 ≤ 2 * r / a := by positivity
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (add_le_add_left hxy 1) hc) _

theorem genusZeroFactor_hasDerivAt (a r x : ℝ) :
    HasDerivAt (genusZeroFactor a r) (2 * r / a) x := by
  have hid : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
    (hasDerivAt_id x).add_const 1
  have hmul : HasDerivAt (fun y : ℝ => (2 * r / a) * (y + 1)) (2 * r / a) x := by
    simpa only [mul_one] using hid.const_mul (2 * r / a)
  exact hmul.const_add ((1 - r / a) ^ 2)

/-- The displayed flux is the actual ordinary derivative of the finite product. -/
theorem finiteProductProfile_hasDerivAt (α : ℕ → ℝ) (r : ℝ) (N : ℕ) (x : ℝ) :
    HasDerivAt (finiteProductProfile α r N) (finiteProductFlux α r N x) x := by
  have h := HasDerivAt.fun_finsetProd (𝕜 := ℝ) (𝔸' := ℝ)
    (u := Finset.range N) (fun i _ => genusZeroFactor_hasDerivAt (α i) r x)
  convert! h using 1
  simp only [finiteProductFlux, smul_eq_mul, mul_comm]

/-- The same finite-product derivative identity holds at both angular endpoints. -/
theorem finiteProductProfile_angularDerivative
    (α : ℕ → ℝ) (r : ℝ) (N : ℕ) (x : ℝ) (hx : x ∈ angularInterval) :
    angularDerivative (fun r x => finiteProductProfile α r N x) r x =
      finiteProductFlux α r N x := by
  exact (finiteProductProfile_hasDerivAt α r N x).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1) x hx)

theorem finiteProductFlux_nonnegative {α : ℕ → ℝ} {r x : ℝ}
    (hα : ∀ i, 0 < α i) (hr : 0 < r) (hx : -1 ≤ x) (N : ℕ) :
    0 ≤ finiteProductFlux α r N x := by
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (div_nonneg (by positivity) (le_of_lt (hα j)))
  exact Finset.prod_nonneg (fun i _ => genusZeroFactor_nonnegative (hα i) hr hx)

theorem finiteProductFlux_mono {α : ℕ → ℝ} {r x y : ℝ}
    (hα : ∀ i, 0 < α i) (hr : 0 < r) (hx : -1 ≤ x) (hxy : x ≤ y) (N : ℕ) :
    finiteProductFlux α r N x ≤ finiteProductFlux α r N y := by
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (le_of_lt (hα j)))
  exact Finset.prod_le_prod
    (fun i _ => genusZeroFactor_nonnegative (hα i) hr hx)
    (fun i _ => genusZeroFactor_mono (hα i) hr hxy)

/-- Each finite flux has its minimum at `x = -1` on the angular interval. -/
theorem finiteProductFlux_angularMinimum {α : ℕ → ℝ} {r x : ℝ}
    (hα : ∀ i, 0 < α i) (hr : 0 < r) (hx : x ∈ angularInterval) (N : ℕ) :
    finiteProductFlux α r N (-1) ≤ finiteProductFlux α r N x :=
  finiteProductFlux_mono hα hr le_rfl hx.1 N

/-- Every finite negative-zero angular product satisfies the actual Master condition. -/
theorem finiteProductProfile_master {α : ℕ → ℝ}
    (hα : ∀ i, 0 < α i) (N : ℕ) :
    ProfileMaster (fun r x => finiteProductProfile α r N x) := by
  constructor
  · intro r hr x hx
    rw [finiteProductProfile_angularDerivative α r N (-1) neg_one_mem_angularInterval,
      finiteProductProfile_angularDerivative α r N x hx]
    exact finiteProductFlux_angularMinimum hα hr hx N
  · intro r hr
    rw [finiteProductProfile_angularDerivative α r N (-1) neg_one_mem_angularInterval]
    exact finiteProductFlux_nonnegative hα hr le_rfl N

/-- The precise analytic convergence certificate needed for a particular profile.

The coefficient `c r` is independent of the angular variable.  For an entire
genus-zero product with a central factor it is `|C|^2 * r^(2*m)`.
-/
def ProductDerivativeLimit (P : ℝ → ℝ → ℝ) : Prop :=
  ∃ α : ℕ → ℝ, ∃ c : ℝ → ℝ,
    (∀ i, 0 < α i) ∧ (∀ r, 0 < r → 0 ≤ c r) ∧
      ∀ r, 0 < r → ∀ x ∈ angularInterval,
        Tendsto (fun N => c r * finiteProductFlux α r N x) atTop
          (𝓝 (angularDerivative P r x))

/-- Nonnegative finite derivatives stay nonnegative in the asserted limit. -/
theorem derivativeNonnegative_of_productDerivativeLimit
    {P : ℝ → ℝ → ℝ} (h : ProductDerivativeLimit P) : DerivativeNonnegative P := by
  rcases h with ⟨α, c, hα, hc, hlim⟩
  intro r hr x hx
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim r hr x hx)
    (fun N => mul_nonneg (hc r hr) (finiteProductFlux_nonnegative hα hr hx.1 N))

/-- Increasing finite derivatives stay increasing in the asserted limit. -/
theorem monotoneDerivative_of_productDerivativeLimit
    {P : ℝ → ℝ → ℝ} (h : ProductDerivativeLimit P) :
    ∀ r, 0 < r → MonotoneOn (angularDerivative P r) angularInterval := by
  rcases h with ⟨α, c, hα, hc, hlim⟩
  intro r hr x hx y hy hxy
  exact le_of_tendsto_of_tendsto' (hlim r hr x hx) (hlim r hr y hy)
    (fun N => mul_le_mul_of_nonneg_left (finiteProductFlux_mono hα hr hx.1 hxy N)
      (hc r hr))

/-- The two Master inequalities follow from the explicit product derivative limit. -/
theorem profileMaster_of_productDerivativeLimit
    {P : ℝ → ℝ → ℝ} (h : ProductDerivativeLimit P) : ProfileMaster P := by
  apply profileMaster_of_monotoneDerivative (monotoneDerivative_of_productDerivativeLimit h)
  intro r hr
  exact derivativeNonnegative_of_productDerivativeLimit h r hr (-1)
    neg_one_mem_angularInterval

end AngularMaster
