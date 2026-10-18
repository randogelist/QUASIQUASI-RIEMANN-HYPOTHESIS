import AngularMaster.ActualProfile
import AngularMaster.ProductValueLimit

noncomputable section
open Filter
open scoped Topology BigOperators

namespace AngularMaster

/-- Finite canonical products with zeros at `-α i`. -/
def finiteCanonicalProduct (α : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range N, (1 + z / (α i : ℂ))

/-- The squared modulus of a canonical linear factor is the angular factor,
including at the two endpoints. -/
theorem normSq_canonicalFactor_circlePoint (a r x : ℝ)
    (hx : x ∈ angularInterval) :
    Complex.normSq (1 + circlePoint r x / (a : ℂ)) = genusZeroFactor a r x := by
  have hs : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := by
    apply Real.sq_sqrt
    rcases hx with ⟨hlo, hhi⟩
    nlinarith
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, zero_add]
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add,
    circlePoint_re, circlePoint_im]
  dsimp [genusZeroFactor]
  simp only [div_eq_mul_inv]
  linear_combination (r * a⁻¹) ^ 2 * hs

/-- Finite canonical products become precisely the finite angular products. -/
theorem normSq_finiteCanonicalProduct_circlePoint (α : ℕ → ℝ)
    (r : ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ angularInterval) :
    Complex.normSq (finiteCanonicalProduct α N (circlePoint r x)) =
      finiteProductProfile α r N x := by
  unfold finiteCanonicalProduct finiteProductProfile
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => normSq_canonicalFactor_circlePoint (α i) r x hx)

/-- Pointwise canonical factorization gives the corresponding pointwise angular
squared-modulus limit. The leading constant can be complex. No factorization of
the actual theta is asserted here. -/
theorem angularNormSq_tendsto_of_complexCanonicalProduct
    {f : ℂ → ℂ} {α : ℕ → ℝ} {k : ℂ}
    (hprod : ∀ z : ℂ, Tendsto (fun N => k * finiteCanonicalProduct α N z)
      atTop (𝓝 (f z)))
    (r : ℝ) {x : ℝ} (hx : x ∈ angularInterval) :
    Tendsto (fun N => Complex.normSq k * finiteProductProfile α r N x)
      atTop (𝓝 (angularNormSq f r x)) := by
  have h := Complex.continuous_normSq.continuousAt.tendsto.comp (hprod (circlePoint r x))
  simpa only [Function.comp_def, map_mul,
    normSq_finiteCanonicalProduct_circlePoint α r _ hx, angularNormSq] using h

/-- The real-constant specialization, with multiplier `k²`. -/
theorem angularNormSq_tendsto_of_canonicalProduct
    {f : ℂ → ℂ} {α : ℕ → ℝ} {k : ℝ}
    (hprod : ∀ z : ℂ, Tendsto (fun N => (k : ℂ) * finiteCanonicalProduct α N z)
      atTop (𝓝 (f z)))
    (r : ℝ) {x : ℝ} (hx : x ∈ angularInterval) :
    Tendsto (fun N => k ^ 2 * finiteProductProfile α r N x)
      atTop (𝓝 (angularNormSq f r x)) := by
  simpa only [Complex.normSq_ofReal, pow_two] using
    angularNormSq_tendsto_of_complexCanonicalProduct hprod r hx

end AngularMaster
