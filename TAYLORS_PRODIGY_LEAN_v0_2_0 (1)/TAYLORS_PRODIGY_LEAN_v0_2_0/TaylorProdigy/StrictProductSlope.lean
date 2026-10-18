import AngularMaster.ProductLimit
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace TaylorsProdigy
open AngularMaster

theorem genusZeroFactor_pos {a r x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hx : -1 < x) :
    0 < genusZeroFactor a r x := by
  unfold genusZeroFactor
  have hcoef : 0 < 2 * r / a := div_pos (by positivity) ha
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hcoef (by linarith))

/-- Removing any one positive affine factor leaves a monotone quotient.
Only convergence of values is needed; no derivative interchange is assumed. -/
theorem monotoneOn_quotient_of_product_values
    {ι : Type*} {P : ℝ → ℝ} {α : ι → ℝ} {c r : ℝ}
    (hα : ∀ i, 0 < α i) (hc : 0 ≤ c) (hr : 0 < r)
    (hp : ∀ x ∈ Ioi (-1 : ℝ),
      Tendsto (fun s : Finset ι => c * ∏ j ∈ s, genusZeroFactor (α j) r x)
        atTop (𝓝 (P x))) (i : ι) :
    MonotoneOn (fun x => P x / genusZeroFactor (α i) r x) (Ioi (-1 : ℝ)) := by
  classical
  intro x hx y hy hxy
  apply le_of_tendsto_of_tendsto
    ((hp x hx).div_const (genusZeroFactor (α i) r x))
    ((hp y hy).div_const (genusZeroFactor (α i) r y))
  filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with s hs
  have his : i ∈ s := hs (by simp)
  have heq (t : ℝ) (ht : -1 < t) :
      (c * ∏ j ∈ s, genusZeroFactor (α j) r t) /
        genusZeroFactor (α i) r t =
      c * ∏ j ∈ s.erase i, genusZeroFactor (α j) r t := by
    rw [← Finset.mul_prod_erase s (fun j => genusZeroFactor (α j) r t) his]
    field_simp [ne_of_gt (genusZeroFactor_pos (hα i) hr ht)]
  rw [heq x hx, heq y hy]
  apply mul_le_mul_of_nonneg_left ?_ hc
  exact Finset.prod_le_prod
    (fun j _ => (genusZeroFactor_pos (hα j) hr hx).le)
    (fun j _ => genusZeroFactor_mono (hα j) hr hxy)

/-- A quantitative lower bound for the actual derivative of the limit.
It is strictly positive wherever the profile is positive. -/
theorem deriv_lower_bound_of_product_values
    {ι : Type*} {P : ℝ → ℝ} {α : ι → ℝ} {c r x : ℝ}
    (hα : ∀ i, 0 < α i) (hc : 0 ≤ c) (hr : 0 < r)
    (hp : ∀ t ∈ Ioi (-1 : ℝ),
      Tendsto (fun s : Finset ι => c * ∏ j ∈ s, genusZeroFactor (α j) r t)
        atTop (𝓝 (P t)))
    (hx : x ∈ Ioi (-1 : ℝ)) (hd : DifferentiableAt ℝ P x) (i : ι) :
    (2 * r / α i) * (P x / genusZeroFactor (α i) r x) ≤ deriv P x := by
  have hfac : 0 < genusZeroFactor (α i) r x := genusZeroFactor_pos (hα i) hr hx
  have hm := monotoneOn_quotient_of_product_values hα hc hr hp i
  have hnonneg : 0 ≤ deriv (fun t => P t / genusZeroFactor (α i) r t) x := by
    have hwithin := hm.derivWithin_nonneg (x := x)
    rwa [derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hx)] at hwithin
  have hderiv := (hd.hasDerivAt.div
    (genusZeroFactor_hasDerivAt (α i) r x) (ne_of_gt hfac)).deriv
  change 0 ≤ deriv (P / genusZeroFactor (α i) r) x at hnonneg
  rw [hderiv] at hnonneg
  have hnum : 0 ≤ deriv P x * genusZeroFactor (α i) r x - P x * (2 * r / α i) := by
    simpa only [zero_mul] using (le_div_iff₀ (sq_pos_of_pos hfac)).mp hnonneg
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hfac).2
  nlinarith

/-- A single factor suffices for strict positivity of the derivative. -/
theorem deriv_pos_of_product_values
    {ι : Type*} {P : ℝ → ℝ} {α : ι → ℝ} {c r x : ℝ}
    (hα : ∀ i, 0 < α i) (hc : 0 ≤ c) (hr : 0 < r)
    (hp : ∀ t ∈ Ioi (-1 : ℝ),
      Tendsto (fun s : Finset ι => c * ∏ j ∈ s, genusZeroFactor (α j) r t)
        atTop (𝓝 (P t)))
    (hx : x ∈ Ioi (-1 : ℝ)) (hd : DifferentiableAt ℝ P x)
    (hP : 0 < P x) (i : ι) : 0 < deriv P x := by
  have hfac : 0 < genusZeroFactor (α i) r x := genusZeroFactor_pos (hα i) hr hx
  have hcoef : 0 < 2 * r / α i := div_pos (by positivity) (hα i)
  exact lt_of_lt_of_le (mul_pos hcoef (div_pos hP hfac))
    (deriv_lower_bound_of_product_values hα hc hr hp hx hd i)

end TaylorsProdigy
