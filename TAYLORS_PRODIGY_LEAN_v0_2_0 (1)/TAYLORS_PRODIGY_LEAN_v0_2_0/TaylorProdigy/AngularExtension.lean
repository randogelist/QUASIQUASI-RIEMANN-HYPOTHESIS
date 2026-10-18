import AngularMaster.ProductSummability
import TaylorProdigy.Objects

/-!
# A smooth extension of the angular slope

The real part of the locally uniform holomorphic angular product gives a
globally smooth real profile.  On the geometric angular interval it agrees
with the actual profile whenever their finite product values have the same
limit.  Its angular derivative therefore extends the interior slope through
the positive real axis; the endpoint value of Lean's total derivative of the
square-root parametrization is not used.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace TaylorsProdigy

variable {ι : Type*}

def realProduct (b : ι → ℝ) (r x : ℝ) : ℝ :=
  (AngularMaster.complexIndexedAngularProduct b r (x : ℂ)).re

def extendedSlope (b : ι → ℝ) (r : ℝ) : ℝ → ℝ :=
  deriv (realProduct b r)

def angleExtension (b : ι → ℝ) (r θ : ℝ) : ℝ :=
  extendedSlope b r (Real.cos θ)

theorem complexIndexedAngularProduct_differentiable
    {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {r : ℝ} (hr : 0 ≤ r) :
    Differentiable ℂ (AngularMaster.complexIndexedAngularProduct b r) := by
  have hu := AngularMaster.indexedComplexProfile_tendstoLocallyUniformlyOn hb hs hr
  have hp : ∀ᶠ s : Finset ι in atTop,
      DifferentiableOn ℂ (AngularMaster.indexedComplexProfile b r s) univ :=
    Eventually.of_forall (fun s =>
      (AngularMaster.indexedComplexProfile_differentiable b r s).differentiableOn)
  exact differentiableOn_univ.mp (hu.differentiableOn hp isOpen_univ)

theorem realProduct_contDiff
    {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {r : ℝ} (hr : 0 ≤ r) : ContDiff ℝ ⊤ (realProduct b r) := by
  have hcomplex := ContDiff.restrict_scalars ℝ
    ((complexIndexedAngularProduct_differentiable hb hs hr).contDiff :
      ContDiff ℂ ⊤ (AngularMaster.complexIndexedAngularProduct b r))
  exact Complex.reCLM.contDiff.comp (hcomplex.comp Complex.ofRealCLM.contDiff)

theorem extendedSlope_contDiff
    {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {r : ℝ} (hr : 0 ≤ r) : ContDiff ℝ ⊤ (extendedSlope b r) := by
  exact (realProduct_contDiff hb hs hr).deriv'

theorem angleExtension_contDiff
    {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {r : ℝ} (hr : 0 ≤ r) : ContDiff ℝ ⊤ (angleExtension b r) := by
  exact (extendedSlope_contDiff hb hs hr).comp Real.contDiff_cos

/-- Finite product values converge on every real angular coordinate, including
the positive-axis endpoint and a neighborhood on both sides of it. -/
theorem indexedProductValues_tendsto_realProduct
    {α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (hs : Summable (fun i => 1 / α i))
    {r : ℝ} (hr : 0 ≤ r) (c x : ℝ) :
    Tendsto (fun s : Finset ι =>
      c * AngularMaster.indexedFiniteProductProfile α r s x) atTop
      (𝓝 (c * realProduct (fun i => 1 / α i) r x)) := by
  have hu := AngularMaster.scaled_indexedComplexProfile_tendstoLocallyUniformlyOn
    (fun i => le_of_lt (one_div_pos.mpr (hα i))) hs hr c
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (hu.tendsto_at (mem_univ (x : ℂ)))
  change Tendsto (fun s : Finset ι =>
    ((c : ℂ) * AngularMaster.indexedComplexProfile (fun i => 1 / α i) r s
      (x : ℂ)).re) atTop
    (𝓝 (((c : ℂ) * AngularMaster.complexIndexedAngularProduct
      (fun i => 1 / α i) r (x : ℂ)).re)) at h
  simpa only [← AngularMaster.indexedComplexFiniteProductProfile_eq_reciprocal,
    AngularMaster.indexedComplexFiniteProductProfile_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, realProduct] using h

theorem scaled_realProduct_eq_actualProfile
    {α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (hs : Summable (fun i => 1 / α i)) {c r : ℝ} (hr : 0 < r)
    (hp : ∀ x ∈ AngularMaster.angularInterval,
      Tendsto (fun s : Finset ι =>
        c * AngularMaster.indexedFiniteProductProfile α r s x) atTop
        (𝓝 (AngularMaster.actualProfile r x)))
    {x : ℝ} (hx : x ∈ AngularMaster.angularInterval) :
    c * realProduct (fun i => 1 / α i) r x = AngularMaster.actualProfile r x :=
  tendsto_nhds_unique (indexedProductValues_tendsto_realProduct hα hs hr.le c x)
    (hp x hx)

theorem scaled_extendedSlope_eq_H
    {α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (hs : Summable (fun i => 1 / α i)) {c r : ℝ} (hr : 0 < r)
    (hp : ∀ x ∈ AngularMaster.angularInterval,
      Tendsto (fun s : Finset ι =>
        c * AngularMaster.indexedFiniteProductProfile α r s x) atTop
        (𝓝 (AngularMaster.actualProfile r x)))
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    c * extendedSlope (fun i => 1 / α i) r x = H r x := by
  have heq : (fun t => c * realProduct (fun i => 1 / α i) r t) =ᶠ[𝓝 x]
      AngularMaster.actualProfile r := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact scaled_realProduct_eq_actualProfile hα hs hr hp ⟨ht.1.le, ht.2.le⟩
  have hd := (realProduct_contDiff
    (fun i => le_of_lt (one_div_pos.mpr (hα i))) hs hr.le).differentiable (by simp)
  change c * deriv (realProduct (fun i => 1 / α i) r) x =
    deriv (AngularMaster.actualProfile r) x
  rw [← ((hd x).hasDerivAt.const_mul c).deriv]
  exact heq.deriv_eq

theorem scaled_angleExtension_eq_F
    {α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (hs : Summable (fun i => 1 / α i)) {c r : ℝ} (hr : 0 < r)
    (hp : ∀ x ∈ AngularMaster.angularInterval,
      Tendsto (fun s : Finset ι =>
        c * AngularMaster.indexedFiniteProductProfile α r s x) atTop
        (𝓝 (AngularMaster.actualProfile r x)))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    c * angleExtension (fun i => 1 / α i) r θ = F r θ :=
  scaled_extendedSlope_eq_H hα hs hr hp (cos_mem_interior hθ)

theorem scaled_angleExtension_eventuallyEq_F
    {α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (hs : Summable (fun i => 1 / α i)) {c r : ℝ} (hr : 0 < r)
    (hp : ∀ x ∈ AngularMaster.angularInterval,
      Tendsto (fun s : Finset ι =>
        c * AngularMaster.indexedFiniteProductProfile α r s x) atTop
        (𝓝 (AngularMaster.actualProfile r x)))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    (fun t => c * angleExtension (fun i => 1 / α i) r t) =ᶠ[𝓝 θ] F r := by
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  exact scaled_angleExtension_eq_F hα hs hr hp ht

end TaylorsProdigy
