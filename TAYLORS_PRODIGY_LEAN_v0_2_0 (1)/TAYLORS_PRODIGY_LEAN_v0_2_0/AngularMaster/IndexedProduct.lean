import AngularMaster.ProductValueLimit

noncomputable section
open Filter
open scoped Topology BigOperators

namespace AngularMaster

variable {ι : Type*}

/-- An angular product over a finite subset of an arbitrary divisor index. -/
def indexedFiniteProductProfile (α : ι → ℝ) (r : ℝ) (s : Finset ι) (x : ℝ) : ℝ :=
  ∏ i ∈ s, genusZeroFactor (α i) r x

/-- Its literal angular derivative. -/
def indexedFiniteProductFlux [DecidableEq ι]
    (α : ι → ℝ) (r : ℝ) (s : Finset ι) (x : ℝ) : ℝ :=
  ∑ j ∈ s, (2 * r / α j) * ∏ i ∈ s.erase j, genusZeroFactor (α i) r x

/-- The holomorphic extension in the angular coordinate. -/
def indexedComplexFiniteProductProfile (α : ι → ℝ)
    (r : ℝ) (s : Finset ι) (z : ℂ) : ℂ :=
  ∏ i ∈ s,
    ((((1 - r / α i) ^ 2 : ℝ) : ℂ) + ((2 * r / α i : ℝ) : ℂ) * (z + 1))

theorem indexedComplexFiniteProductProfile_differentiable
    (α : ι → ℝ) (r : ℝ) (s : Finset ι) :
    Differentiable ℂ (indexedComplexFiniteProductProfile α r s) := by
  unfold indexedComplexFiniteProductProfile
  fun_prop

theorem indexedComplexFiniteProductProfile_ofReal
    (α : ι → ℝ) (r : ℝ) (s : Finset ι) (x : ℝ) :
    indexedComplexFiniteProductProfile α r s (x : ℂ) =
      (indexedFiniteProductProfile α r s x : ℂ) := by
  simp only [indexedComplexFiniteProductProfile, indexedFiniteProductProfile,
    genusZeroFactor, Complex.ofReal_prod, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one]

theorem indexedFiniteProductProfile_hasDerivAt [DecidableEq ι]
    (α : ι → ℝ) (r : ℝ) (s : Finset ι) (x : ℝ) :
    HasDerivAt (indexedFiniteProductProfile α r s)
      (indexedFiniteProductFlux α r s x) x := by
  have h := HasDerivAt.fun_finsetProd (𝕜 := ℝ) (𝔸' := ℝ)
    (u := s) (fun i _ => genusZeroFactor_hasDerivAt (α i) r x)
  convert! h using 1
  simp only [indexedFiniteProductFlux, smul_eq_mul, mul_comm]

theorem indexedFiniteProductFlux_nonnegative [DecidableEq ι]
    {α : ι → ℝ} {r x : ℝ}
    (hα : ∀ i, 0 < α i) (hr : 0 < r) (hx : -1 ≤ x) (s : Finset ι) :
    0 ≤ indexedFiniteProductFlux α r s x := by
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (div_nonneg (by positivity) (le_of_lt (hα j)))
  exact Finset.prod_nonneg (fun i _ => genusZeroFactor_nonnegative (hα i) hr hx)

theorem indexedFiniteProductFlux_mono [DecidableEq ι]
    {α : ι → ℝ} {r x y : ℝ}
    (hα : ∀ i, 0 < α i) (hr : 0 < r) (hx : -1 ≤ x) (hxy : x ≤ y)
    (s : Finset ι) :
    indexedFiniteProductFlux α r s x ≤ indexedFiniteProductFlux α r s y := by
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (le_of_lt (hα j)))
  exact Finset.prod_le_prod
    (fun i _ => genusZeroFactor_nonnegative (hα i) hr hx)
    (fun i _ => genusZeroFactor_mono (hα i) hr hxy)

theorem scaled_indexedComplexFiniteProductProfile_deriv_re [DecidableEq ι]
    (α : ι → ℝ) (c r : ℝ) (s : Finset ι) (x : ℝ) :
    (deriv (fun z => (c : ℂ) * indexedComplexFiniteProductProfile α r s z) (x : ℂ)).re =
      c * indexedFiniteProductFlux α r s x := by
  have hcomplex : Differentiable ℂ
      (fun z => (c : ℂ) * indexedComplexFiniteProductProfile α r s z) :=
    (indexedComplexFiniteProductProfile_differentiable α r s).const_mul c
  have hreal := (hcomplex (x : ℂ)).hasDerivAt.real_of_complex
  have heq : (fun y : ℝ =>
      ((c : ℂ) * indexedComplexFiniteProductProfile α r s (y : ℂ)).re) =
      (fun y : ℝ => c * indexedFiniteProductProfile α r s y) := by
    funext y
    rw [indexedComplexFiniteProductProfile_ofReal]
    simp
  rw [heq] at hreal
  exact hreal.unique ((indexedFiniteProductProfile_hasDerivAt α r s x).const_mul c)

/-- Locally uniform finite-subset product values imply the Master, without
requiring a countably infinite enumeration of the divisor. -/
theorem profileMaster_of_indexedProductValues
    {P : ℝ → ℝ → ℝ} {α : ι → ℝ} {c : ℝ → ℝ} {F : ℝ → ℂ → ℂ}
    (hα : ∀ i, 0 < α i) (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hlim : ∀ r, 0 < r → TendstoLocallyUniformlyOn
      (fun s z => (c r : ℂ) * indexedComplexFiniteProductProfile α r s z)
      (F r) atTop Set.univ)
    (hagree : ∀ r, 0 < r → ∀ x ∈ angularInterval, (F r (x : ℂ)).re = P r x) :
    ProfileMaster P := by
  classical
  have hderiv : ∀ r, 0 < r → ∀ x ∈ angularInterval,
      Tendsto (fun s => c r * indexedFiniteProductFlux α r s x)
        atTop (𝓝 (angularDerivative P r x)) := by
    intro r hr x hx
    have hpoly : ∀ᶠ s : Finset ι in atTop,
        DifferentiableOn ℂ
          (fun z => (c r : ℂ) * indexedComplexFiniteProductProfile α r s z) Set.univ :=
      Eventually.of_forall (fun s =>
        ((indexedComplexFiniteProductProfile_differentiable α r s).const_mul
          (c r)).differentiableOn)
    have hF : DifferentiableOn ℂ (F r) Set.univ :=
      (hlim r hr).differentiableOn hpoly isOpen_univ
    have hreal : HasDerivWithinAt (P r) (deriv (F r) (x : ℂ)).re angularInterval x := by
      have h := (hF.differentiableAt (Filter.univ_mem : Set.univ ∈ 𝓝 (x : ℂ))).hasDerivAt
      exact h.real_of_complex.hasDerivWithinAt.congr_of_mem
        (fun y hy => (hagree r hr y hy).symm) hx
    have hid : angularDerivative P r x = (deriv (F r) (x : ℂ)).re :=
      hreal.derivWithin (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1) x hx)
    have hd := ((hlim r hr).deriv hpoly isOpen_univ).tendsto_at (Set.mem_univ (x : ℂ))
    have hdre := Complex.continuous_re.continuousAt.tendsto.comp hd
    change Tendsto (fun s =>
        (deriv (fun z => (c r : ℂ) * indexedComplexFiniteProductProfile α r s z) (x : ℂ)).re)
        atTop (𝓝 (deriv (F r) (x : ℂ)).re) at hdre
    simpa only [scaled_indexedComplexFiniteProductProfile_deriv_re, hid] using hdre
  constructor
  · intro r hr x hx
    exact le_of_tendsto_of_tendsto'
      (hderiv r hr (-1) neg_one_mem_angularInterval) (hderiv r hr x hx)
      (fun s => mul_le_mul_of_nonneg_left
        (indexedFiniteProductFlux_mono hα hr le_rfl hx.1 s) (hc r hr))
  · intro r hr
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds
      (hderiv r hr (-1) neg_one_mem_angularInterval)
      (fun s => mul_nonneg (hc r hr) (indexedFiniteProductFlux_nonnegative hα hr le_rfl s))

/-- Pointwise real value identification is enough once complex local uniform
convergence has been proved independently. -/
theorem profileMaster_of_indexedProductValues_and_pointwise
    {P : ℝ → ℝ → ℝ} {α : ι → ℝ} {c : ℝ → ℝ} {F : ℝ → ℂ → ℂ}
    (hα : ∀ i, 0 < α i) (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hlim : ∀ r, 0 < r → TendstoLocallyUniformlyOn
      (fun s z => (c r : ℂ) * indexedComplexFiniteProductProfile α r s z)
      (F r) atTop Set.univ)
    (hpoint : ∀ r, 0 < r → ∀ x ∈ angularInterval,
      Tendsto (fun s => c r * indexedFiniteProductProfile α r s x)
        atTop (𝓝 (P r x))) : ProfileMaster P := by
  apply profileMaster_of_indexedProductValues hα hc hlim
  intro r hr x hx
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    ((hlim r hr).tendsto_at (Set.mem_univ (x : ℂ)))
  have h' : Tendsto (fun s => c r * indexedFiniteProductProfile α r s x)
      atTop (𝓝 (F r (x : ℂ)).re) := by
    simpa only [Function.comp_def, indexedComplexFiniteProductProfile_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re] using h
  exact tendsto_nhds_unique h' (hpoint r hr x hx)

end AngularMaster
