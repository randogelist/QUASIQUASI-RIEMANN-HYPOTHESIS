import AngularMaster.IndexedProduct
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.MetricSpace.Algebra

/-!
# Summable reciprocal zeros imply angular product convergence

This file constructs the locally uniform complex angular product from
`Summable (fun n => 1 / α n)`.  No convergence premise for derivatives or
finite angular products is required.  Identifying this product with the
actual theta profile remains a separate mathematical obligation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace AngularMaster

/-- The perturbation of one in a complex angular factor. -/
def complexAngularDeviation (a r : ℝ) (z : ℂ) : ℂ :=
  (((r / a) ^ 2 : ℝ) : ℂ) + ((2 * r / a : ℝ) : ℂ) * z

/-- The infinite angular product constructed from reciprocal-summable zeros. -/
def complexAngularProduct (α : ℕ → ℝ) (r : ℝ) (z : ℂ) : ℂ :=
  ∏' n, (1 + complexAngularDeviation (α n) r z)

theorem complexFiniteProductProfile_eq_one_add
    (α : ℕ → ℝ) (r : ℝ) (N : ℕ) (z : ℂ) :
    complexFiniteProductProfile α r N z =
      ∏ i ∈ Finset.range N, (1 + complexAngularDeviation (α i) r z) := by
  apply Finset.prod_congr rfl
  intro i hi
  unfold complexAngularDeviation
  push_cast
  ring

theorem summable_reciprocal_sq {α : ℕ → ℝ}
    (hα : ∀ n, 0 < α n) (hs : Summable (fun n => 1 / α n)) :
    Summable (fun n => (1 / α n) ^ 2) := by
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hs.tendsto_atTop_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnonneg : 0 ≤ 1 / α n := le_of_lt (one_div_pos.mpr (hα n))
  nlinarith

theorem complexAngularDeviation_norm_le {a r R : ℝ} {z : ℂ}
    (ha : 0 < a) (hr : 0 ≤ r) (hz : ‖z‖ ≤ R) :
    ‖complexAngularDeviation a r z‖ ≤
      r ^ 2 * (1 / a) ^ 2 + (2 * r * R) * (1 / a) := by
  unfold complexAngularDeviation
  calc
    ‖(((r / a) ^ 2 : ℝ) : ℂ) + ((2 * r / a : ℝ) : ℂ) * z‖
        ≤ ‖(((r / a) ^ 2 : ℝ) : ℂ)‖ + ‖((2 * r / a : ℝ) : ℂ) * z‖ := norm_add_le _ _
    _ = (r / a) ^ 2 + (2 * r / a) * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 2 * r / a)]
    _ ≤ (r / a) ^ 2 + (2 * r / a) * R := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hz
        (by positivity : 0 ≤ 2 * r / a)) _
    _ = r ^ 2 * (1 / a) ^ 2 + (2 * r * R) * (1 / a) := by ring

/-- Reciprocal summability supplies locally uniform convergence on all of `ℂ`. -/
theorem complexAngularProduct_hasProdLocallyUniformlyOn
    {α : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    (hs : Summable (fun n => 1 / α n)) {r : ℝ} (hr : 0 ≤ r) :
    HasProdLocallyUniformlyOn
      (fun n z => 1 + complexAngularDeviation (α n) r z)
      (complexAngularProduct α r) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K hKsub hK
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  have hsum : Summable (fun n => r ^ 2 * (1 / α n) ^ 2 +
      (2 * r * R) * (1 / α n)) :=
    ((summable_reciprocal_sq hα hs).mul_left (r ^ 2)).add (hs.mul_left (2 * r * R))
  exact Summable.hasProdUniformlyOn_nat_one_add hK hsum
    (Eventually.of_forall (fun n z hz =>
      complexAngularDeviation_norm_le (hα n) hr (hbound z hz)))
    (fun n => by unfold complexAngularDeviation; fun_prop)

/-- The original finite angular polynomials converge locally uniformly. -/
theorem complexFiniteProductProfile_tendstoLocallyUniformlyOn
    {α : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    (hs : Summable (fun n => 1 / α n)) {r : ℝ} (hr : 0 ≤ r) :
    TendstoLocallyUniformlyOn
      (complexFiniteProductProfile α r) (complexAngularProduct α r) atTop Set.univ := by
  have heq : complexFiniteProductProfile α r = fun N z =>
      ∏ i ∈ Finset.range N, (1 + complexAngularDeviation (α i) r z) := by
    funext N z
    exact complexFiniteProductProfile_eq_one_add α r N z
  rw [heq]
  exact (complexAngularProduct_hasProdLocallyUniformlyOn hα hs hr).tendstoLocallyUniformlyOn_finsetRange

/-- Multiplication by an angularly constant real coefficient preserves the
locally uniform convergence just proved. -/
theorem scaled_complexFiniteProductProfile_tendstoLocallyUniformlyOn
    {α : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    (hs : Summable (fun n => 1 / α n)) {r : ℝ} (hr : 0 ≤ r) (c : ℝ) :
    TendstoLocallyUniformlyOn
      (fun N z => (c : ℂ) * complexFiniteProductProfile α r N z)
      (fun z => (c : ℂ) * complexAngularProduct α r z) atTop Set.univ := by
  have hu : UniformContinuous (fun z : ℂ => (c : ℂ) * z) := by
    simpa only [smul_eq_mul] using
      (uniformContinuous_const_smul (c : ℂ) :
        UniformContinuous (fun z : ℂ => (c : ℂ) • z))
  exact hu.comp_tendstoLocallyUniformlyOn
    (complexFiniteProductProfile_tendstoLocallyUniformlyOn hα hs hr)

/-- Once reciprocal summability is known, pointwise agreement of the finite
real product limits with `P` suffices.  Local uniform convergence and derivative
convergence are conclusions, not further assumptions. -/
theorem productProfileLimit_of_summable_pointwise_limit
    {P : ℝ → ℝ → ℝ} {α : ℕ → ℝ} {c : ℝ → ℝ}
    (hα : ∀ n, 0 < α n) (hs : Summable (fun n => 1 / α n))
    (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hp : ∀ r, 0 < r → ∀ x ∈ angularInterval,
      Tendsto (fun N => c r * finiteProductProfile α r N x) atTop (𝓝 (P r x))) :
    ProductProfileLimit P := by
  refine ⟨α, c, (fun r z => (c r : ℂ) * complexAngularProduct α r z), hα, hc, ?_, ?_⟩
  · intro r hr
    exact scaled_complexFiniteProductProfile_tendstoLocallyUniformlyOn hα hs hr.le (c r)
  · intro r hr x hx
    have hlim := (scaled_complexFiniteProductProfile_tendstoLocallyUniformlyOn
      hα hs hr.le (c r)).tendsto_at (Set.mem_univ (x : ℂ))
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hlim
    have heq : (fun N =>
        ((c r : ℂ) * complexFiniteProductProfile α r N (x : ℂ)).re) =
        (fun N => c r * finiteProductProfile α r N x) := by
      funext N
      rw [complexFiniteProductProfile_ofReal]
      simp
    change Tendsto (fun N =>
        ((c r : ℂ) * complexFiniteProductProfile α r N (x : ℂ)).re)
      atTop (𝓝 (((c r : ℂ) * complexAngularProduct α r (x : ℂ)).re)) at hre
    rw [heq] at hre
    exact tendsto_nhds_unique hre (hp r hr x hx)

theorem profileMaster_of_summable_pointwise_limit
    {P : ℝ → ℝ → ℝ} {α : ℕ → ℝ} {c : ℝ → ℝ}
    (hα : ∀ n, 0 < α n) (hs : Summable (fun n => 1 / α n))
    (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hp : ∀ r, 0 < r → ∀ x ∈ angularInterval,
      Tendsto (fun N => c r * finiteProductProfile α r N x) atTop (𝓝 (P r x))) :
    ProfileMaster P :=
  profileMaster_of_productProfileLimit
    (productProfileLimit_of_summable_pointwise_limit hα hs hc hp)

/-! ## Arbitrary index sets, including finite zero sets -/

/-- A complex angular factor parameterized by a nonnegative reciprocal zero. -/
def indexedComplexFactor (b r : ℝ) (z : ℂ) : ℂ :=
  (((1 - r * b) ^ 2 : ℝ) : ℂ) + ((2 * r * b : ℝ) : ℂ) * (z + 1)

def indexedComplexProfile {ι : Type*} (b : ι → ℝ) (r : ℝ)
    (s : Finset ι) (z : ℂ) : ℂ :=
  ∏ i ∈ s, indexedComplexFactor (b i) r z

def complexIndexedAngularProduct {ι : Type*} (b : ι → ℝ) (r : ℝ) (z : ℂ) : ℂ :=
  ∏' i, indexedComplexFactor (b i) r z

theorem indexedComplexFactor_eq_one_add (b r : ℝ) (z : ℂ) :
    indexedComplexFactor b r z =
      1 + ((((r * b) ^ 2 : ℝ) : ℂ) + ((2 * r * b : ℝ) : ℂ) * z) := by
  unfold indexedComplexFactor
  push_cast
  ring

theorem indexedComplexProfile_ofReal {ι : Type*} (b : ι → ℝ) (r : ℝ)
    (s : Finset ι) (x : ℝ) :
    indexedComplexProfile b r s (x : ℂ) =
      ((∏ i ∈ s, ((1 - r * b i) ^ 2 + (2 * r * b i) * (x + 1)) : ℝ) : ℂ) := by
  simp only [indexedComplexProfile, indexedComplexFactor, Complex.ofReal_prod,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one]

theorem indexedComplexProfile_differentiable {ι : Type*} (b : ι → ℝ)
    (r : ℝ) (s : Finset ι) : Differentiable ℂ (indexedComplexProfile b r s) := by
  unfold indexedComplexProfile indexedComplexFactor
  fun_prop

theorem summable_sq_of_nonnegative {ι : Type*} {b : ι → ℝ}
    (hb : ∀ i, 0 ≤ b i) (hs : Summable b) : Summable (fun i => (b i) ^ 2) := by
  apply hs.of_norm_bounded_eventually
  filter_upwards [hs.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnonneg := hb i
  nlinarith

theorem indexedAngularDeviation_norm_le {b r R : ℝ} {z : ℂ}
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ R) :
    ‖((((r * b) ^ 2 : ℝ) : ℂ) + ((2 * r * b : ℝ) : ℂ) * z)‖ ≤
      r ^ 2 * b ^ 2 + (2 * r * R) * b := by
  calc
    ‖((((r * b) ^ 2 : ℝ) : ℂ) + ((2 * r * b : ℝ) : ℂ) * z)‖
        ≤ ‖(((r * b) ^ 2 : ℝ) : ℂ)‖ + ‖((2 * r * b : ℝ) : ℂ) * z‖ := norm_add_le _ _
    _ = (r * b) ^ 2 + (2 * r * b) * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 2 * r * b)]
    _ ≤ (r * b) ^ 2 + (2 * r * b) * R := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hz
        (by positivity : 0 ≤ 2 * r * b)) _
    _ = r ^ 2 * b ^ 2 + (2 * r * R) * b := by ring

/-- The construction is valid for an arbitrary zero-index type, even a finite
one; no enumeration or infinitude of zeros is assumed. -/
theorem complexIndexedAngularProduct_hasProdLocallyUniformlyOn
    {ι : Type*} {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {r : ℝ} (hr : 0 ≤ r) :
    HasProdLocallyUniformlyOn (fun i z => indexedComplexFactor (b i) r z)
      (complexIndexedAngularProduct b r) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K hKsub hK
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  have hsum : Summable (fun i => r ^ 2 * (b i) ^ 2 + (2 * r * R) * b i) :=
    ((summable_sq_of_nonnegative hb hs).mul_left (r ^ 2)).add (hs.mul_left (2 * r * R))
  have h := Summable.hasProdUniformlyOn_one_add hK hsum
    (Eventually.of_forall (fun i z hz =>
      indexedAngularDeviation_norm_le (hb i) hr (hbound z hz)))
    (fun i => by fun_prop)
  change HasProdUniformlyOn (fun i z => indexedComplexFactor (b i) r z)
    (fun z => ∏' i, indexedComplexFactor (b i) r z) K
  simp_rw [indexedComplexFactor_eq_one_add]
  exact h

theorem indexedComplexProfile_tendstoLocallyUniformlyOn
    {ι : Type*} {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {r : ℝ} (hr : 0 ≤ r) :
    TendstoLocallyUniformlyOn (indexedComplexProfile b r)
      (complexIndexedAngularProduct b r) atTop Set.univ :=
  complexIndexedAngularProduct_hasProdLocallyUniformlyOn hb hs hr

theorem scaled_indexedComplexProfile_tendstoLocallyUniformlyOn
    {ι : Type*} {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {r : ℝ} (hr : 0 ≤ r) (c : ℝ) :
    TendstoLocallyUniformlyOn
      (fun s z => (c : ℂ) * indexedComplexProfile b r s z)
      (fun z => (c : ℂ) * complexIndexedAngularProduct b r z) atTop Set.univ := by
  have hu : UniformContinuous (fun z : ℂ => (c : ℂ) * z) := by
    simpa only [smul_eq_mul] using
      (uniformContinuous_const_smul (c : ℂ) :
        UniformContinuous (fun z : ℂ => (c : ℂ) • z))
  exact hu.comp_tendstoLocallyUniformlyOn
    (indexedComplexProfile_tendstoLocallyUniformlyOn hb hs hr)

/-- The reciprocal-parameter form agrees with the positive-zero-coordinate
form used by the indexed derivative calculus. -/
theorem indexedComplexFiniteProductProfile_eq_reciprocal
    {ι : Type*} (α : ι → ℝ) (r : ℝ) (s : Finset ι) (z : ℂ) :
    indexedComplexFiniteProductProfile α r s z =
      indexedComplexProfile (fun i => 1 / α i) r s z := by
  simp only [indexedComplexFiniteProductProfile, indexedComplexProfile,
    indexedComplexFactor, div_eq_mul_inv, one_mul]

/-- Positive reciprocal-summable zeros plus pointwise product values suffice
for the complete indexed angular Master. -/
theorem profileMaster_of_summable_indexedProductValues
    {ι : Type*} {P : ℝ → ℝ → ℝ} {α : ι → ℝ} {c : ℝ → ℝ}
    (hα : ∀ i, 0 < α i) (hs : Summable (fun i => 1 / α i))
    (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hp : ∀ r, 0 < r → ∀ x ∈ angularInterval,
      Tendsto (fun s => c r * indexedFiniteProductProfile α r s x)
        atTop (𝓝 (P r x))) : ProfileMaster P := by
  apply profileMaster_of_indexedProductValues_and_pointwise hα hc
    (F := fun r z => (c r : ℂ) * complexIndexedAngularProduct (fun i => 1 / α i) r z)
    ?_ hp
  intro r hr
  have h := scaled_indexedComplexProfile_tendstoLocallyUniformlyOn
    (fun i => le_of_lt (one_div_pos.mpr (hα i))) hs hr.le (c r)
  simpa only [indexedComplexFiniteProductProfile_eq_reciprocal] using h

end AngularMaster
