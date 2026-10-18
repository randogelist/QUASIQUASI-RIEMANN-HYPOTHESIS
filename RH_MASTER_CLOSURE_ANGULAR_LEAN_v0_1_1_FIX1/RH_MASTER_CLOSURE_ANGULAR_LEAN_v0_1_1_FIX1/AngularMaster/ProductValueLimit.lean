import AngularMaster.ProductLimit
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Derivative convergence from complex angular product values

The certificate in this file asks only for locally uniform convergence of the
finite complex angular products and agreement of their limit with a real
profile on `[-1,1]`.  Holomorphic derivative convergence, including both real
angular endpoints, is proved rather than assumed.

This does not establish a Hadamard factorization for the actual theta function.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AngularMaster

/-- The finite angular product extended polynomially to a complex angular
coordinate.  Its restriction to the real axis is `finiteProductProfile`. -/
def complexFiniteProductProfile (α : ℕ → ℝ) (r : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range N,
    ((((1 - r / α i) ^ 2 : ℝ) : ℂ) + ((2 * r / α i : ℝ) : ℂ) * (z + 1))

theorem complexFiniteProductProfile_differentiable
    (α : ℕ → ℝ) (r : ℝ) (N : ℕ) :
    Differentiable ℂ (complexFiniteProductProfile α r N) := by
  unfold complexFiniteProductProfile
  fun_prop

theorem complexFiniteProductProfile_ofReal
    (α : ℕ → ℝ) (r : ℝ) (N : ℕ) (x : ℝ) :
    complexFiniteProductProfile α r N (x : ℂ) =
      (finiteProductProfile α r N x : ℂ) := by
  simp only [complexFiniteProductProfile, finiteProductProfile, genusZeroFactor,
    Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one]

/-- Value convergence alone: no derivative-convergence field is present. -/
def ProductProfileLimit (P : ℝ → ℝ → ℝ) : Prop :=
  ∃ α : ℕ → ℝ, ∃ c : ℝ → ℝ, ∃ F : ℝ → ℂ → ℂ,
    (∀ i, 0 < α i) ∧ (∀ r, 0 < r → 0 ≤ c r) ∧
    (∀ r, 0 < r →
      TendstoLocallyUniformlyOn
        (fun N z => (c r : ℂ) * complexFiniteProductProfile α r N z)
        (F r) atTop Set.univ) ∧
    (∀ r, 0 < r → ∀ x ∈ angularInterval, (F r (x : ℂ)).re = P r x)

theorem scaled_complexFiniteProductProfile_deriv_re
    (α : ℕ → ℝ) (c r : ℝ) (N : ℕ) (x : ℝ) :
    (deriv (fun z => (c : ℂ) * complexFiniteProductProfile α r N z) (x : ℂ)).re =
      c * finiteProductFlux α r N x := by
  have hcomplex : Differentiable ℂ
      (fun z => (c : ℂ) * complexFiniteProductProfile α r N z) :=
    (complexFiniteProductProfile_differentiable α r N).const_mul c
  have hreal := (hcomplex (x : ℂ)).hasDerivAt.real_of_complex
  have heq : (fun y : ℝ =>
      ((c : ℂ) * complexFiniteProductProfile α r N (y : ℂ)).re) =
      (fun y : ℝ => c * finiteProductProfile α r N y) := by
    funext y
    rw [complexFiniteProductProfile_ofReal]
    simp
  rw [heq] at hreal
  exact hreal.unique ((finiteProductProfile_hasDerivAt α r N x).const_mul c)

/-- Local uniform value convergence supplies the angular derivative limit,
including `x = -1` and `x = 1`. -/
theorem productDerivativeLimit_of_productProfileLimit
    {P : ℝ → ℝ → ℝ} (h : ProductProfileLimit P) : ProductDerivativeLimit P := by
  rcases h with ⟨α, c, F, hα, hc, hlim, hagree⟩
  refine ⟨α, c, hα, hc, ?_⟩
  intro r hr x hx
  have hpoly : ∀ᶠ N : ℕ in atTop,
      DifferentiableOn ℂ
        (fun z => (c r : ℂ) * complexFiniteProductProfile α r N z) Set.univ :=
    Eventually.of_forall (fun N =>
      ((complexFiniteProductProfile_differentiable α r N).const_mul (c r)).differentiableOn)
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
  change Tendsto (fun N =>
      (deriv (fun z => (c r : ℂ) * complexFiniteProductProfile α r N z) (x : ℂ)).re)
      atTop (𝓝 (deriv (F r) (x : ℂ)).re) at hdre
  simpa only [scaled_complexFiniteProductProfile_deriv_re, hid] using hdre

theorem profileMaster_of_productProfileLimit
    {P : ℝ → ℝ → ℝ} (h : ProductProfileLimit P) : ProfileMaster P :=
  profileMaster_of_productDerivativeLimit (productDerivativeLimit_of_productProfileLimit h)

end AngularMaster
