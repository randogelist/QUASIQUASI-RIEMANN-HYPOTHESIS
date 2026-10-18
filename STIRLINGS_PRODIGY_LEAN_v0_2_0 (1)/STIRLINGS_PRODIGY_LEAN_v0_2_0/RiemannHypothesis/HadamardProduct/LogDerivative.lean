/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import RiemannHypothesis.HadamardProduct.InfiniteProducts

/-!
# HadamardProduct.LogDerivative

Locally-uniform convergence of the genus-one Hadamard product and the resulting
log-derivative-of-limit identity: on the open region where finite truncations converge
locally uniformly, the infinite product is holomorphic and its logarithmic derivative is
the regularized zero-sum series `Σ (1/(s-ρ) + 1/ρ)`.

The genuinely hard analytic content (locally-uniform convergence on the AFZ region) is
isolated in the `…LimitData` hypotheses; the theorems here transport it through Mathlib's
Weierstrass derivative theorem (`TendstoLocallyUniformlyOn.deriv`) to the log-derivative
formula. Identity content only.

## Main declarations

* `HadamardLogDerivLimitData` — analytic-legitimacy data on an arbitrary region.
* `HadamardFiniteExhaustion`, `HadamardFiniteDerivativeLimitData`,
  `HadamardProductLocallyUniformLimitData` — finite-truncation convergence interfaces.
* `HadamardFiniteDerivativeLimitData.logDeriv_eq_tsum_at` — the LUC log-derivative
  interchange (`Λ[P] = Σ`).
-/

namespace OverflowResidueRH

open Filter Topology

/-- 📦 **`HadamardLogDerivLimitData`** — the log-derivative-of-limit
content, packaged on an arbitrary `region : Set ℂ`. The genuine analytic
theorem (log-deriv interchanges with locally uniform convergence)
inhabits this bundle on the AFZ region of `ξ`. -/
structure HadamardLogDerivLimitData
    {ι : Type*} (zeroLoc : ι → ℂ) : Type where
  region : Set ℂ
  product_differentiable_at :
    ∀ s ∈ region,
      DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s
  regularized_summable_at :
    ∀ s ∈ region,
      Summable fun i : ι => 1 / (s - zeroLoc i) + 1 / zeroLoc i
  logDeriv_eq_tsum_at :
    ∀ s ∈ region,
      logDerivativeResponse (infiniteHadamardProduct zeroLoc) s
        = hadamardRegularizedLogDerivSeries zeroLoc s

/-- 📦 **`HadamardFiniteExhaustion`** — finite-truncation convergence
interface for the genus-1 Hadamard product. -/
structure HadamardFiniteExhaustion
    {ι : Type*} (zeroLoc : ι → ℂ) where
  exhaust : ℕ → Finset ι
  exhaust_mono :
    ∀ {n m : ℕ}, n ≤ m → exhaust n ⊆ exhaust m
  product_tendsto :
    ∀ s : ℂ,
      Tendsto
        (fun n => indexedFiniteHadamardProduct zeroLoc (exhaust n) s)
        Filter.atTop
        (𝓝 (infiniteHadamardProduct zeroLoc s))
  regularized_sum_tendsto :
    ∀ s : ℂ,
      Tendsto
        (fun n => finiteHadamardRegularizedSum zeroLoc (exhaust n) s)
        Filter.atTop
        (𝓝 (hadamardRegularizedLogDerivSeries zeroLoc s))

/-- ⭐ **PROVED — finite-truncation log-derivative identity at every
exhaustion stage.** -/
theorem logDerivativeResponse_indexedFiniteHadamardProduct_at_exhaustion
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hex : HadamardFiniteExhaustion zeroLoc)
    {s : ℂ} {n : ℕ}
    (hρ : ∀ i ∈ Hex.exhaust n, zeroLoc i ≠ 0)
    (hs : ∀ i ∈ Hex.exhaust n, s ≠ zeroLoc i) :
    logDerivativeResponse
        (fun s' : ℂ => indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s') s
      = finiteHadamardRegularizedSum zeroLoc (Hex.exhaust n) s :=
  logDerivativeResponse_indexedFiniteHadamardProduct hρ hs

/-- ⭐ **PROVED — finite-truncation derivative identity at every
exhaustion stage.** -/
theorem deriv_indexedFiniteHadamardProduct_at_exhaustion
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hex : HadamardFiniteExhaustion zeroLoc)
    {s : ℂ} {n : ℕ}
    (hρ : ∀ i ∈ Hex.exhaust n, zeroLoc i ≠ 0)
    (hs : ∀ i ∈ Hex.exhaust n, s ≠ zeroLoc i) :
    deriv
        (fun s' : ℂ =>
          indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s') s
      =
    indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s
      * finiteHadamardRegularizedSum zeroLoc (Hex.exhaust n) s :=
  deriv_indexedFiniteHadamardProduct hρ hs

/-- ⭐ **PROVED — indexed finite Hadamard products are differentiable
everywhere.** The finite holomorphicity input for Mathlib's
locally-uniform derivative theorem. -/
theorem indexedFiniteHadamardProduct_differentiableAt
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) (s : ℂ) :
    DifferentiableAt ℂ (fun s' : ℂ =>
      indexedFiniteHadamardProduct zeroLoc F s') s := by
  unfold indexedFiniteHadamardProduct
  exact DifferentiableAt.fun_finsetProd (fun i _hi =>
    hadamardGenus1Factor_differentiableAt (zeroLoc i) s)

/-- ⭐ **PROVED — indexed finite Hadamard products are differentiable on
every region.** -/
theorem indexedFiniteHadamardProduct_differentiableOn
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) (U : Set ℂ) :
    DifferentiableOn ℂ
      (fun s' : ℂ => indexedFiniteHadamardProduct zeroLoc F s') U := by
  intro s _hs
  exact (indexedFiniteHadamardProduct_differentiableAt zeroLoc F s).differentiableWithinAt

/-- 📦 **`HadamardFiniteDerivativeLimitData`** — the hard derivative
passage in finite-exhaustion coordinates: finite genus-one product
derivatives tend to the derivative of the infinite Hadamard product on
the target region. -/
structure HadamardFiniteDerivativeLimitData
    {ι : Type*} (zeroLoc : ι → ℂ)
    (Hex : HadamardFiniteExhaustion zeroLoc) : Type where
  region : Set ℂ
  derivative_tendsto :
    ∀ s ∈ region,
      Tendsto
        (fun n : ℕ =>
          deriv
            (fun s' : ℂ =>
              indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s') s)
        Filter.atTop
        (𝓝 (deriv (infiniteHadamardProduct zeroLoc) s))

/-- 📦 **`HadamardProductLocallyUniformLimitData`** — the genuine
Weierstrass-style locally-uniform product convergence input on an open
region. -/
structure HadamardProductLocallyUniformLimitData
    {ι : Type*} (zeroLoc : ι → ℂ)
    (Hex : HadamardFiniteExhaustion zeroLoc) : Type where
  region : Set ℂ
  isOpen_region : IsOpen region
  locally_uniform_product :
    TendstoLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      region

/-- 🌟🌟🌟🌟 **PROVED — locally-uniform product convergence gives the
finite-derivative limit data.** Mathlib's `TendstoLocallyUniformlyOn.deriv`
converts locally-uniform convergence of (holomorphic) finite products into
locally-uniform convergence of derivatives. -/
noncomputable def HadamardFiniteDerivativeLimitData.of_locallyUniformProduct
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hluc : HadamardProductLocallyUniformLimitData zeroLoc Hex) :
    HadamardFiniteDerivativeLimitData zeroLoc Hex := by
  let F : ℕ → ℂ → ℂ := fun n s =>
    indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s
  have hfinite_diff :
      ∀ᶠ n : ℕ in Filter.atTop,
        DifferentiableOn ℂ (F n) Hluc.region := by
    filter_upwards [] with n
    exact indexedFiniteHadamardProduct_differentiableOn
      zeroLoc (Hex.exhaust n) Hluc.region
  have hderiv_luc :
      TendstoLocallyUniformlyOn
        (deriv ∘ F)
        (deriv (infiniteHadamardProduct zeroLoc))
        Filter.atTop
        Hluc.region :=
    Hluc.locally_uniform_product.deriv hfinite_diff Hluc.isOpen_region
  refine
    { region := Hluc.region
      derivative_tendsto := ?_ }
  intro s hs
  simpa [F, Function.comp_def] using hderiv_luc.tendsto_at hs

/-- 🌟🌟🌟 **PROVED — the locally-uniform Hadamard product limit is
differentiable on its open region.** -/
theorem HadamardProductLocallyUniformLimitData.infinite_differentiableOn
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hluc : HadamardProductLocallyUniformLimitData zeroLoc Hex) :
    DifferentiableOn ℂ
      (infiniteHadamardProduct zeroLoc) Hluc.region := by
  let F : ℕ → ℂ → ℂ := fun n s =>
    indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s
  have hfinite_diff :
      ∀ᶠ n : ℕ in Filter.atTop,
        DifferentiableOn ℂ (F n) Hluc.region := by
    filter_upwards [] with n
    exact indexedFiniteHadamardProduct_differentiableOn
      zeroLoc (Hex.exhaust n) Hluc.region
  simpa [F] using
    Hluc.locally_uniform_product.differentiableOn
      hfinite_diff Hluc.isOpen_region

/-- 🌟🌟🌟 **PROVED — pointwise differentiability from locally-uniform
Hadamard product convergence on an open region.** -/
theorem HadamardProductLocallyUniformLimitData.infinite_differentiableAt
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hluc : HadamardProductLocallyUniformLimitData zeroLoc Hex)
    {s : ℂ} (hs : s ∈ Hluc.region) :
    DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s :=
  Hluc.infinite_differentiableOn.differentiableAt
    (Hluc.isOpen_region.mem_nhds hs)

/-- 🌟🌟🌟🌟 **PROVED — derivative-limit passage gives the infinite
Hadamard log-derivative formula.** If finite product derivatives converge
to the derivative of the infinite product, the finite identity
`P_F' = P_F · Σ_F` passes to the limit and yields `Λ[P] = Σ`. -/
theorem HadamardFiniteDerivativeLimitData.logDeriv_eq_tsum_at
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hderiv : HadamardFiniteDerivativeLimitData zeroLoc Hex)
    {s : ℂ}
    (hs_region : s ∈ Hderiv.region)
    (hzero_ne : ∀ i : ι, zeroLoc i ≠ 0)
    (hs_ne : ∀ i : ι, s ≠ zeroLoc i)
    (hprod_ne : infiniteHadamardProduct zeroLoc s ≠ 0) :
    logDerivativeResponse (infiniteHadamardProduct zeroLoc) s
      = hadamardRegularizedLogDerivSeries zeroLoc s := by
  have hderiv_lim := Hderiv.derivative_tendsto s hs_region
  have hprod_lim := Hex.product_tendsto s
  have hsum_lim := Hex.regularized_sum_tendsto s
  have hmul_lim :
      Tendsto
        (fun n : ℕ =>
          indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s
            * finiteHadamardRegularizedSum zeroLoc (Hex.exhaust n) s)
        Filter.atTop
        (𝓝 (infiniteHadamardProduct zeroLoc s
          * hadamardRegularizedLogDerivSeries zeroLoc s)) :=
    hprod_lim.mul hsum_lim
  have hderiv_eq_mul :
      (fun n : ℕ =>
          deriv
            (fun s' : ℂ =>
              indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s') s)
        =ᶠ[Filter.atTop]
      (fun n : ℕ =>
          indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s
            * finiteHadamardRegularizedSum zeroLoc (Hex.exhaust n) s) := by
    filter_upwards [] with n
    exact deriv_indexedFiniteHadamardProduct_at_exhaustion
      Hex
      (fun i _hi => hzero_ne i)
      (fun i _hi => hs_ne i)
  have hderiv_mul_lim :
      Tendsto
        (fun n : ℕ =>
          deriv
            (fun s' : ℂ =>
              indexedFiniteHadamardProduct zeroLoc (Hex.exhaust n) s') s)
        Filter.atTop
        (𝓝 (infiniteHadamardProduct zeroLoc s
          * hadamardRegularizedLogDerivSeries zeroLoc s)) :=
    hmul_lim.congr' hderiv_eq_mul.symm
  have hderiv_eq :
      deriv (infiniteHadamardProduct zeroLoc) s
        =
      infiniteHadamardProduct zeroLoc s
        * hadamardRegularizedLogDerivSeries zeroLoc s :=
    tendsto_nhds_unique hderiv_lim hderiv_mul_lim
  unfold logDerivativeResponse
  rw [hderiv_eq]
  field_simp [hprod_ne]

/-! ## Inverse-square zero distribution: summability and multipliability

The classical genus-one hypothesis `Σ 1/‖ρ‖² < ∞` (with the zeros eventually large relative
to any probe) makes the regularized term series summable and the genus-one product
multipliable, supplying the convergence inputs the LUC data above consumes. -/

/-- ⭐ **PROVED — paired/regularized identity.** `1/(s-ρ) + 1/ρ = s/((s-ρ)·ρ)`. -/
lemma hadamard_regularized_term_eq {s ρ : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    1 / (s - ρ) + 1 / ρ = s / ((s - ρ) * ρ) := by
  have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
  field_simp
  ring

/-- ⭐ **PROVED — norm form of the regularized identity.** -/
lemma norm_hadamard_regularized_term_eq
    {s ρ : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    ‖1 / (s - ρ) + 1 / ρ‖ = ‖s‖ / (‖s - ρ‖ * ‖ρ‖) := by
  rw [hadamard_regularized_term_eq hρ hsρ, norm_div, norm_mul]

/-- ⭐ **PROVED — reverse-triangle large-zero bound.** When `2‖s‖ ≤ ‖ρ‖`,
`‖s − ρ‖ ≥ ‖ρ‖/2`. -/
lemma norm_sub_ge_half_of_two_norm_le {s ρ : ℂ}
    (hlarge : 2 * ‖s‖ ≤ ‖ρ‖) :
    ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
  have htriangle : ‖ρ‖ ≤ ‖s‖ + ‖s - ρ‖ := by
    have h_sub := norm_sub_le s (s - ρ)
    have h_eq : s - (s - ρ) = ρ := by ring
    rw [h_eq] at h_sub
    exact h_sub
  linarith

/-- 🌟🌟🌟 **PROVED — large-zero bound on the regularized Hadamard term.**
`‖1/(s−ρ) + 1/ρ‖ ≤ 2‖s‖/‖ρ‖²` for `‖ρ‖ ≥ 2‖s‖`. -/
lemma norm_hadamard_regularized_term_le_large {s ρ : ℂ}
    (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) (hlarge : 2 * ‖s‖ ≤ ‖ρ‖) :
    ‖1 / (s - ρ) + 1 / ρ‖ ≤ 2 * ‖s‖ / ‖ρ‖ ^ 2 := by
  rw [norm_hadamard_regularized_term_eq hρ hsρ]
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have h_sρ_pos : 0 < ‖s - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsρ)
  have h_denom_pos : 0 < ‖s - ρ‖ * ‖ρ‖ := mul_pos h_sρ_pos hρ_pos
  have h_ρ_sq_pos : 0 < ‖ρ‖ ^ 2 := by positivity
  have h_sρ_ge : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := norm_sub_ge_half_of_two_norm_le hlarge
  have h_s_nn : 0 ≤ ‖s‖ := norm_nonneg _
  rw [div_le_div_iff₀ h_denom_pos h_ρ_sq_pos]
  have h_ρ_le : ‖ρ‖ ≤ 2 * ‖s - ρ‖ := by linarith
  have h_mul : ‖ρ‖ * ‖ρ‖ ≤ 2 * ‖s - ρ‖ * ‖ρ‖ :=
    mul_le_mul_of_nonneg_right h_ρ_le hρ_pos.le
  have h_ρ_sq : ‖ρ‖ ^ 2 = ‖ρ‖ * ‖ρ‖ := by ring
  nlinarith [h_mul, h_s_nn, h_ρ_sq]

/-- 📦 **`HadamardZeroInvSqSummability`** — the classical analytic
hypothesis on a zero set: `Σ 1/‖ρ‖² < ∞` (genus ≤ 1) and for every `s`,
eventually `‖ρ‖ ≥ 2‖s‖`. -/
structure HadamardZeroInvSqSummability
    {ι : Type*} (zeroLoc : ι → ℂ) : Prop where
  zero_ne : ∀ i, zeroLoc i ≠ 0
  inv_sq_summable :
    Summable fun i : ι => (‖zeroLoc i‖ ^ 2)⁻¹
  eventually_large :
    ∀ s : ℂ, ∀ᶠ i in Filter.cofinite, 2 * ‖s‖ ≤ ‖zeroLoc i‖

/-- 📦 **`HadamardZeroNormProper`** — classical local finiteness of the
zero locations: every closed norm disk contains only finitely many zeros. -/
structure HadamardZeroNormProper
    {ι : Type*} (zeroLoc : ι → ℂ) : Prop where
  finite_norm_le :
    ∀ R : ℝ, { i : ι | ‖zeroLoc i‖ ≤ R }.Finite

/-- 🌟🌟 **PROVED — norm-proper zero locations are eventually large in the
cofinite filter.** -/
theorem HadamardZeroNormProper.eventually_large
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) :
    ∀ s : ℂ, ∀ᶠ i in Filter.cofinite, 2 * ‖s‖ ≤ ‖zeroLoc i‖ := by
  intro s
  rw [Filter.eventually_cofinite]
  exact (H.finite_norm_le (2 * ‖s‖)).subset (by
    intro i hi
    exact (not_le.mp hi).le)

/-- **Norm-ball finite exhaustion** attached to a norm-proper zero system.
Stage `n` contains all indices with `‖ρᵢ‖ ≤ n`. -/
noncomputable def HadamardZeroNormProper.normExhaustion
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) : ℕ → Finset ι :=
  fun n => (H.finite_norm_le (n : ℝ)).toFinset

/-- ⭐ **PROVED — membership in the norm-ball exhaustion.** -/
theorem HadamardZeroNormProper.mem_normExhaustion
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc)
    {n : ℕ} {i : ι} :
    i ∈ H.normExhaustion n ↔ ‖zeroLoc i‖ ≤ (n : ℝ) := by
  unfold HadamardZeroNormProper.normExhaustion
  rw [Set.Finite.mem_toFinset]
  rfl

/-- 🌟🌟 **PROVED — norm-ball finite exhaustion is monotone.** -/
theorem HadamardZeroNormProper.normExhaustion_mono
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) :
    Monotone H.normExhaustion := by
  intro n m hnm i hi
  rw [H.mem_normExhaustion] at hi
  rw [H.mem_normExhaustion]
  exact le_trans hi (Nat.cast_le.mpr hnm)

/-- 🌟🌟 **PROVED — norm-ball finite exhaustion is exhaustive.** -/
theorem HadamardZeroNormProper.normExhaustion_exhaustive
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) :
    ∀ i : ι, ∃ n : ℕ, i ∈ H.normExhaustion n := by
  intro i
  obtain ⟨n, hn⟩ := exists_nat_ge ‖zeroLoc i‖
  exact ⟨n, (H.mem_normExhaustion).mpr hn⟩

/-- 🌟🌟 **PROVED — build inverse-square Hadamard zero data from
summability plus local finiteness.** -/
theorem HadamardZeroInvSqSummability.of_invSqSummable_normProper
    {ι : Type*} {zeroLoc : ι → ℂ}
    (hzero : ∀ i, zeroLoc i ≠ 0)
    (hinv : Summable fun i : ι => (‖zeroLoc i‖ ^ 2)⁻¹)
    (Hproper : HadamardZeroNormProper zeroLoc) :
    HadamardZeroInvSqSummability zeroLoc :=
  { zero_ne := hzero
    inv_sq_summable := hinv
    eventually_large := Hproper.eventually_large }

/-- 🌟🌟🌟 **PROVED — regularized series is summable from inv-sq
summability + eventually-large.** -/
theorem summable_hadamard_regularized_terms_of_inv_sq
    {ι : Type*} {zeroLoc : ι → ℂ} {s : ℂ}
    (hzero_ne : ∀ i, zeroLoc i ≠ 0)
    (hs_ne : ∀ i, s ≠ zeroLoc i)
    (hinv_sq : Summable fun i : ι => (‖zeroLoc i‖ ^ 2)⁻¹)
    (heventual_large :
      ∀ᶠ i in Filter.cofinite, 2 * ‖s‖ ≤ ‖zeroLoc i‖) :
    Summable fun i : ι => 1 / (s - zeroLoc i) + 1 / zeroLoc i := by
  apply Summable.of_norm_bounded_eventually
    (g := fun i => 2 * ‖s‖ * (‖zeroLoc i‖ ^ 2)⁻¹)
  · exact hinv_sq.mul_left (2 * ‖s‖)
  · filter_upwards [heventual_large] with i hi
    have h_bound :=
      norm_hadamard_regularized_term_le_large (hzero_ne i) (hs_ne i) hi
    have h_eq :
        (2 : ℝ) * ‖s‖ / ‖zeroLoc i‖ ^ 2
          = 2 * ‖s‖ * (‖zeroLoc i‖ ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
    linarith [h_eq ▸ h_bound]

/-- ⭐ **PROVED — regularized summability from `HadamardZeroInvSqSummability`.** -/
theorem HadamardZeroInvSqSummability.summable_regularized
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {s : ℂ} (hs_ne : ∀ i, s ≠ zeroLoc i) :
    Summable fun i : ι => 1 / (s - zeroLoc i) + 1 / zeroLoc i :=
  summable_hadamard_regularized_terms_of_inv_sq
    H.zero_ne hs_ne H.inv_sq_summable (H.eventually_large s)

/-- 🌟🌟🌟 **PROVED — totalized regularized series is summable at every
point.** Collisions can occur only among the finitely many non-large
zeros; once `2‖s‖ ≤ ‖ρᵢ‖`, `s = ρᵢ` would force `ρᵢ = 0`, contradicting
`zero_ne`. -/
theorem HadamardZeroInvSqSummability.summable_regularized_totalized
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    (s : ℂ) :
    Summable fun i : ι => 1 / (s - zeroLoc i) + 1 / zeroLoc i := by
  apply Summable.of_norm_bounded_eventually
    (g := fun i => 2 * ‖s‖ * (‖zeroLoc i‖ ^ 2)⁻¹)
  · exact H.inv_sq_summable.mul_left (2 * ‖s‖)
  · filter_upwards [H.eventually_large s] with i hi
    have hs_ne : s ≠ zeroLoc i := by
      intro h
      have hnorm_zero : ‖s‖ = 0 := by
        rw [← h] at hi
        have hs_nonneg : 0 ≤ ‖s‖ := norm_nonneg s
        linarith
      have hs0 : s = 0 := norm_eq_zero.mp hnorm_zero
      exact H.zero_ne i (by rw [← h, hs0])
    have h_bound :=
      norm_hadamard_regularized_term_le_large (H.zero_ne i) hs_ne hi
    have h_eq :
        (2 : ℝ) * ‖s‖ / ‖zeroLoc i‖ ^ 2
          = 2 * ‖s‖ * (‖zeroLoc i‖ ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
    linarith [h_eq ▸ h_bound]

/-- 🌟🌟🌟🌟 **PROVED — build Hadamard log-derivative limit data from
finite derivative convergence.** Inverse-square distribution supplies
summability; no-collision supplies the AFZ denominator guards; finite
derivative convergence supplies the log-derivative/`tsum` identity. -/
noncomputable def HadamardLogDerivLimitData.of_finiteDerivativeLimitData
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hderiv : HadamardFiniteDerivativeLimitData zeroLoc Hex)
    (Hdiff :
      ∀ s ∈ Hderiv.region,
        DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s)
    (Hno_collision :
      ∀ s ∈ Hderiv.region, ∀ i : ι, s ≠ zeroLoc i)
    (Hprod_ne :
      ∀ s ∈ Hderiv.region,
        infiniteHadamardProduct zeroLoc s ≠ 0) :
    HadamardLogDerivLimitData zeroLoc :=
  { region := Hderiv.region
    product_differentiable_at := Hdiff
    regularized_summable_at := by
      intro s hs
      exact Hinv.summable_regularized (Hno_collision s hs)
    logDeriv_eq_tsum_at := by
      intro s hs
      exact
        HadamardFiniteDerivativeLimitData.logDeriv_eq_tsum_at
          Hderiv
          hs
          Hinv.zero_ne
          (Hno_collision s hs)
          (Hprod_ne s hs) }

/-- 📦 **`GenusOneTaylorBoundData`** — quantitative form of
`1 - (1-w)·exp(w) = O(w²)`. `C = 4` is unsharp but suffices. -/
structure GenusOneTaylorBoundData : Prop where
  bound :
    ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖1 - (1 - w) * Complex.exp w‖ ≤ 4 * ‖w‖ ^ 2

/-- 🌟🌟🌟 **PROVED — specialization to `hadamardGenus1Factor` with
`‖s‖ ≤ ‖ρ‖`.** -/
lemma norm_one_sub_hadamardGenus1Factor_le_large
    {ρ s : ℂ} (hρ : ρ ≠ 0) (hlarge : ‖s‖ ≤ ‖ρ‖)
    (Hbound : GenusOneTaylorBoundData) :
    ‖1 - hadamardGenus1Factor ρ s‖ ≤ 4 * (‖s‖ ^ 2 / ‖ρ‖ ^ 2) := by
  unfold hadamardGenus1Factor
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hw : ‖s / ρ‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hlarge (norm_nonneg _)
  have h := Hbound.bound (s / ρ) hw
  rw [norm_div, div_pow] at h
  exact h

/-- 🌟🌟🌟 **PROVED — norm-summability of `1 - E₁(s/ρᵢ)`.** -/
theorem summable_norm_one_sub_hadamardGenus1Factor_of_inv_sq
    {ι : Type*} {zeroLoc : ι → ℂ} {s : ℂ}
    (Hbound : GenusOneTaylorBoundData)
    (hzero_ne : ∀ i, zeroLoc i ≠ 0)
    (hinv_sq : Summable fun i : ι => (‖zeroLoc i‖ ^ 2)⁻¹)
    (heventual_large :
      ∀ᶠ i in Filter.cofinite, ‖s‖ ≤ ‖zeroLoc i‖) :
    Summable fun i : ι => ‖1 - hadamardGenus1Factor (zeroLoc i) s‖ := by
  apply Summable.of_norm_bounded_eventually
    (g := fun i => 4 * ‖s‖ ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹)
  · exact hinv_sq.mul_left (4 * ‖s‖ ^ 2)
  · filter_upwards [heventual_large] with i hi
    have h_bound :=
      norm_one_sub_hadamardGenus1Factor_le_large (hzero_ne i) hi Hbound
    have h_eq : (4 : ℝ) * ‖s‖ ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹
              = 4 * (‖s‖ ^ 2 / ‖zeroLoc i‖ ^ 2) := by
      rw [div_eq_mul_inv]; ring
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    linarith [h_eq ▸ h_bound]

/-- 🌟🌟🌟 **PROVED — ℂ-valued `Summable (1 - E₁(s/ρᵢ))` from norm.** -/
theorem summable_one_sub_hadamardGenus1Factor_of_inv_sq
    {ι : Type*} {zeroLoc : ι → ℂ} {s : ℂ}
    (Hbound : GenusOneTaylorBoundData)
    (hzero_ne : ∀ i, zeroLoc i ≠ 0)
    (hinv_sq : Summable fun i : ι => (‖zeroLoc i‖ ^ 2)⁻¹)
    (heventual_large :
      ∀ᶠ i in Filter.cofinite, ‖s‖ ≤ ‖zeroLoc i‖) :
    Summable fun i : ι => 1 - hadamardGenus1Factor (zeroLoc i) s :=
  Summable.of_norm
    (summable_norm_one_sub_hadamardGenus1Factor_of_inv_sq
      Hbound hzero_ne hinv_sq heventual_large)

/-- 🌟🌟🌟 **PROVED — `Multipliable (hadamardGenus1Factor ∘ zeroLoc)`
from inverse-square zero summability + Taylor bound.** Uses Mathlib's
`Complex.multipliable_one_add_of_summable`. -/
theorem multipliable_hadamardGenus1Factor_of_inv_sq
    {ι : Type*} {zeroLoc : ι → ℂ} {s : ℂ}
    (Hbound : GenusOneTaylorBoundData)
    (hzero_ne : ∀ i, zeroLoc i ≠ 0)
    (hinv_sq : Summable fun i : ι => (‖zeroLoc i‖ ^ 2)⁻¹)
    (heventual_large :
      ∀ᶠ i in Filter.cofinite, ‖s‖ ≤ ‖zeroLoc i‖) :
    Multipliable fun i : ι => hadamardGenus1Factor (zeroLoc i) s := by
  have h_sum :=
    summable_one_sub_hadamardGenus1Factor_of_inv_sq
      Hbound hzero_ne hinv_sq heventual_large
  have h_sum_neg :
      Summable fun i : ι => hadamardGenus1Factor (zeroLoc i) s - 1 := by
    have := h_sum.neg
    simpa [neg_sub] using this
  have h_mul := Complex.multipliable_one_add_of_summable h_sum_neg
  simpa using h_mul

/-- ⭐ **PROVED — `Multipliable` from the `HadamardZeroInvSqSummability`
bundle + Taylor bound.** -/
theorem HadamardZeroInvSqSummability.multipliable_genus1
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    (Hbound : GenusOneTaylorBoundData) (s : ℂ) :
    Multipliable fun i : ι => hadamardGenus1Factor (zeroLoc i) s := by
  apply multipliable_hadamardGenus1Factor_of_inv_sq
    Hbound H.zero_ne H.inv_sq_summable
  filter_upwards [H.eventually_large s] with i hi
  have h_s_nn : 0 ≤ ‖s‖ := norm_nonneg s
  linarith

/-- 🌟🌟🌟🌟 **PROVED — `GenusOneTaylorBoundData` inhabited.**
`1 - (1-w)·exp(w) = -(exp(w)-1-w) + w·(exp(w)-1)`; the triangle inequality
plus Mathlib's two exponential bounds give `‖·‖ ≤ 3‖w‖² ≤ 4‖w‖²`. -/
theorem genusOneTaylorBoundData : GenusOneTaylorBoundData := by
  refine ⟨?_⟩
  intro w hw
  have h_decomp :
      (1 : ℂ) - (1 - w) * Complex.exp w
        = -(Complex.exp w - 1 - w) + w * (Complex.exp w - 1) := by
    ring
  rw [h_decomp]
  have h_exp_sub_1_sub_id := Complex.norm_exp_sub_one_sub_id_le hw
  have h_exp_sub_1 := Complex.norm_exp_sub_one_le hw
  have h_w_nn : 0 ≤ ‖w‖ := norm_nonneg _
  calc ‖-(Complex.exp w - 1 - w) + w * (Complex.exp w - 1)‖
      ≤ ‖-(Complex.exp w - 1 - w)‖ + ‖w * (Complex.exp w - 1)‖ :=
        norm_add_le _ _
    _ = ‖Complex.exp w - 1 - w‖ + ‖w‖ * ‖Complex.exp w - 1‖ := by
        rw [norm_neg, norm_mul]
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
        gcongr
    _ = 3 * ‖w‖ ^ 2 := by ring
    _ ≤ 4 * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]

/-- 🌟🌟🌟 **PROVED — `Multipliable` from `HadamardZeroInvSqSummability`
alone** (no Taylor hypothesis). -/
theorem HadamardZeroInvSqSummability.product_multipliable
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc) :
    ∀ s : ℂ,
      Multipliable fun i : ι => hadamardGenus1Factor (zeroLoc i) s :=
  fun s => H.multipliable_genus1 genusOneTaylorBoundData s

/-- 🌟🌟🌟 **PROVED — finite Hadamard products converge to the `tprod`.** -/
theorem HadamardZeroInvSqSummability.indexedFiniteProduct_tendsto
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc) (s : ℂ) :
    Tendsto
      (fun F : Finset ι => indexedFiniteHadamardProduct zeroLoc F s)
      Filter.atTop
      (𝓝 (infiniteHadamardProduct zeroLoc s)) := by
  unfold indexedFiniteHadamardProduct infiniteHadamardProduct
  exact (H.product_multipliable s).hasProd

/-- 🌟🌟🌟 **PROVED — finite regularized sums converge to the `tsum`
away from the indexed zeros.** -/
theorem HadamardZeroInvSqSummability.finiteRegularizedSum_tendsto
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {s : ℂ} (hs_ne : ∀ i : ι, s ≠ zeroLoc i) :
    Tendsto
      (fun F : Finset ι => finiteHadamardRegularizedSum zeroLoc F s)
      Filter.atTop
      (𝓝 (hadamardRegularizedLogDerivSeries zeroLoc s)) := by
  unfold finiteHadamardRegularizedSum hadamardRegularizedLogDerivSeries
  exact (H.summable_regularized hs_ne).hasSum

/-- 🌟🌟🌟 **PROVED — finite regularized sums converge to the `tsum`
for the totalized expression at every point.** -/
theorem HadamardZeroInvSqSummability.finiteRegularizedSum_tendsto_totalized
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    (s : ℂ) :
    Tendsto
      (fun F : Finset ι => finiteHadamardRegularizedSum zeroLoc F s)
      Filter.atTop
      (𝓝 (hadamardRegularizedLogDerivSeries zeroLoc s)) := by
  unfold finiteHadamardRegularizedSum hadamardRegularizedLogDerivSeries
  exact (H.summable_regularized_totalized s).hasSum

/-- 🌟🌟🌟 **PROVED — monotone finite exhaustions inherit Hadamard product
convergence.** -/
theorem HadamardZeroInvSqSummability.indexedFiniteProduct_tendsto_at_exhaustion
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {exhaust : ℕ → Finset ι}
    (hmono : Monotone exhaust)
    (hexhaustive : ∀ i : ι, ∃ n : ℕ, i ∈ exhaust n)
    (s : ℂ) :
    Tendsto
      (fun n : ℕ => indexedFiniteHadamardProduct zeroLoc (exhaust n) s)
      Filter.atTop
      (𝓝 (infiniteHadamardProduct zeroLoc s)) :=
  (H.indexedFiniteProduct_tendsto s).comp
    (tendsto_atTop_finset_of_monotone hmono hexhaustive)

/-- 🌟🌟🌟 **PROVED — monotone finite exhaustions inherit regularized-sum
convergence away from indexed zeros.** -/
theorem HadamardZeroInvSqSummability.finiteRegularizedSum_tendsto_at_exhaustion
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {exhaust : ℕ → Finset ι}
    (hmono : Monotone exhaust)
    (hexhaustive : ∀ i : ι, ∃ n : ℕ, i ∈ exhaust n)
    {s : ℂ} (hs_ne : ∀ i : ι, s ≠ zeroLoc i) :
    Tendsto
      (fun n : ℕ => finiteHadamardRegularizedSum zeroLoc (exhaust n) s)
      Filter.atTop
      (𝓝 (hadamardRegularizedLogDerivSeries zeroLoc s)) :=
  (H.finiteRegularizedSum_tendsto hs_ne).comp
    (tendsto_atTop_finset_of_monotone hmono hexhaustive)

/-- 🌟🌟🌟 **PROVED — monotone finite exhaustions inherit totalized
regularized-sum convergence at every point.** -/
theorem HadamardZeroInvSqSummability.finiteRegularizedSum_tendsto_at_exhaustion_totalized
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {exhaust : ℕ → Finset ι}
    (hmono : Monotone exhaust)
    (hexhaustive : ∀ i : ι, ∃ n : ℕ, i ∈ exhaust n)
    (s : ℂ) :
    Tendsto
      (fun n : ℕ => finiteHadamardRegularizedSum zeroLoc (exhaust n) s)
      Filter.atTop
      (𝓝 (hadamardRegularizedLogDerivSeries zeroLoc s)) :=
  (H.finiteRegularizedSum_tendsto_totalized s).comp
    (tendsto_atTop_finset_of_monotone hmono hexhaustive)

/-- 🌟🌟🌟🌟 **PROVED — build the finite-exhaustion convergence interface
from inverse-square zero distribution and a monotone exhaustive sequence.** -/
noncomputable def HadamardFiniteExhaustion.of_invSq_mono_exhaustive
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    (exhaust : ℕ → Finset ι)
    (hmono : Monotone exhaust)
    (hexhaustive : ∀ i : ι, ∃ n : ℕ, i ∈ exhaust n) :
    HadamardFiniteExhaustion zeroLoc :=
  { exhaust := exhaust
    exhaust_mono := by
      intro n m hnm
      exact hmono hnm
    product_tendsto := by
      intro s
      exact H.indexedFiniteProduct_tendsto_at_exhaustion
        hmono hexhaustive s
    regularized_sum_tendsto := by
      intro s
      exact H.finiteRegularizedSum_tendsto_at_exhaustion_totalized
        hmono hexhaustive s }

/-- 🌟🌟🌟🌟 **PROVED — locally uniform convergence of the genus-one
Hadamard product from a summable uniform deviation bound.** Mathlib's
Weierstrass product theorem applied to `E₁(s/ρᵢ) = 1 + (E₁(s/ρᵢ)-1)`. -/
theorem hasProdLocallyUniformlyOn_hadamardGenus1Factor_of_summable_bound
    {ι : Type*} {zeroLoc : ι → ℂ} {U : Set ℂ} {u : ι → ℝ}
    (hU : IsOpen U)
    (hu : Summable u)
    (hbound :
      ∀ᶠ i in Filter.cofinite,
        ∀ s ∈ U,
          ‖hadamardGenus1Factor (zeroLoc i) s - 1‖ ≤ u i) :
    HasProdLocallyUniformlyOn
      (fun i : ι => fun s : ℂ => hadamardGenus1Factor (zeroLoc i) s)
      (fun s : ℂ => infiniteHadamardProduct zeroLoc s)
      U := by
  have hcts :
      ∀ i : ι,
        ContinuousOn
          (fun s : ℂ => hadamardGenus1Factor (zeroLoc i) s - 1) U := by
    intro i s _hs
    exact
      ((hadamardGenus1Factor_differentiableAt (zeroLoc i) s).continuousAt.sub
        continuousAt_const).continuousWithinAt
  have hprod :=
    hu.hasProdLocallyUniformlyOn_one_add
      (K := U)
      (f := fun i : ι => fun s : ℂ =>
        hadamardGenus1Factor (zeroLoc i) s - 1)
      hU
      hbound
      hcts
  simpa [infiniteHadamardProduct, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hprod

/-- 🌟🌟🌟🌟 **PROVED — finite Hadamard products tend locally uniformly
to the infinite genus-one product under a summable uniform bound.** -/
theorem tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_of_summable_bound
    {ι : Type*} {zeroLoc : ι → ℂ} {U : Set ℂ} {u : ι → ℝ}
    (hU : IsOpen U)
    (hu : Summable u)
    (hbound :
      ∀ᶠ i in Filter.cofinite,
        ∀ s ∈ U,
          ‖hadamardGenus1Factor (zeroLoc i) s - 1‖ ≤ u i) :
    TendstoLocallyUniformlyOn
      (fun F : Finset ι => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc F s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      U := by
  have hprod :=
    hasProdLocallyUniformlyOn_hadamardGenus1Factor_of_summable_bound
      (zeroLoc := zeroLoc) hU hu hbound
  simpa [HasProdLocallyUniformlyOn, indexedFiniteHadamardProduct] using hprod

/-- 🌟🌟🌟🌟 **PROVED — bounded-region uniform genus-one deviation
estimate from inverse-square zero data.** On any region bounded by `R`,
all large zeros satisfy `‖s‖ ≤ ‖ρᵢ‖` uniformly; the Taylor bound gives the
summable majorant `4R²/‖ρᵢ‖²`. -/
theorem HadamardZeroInvSqSummability.eventually_uniform_factor_sub_one_bound
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {U : Set ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hUbound : ∀ s : ℂ, s ∈ U → ‖s‖ ≤ R) :
    ∀ᶠ i in Filter.cofinite,
      ∀ s ∈ U,
        ‖hadamardGenus1Factor (zeroLoc i) s - 1‖
          ≤ 4 * R ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹ := by
  filter_upwards [H.eventually_large ((R : ℝ) : ℂ)] with i hi s hs
  have hnorm_R : ‖((R : ℝ) : ℂ)‖ = R := by
    simp [hR]
  rw [hnorm_R] at hi
  have hR_le : R ≤ ‖zeroLoc i‖ := by
    nlinarith [hR, hi]
  have hlarge : ‖s‖ ≤ ‖zeroLoc i‖ :=
    le_trans (hUbound s hs) hR_le
  have htail :=
    norm_one_sub_hadamardGenus1Factor_le_large
      (ρ := zeroLoc i) (s := s) (H.zero_ne i) hlarge
      genusOneTaylorBoundData
  have hdiff :
      ‖hadamardGenus1Factor (zeroLoc i) s - 1‖
        = ‖1 - hadamardGenus1Factor (zeroLoc i) s‖ := by
    rw [← norm_neg (hadamardGenus1Factor (zeroLoc i) s - 1)]
    congr 1
    ring
  have hsq : ‖s‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [hUbound s hs, norm_nonneg s, hR]
  have hinv_nonneg : 0 ≤ (‖zeroLoc i‖ ^ 2)⁻¹ :=
    inv_nonneg.mpr (sq_nonneg _)
  calc
    ‖hadamardGenus1Factor (zeroLoc i) s - 1‖
        = ‖1 - hadamardGenus1Factor (zeroLoc i) s‖ := hdiff
    _ ≤ 4 * (‖s‖ ^ 2 / ‖zeroLoc i‖ ^ 2) := htail
    _ = 4 * (‖s‖ ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹) := by
        rw [div_eq_mul_inv]
    _ ≤ 4 * (R ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹) := by
        gcongr
    _ = 4 * R ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹ := by ring

/-- 🌟🌟🌟🌟 **PROVED — locally uniform Hadamard product convergence on
bounded open regions from inverse-square zero distribution.** -/
theorem tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_of_norm_bounded_open
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {U : Set ℂ} {R : ℝ}
    (hU : IsOpen U)
    (hR : 0 ≤ R)
    (hUbound : ∀ s : ℂ, s ∈ U → ‖s‖ ≤ R) :
    TendstoLocallyUniformlyOn
      (fun F : Finset ι => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc F s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      U := by
  have hu :
      Summable fun i : ι =>
        4 * R ^ 2 * (‖zeroLoc i‖ ^ 2)⁻¹ :=
    H.inv_sq_summable.mul_left (4 * R ^ 2)
  exact
    tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_of_summable_bound
      hU
      hu
      (H.eventually_uniform_factor_sub_one_bound hR hUbound)

/-- 🌟🌟🌟 **PROVED — a monotone exhaustive finite sequence inherits
locally-uniform convergence from the canonical `Finset` net.** -/
theorem tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_at_exhaustion
    {ι : Type*} {zeroLoc : ι → ℂ}
    {U : Set ℂ} {exhaust : ℕ → Finset ι}
    (HlucFinset :
      TendstoLocallyUniformlyOn
        (fun F : Finset ι => fun s : ℂ =>
          indexedFiniteHadamardProduct zeroLoc F s)
        (infiniteHadamardProduct zeroLoc)
        Filter.atTop
        U)
    (hmono : Monotone exhaust)
    (hexhaustive : ∀ i : ι, ∃ n : ℕ, i ∈ exhaust n) :
    TendstoLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc (exhaust n) s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      U := by
  intro V hV x hx
  rcases HlucFinset V hV x hx with ⟨t, ht, htail⟩
  refine ⟨t, ht, ?_⟩
  exact
    (tendsto_atTop_finset_of_monotone hmono hexhaustive).eventually htail

/-- 🌟🌟🌟🌟 **PROVED — build the sequential locally-uniform Hadamard
product-limit data from `Finset`-net locally-uniform convergence.** -/
noncomputable def HadamardProductLocallyUniformLimitData.of_finsetLocallyUniform
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hex : HadamardFiniteExhaustion zeroLoc)
    (hexhaustive : ∀ i : ι, ∃ n : ℕ, i ∈ Hex.exhaust n)
    {U : Set ℂ}
    (hU : IsOpen U)
    (HlucFinset :
      TendstoLocallyUniformlyOn
        (fun F : Finset ι => fun s : ℂ =>
          indexedFiniteHadamardProduct zeroLoc F s)
        (infiniteHadamardProduct zeroLoc)
        Filter.atTop
        U) :
    HadamardProductLocallyUniformLimitData zeroLoc Hex :=
  { region := U
    isOpen_region := hU
    locally_uniform_product :=
      tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_at_exhaustion
        HlucFinset
        (by
          intro n m hnm
          exact Hex.exhaust_mono hnm)
        hexhaustive }

/-- 🌟🌟🌟🌟🌟 **PROVED — locally uniform convergence of the genus-one
Hadamard product on the whole complex plane from inverse-square zero
distribution.** Genuinely local: near `x`, work inside a ball of radius
`‖x‖+1` and apply the bounded-open theorem. -/
theorem HadamardZeroInvSqSummability.tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_univ
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc) :
    TendstoLocallyUniformlyOn
      (fun F : Finset ι => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc F s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      Set.univ := by
  intro V hV x _hx
  let R : ℝ := ‖x‖ + 1
  have hR : 0 ≤ R := by
    have hxnn : 0 ≤ ‖x‖ := norm_nonneg x
    linarith
  have hRpos : 0 < R := by
    have hxnn : 0 ≤ ‖x‖ := norm_nonneg x
    linarith
  have hxball : x ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball]
    simp [R, dist_eq_norm]
  have hUbound :
      ∀ s : ℂ, s ∈ Metric.ball (0 : ℂ) R → ‖s‖ ≤ R := by
    intro s hs
    exact le_of_lt (by
      rw [Metric.mem_ball] at hs
      simpa [dist_eq_norm] using hs)
  have hball :=
    tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_of_norm_bounded_open
      H Metric.isOpen_ball hR hUbound
  rcases hball V hV x hxball with ⟨t, ht, htail⟩
  refine ⟨t, ?_, htail⟩
  have ht_nhds : t ∈ 𝓝 x := by
    rwa [Metric.isOpen_ball.nhdsWithin_eq hxball] at ht
  simpa using ht_nhds

/-- 🌟🌟🌟🌟 **PROVED — full-plane sequential Hadamard product LUC data
from inverse-square zero distribution and an exhaustive truncation
sequence.** -/
noncomputable def HadamardProductLocallyUniformLimitData.of_invSq_univ
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    (Hex : HadamardFiniteExhaustion zeroLoc)
    (hexhaustive : ∀ i : ι, ∃ n : ℕ, i ∈ Hex.exhaust n) :
    HadamardProductLocallyUniformLimitData zeroLoc Hex :=
  HadamardProductLocallyUniformLimitData.of_finsetLocallyUniform
    Hex
    hexhaustive
    isOpen_univ
    H.tendstoLocallyUniformlyOn_indexedFiniteHadamardProduct_univ

/-- 🌟🌟🌟 **PROVED — infinite genus-one product is nonzero off the
indexed zeros when the genus-one deviations are summable.** Uses Mathlib's
complex logarithm infinite-product theorem. -/
theorem infiniteHadamardProduct_ne_zero_of_summable_factor_sub_one
    {ι : Type*} {zeroLoc : ι → ℂ} {s : ℂ}
    (hfactor_ne :
      ∀ i : ι, hadamardGenus1Factor (zeroLoc i) s ≠ 0)
    (hsum :
      Summable fun i : ι => hadamardGenus1Factor (zeroLoc i) s - 1) :
    infiniteHadamardProduct zeroLoc s ≠ 0 := by
  unfold infiniteHadamardProduct
  have hlog :
      Summable fun i : ι =>
        Complex.log (hadamardGenus1Factor (zeroLoc i) s) := by
    have h :=
      Complex.summable_log_one_add_of_summable
        (f := fun i : ι => hadamardGenus1Factor (zeroLoc i) s - 1)
        hsum
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hprod :=
    Complex.cexp_tsum_eq_tprod
      (f := fun i : ι => hadamardGenus1Factor (zeroLoc i) s)
      hfactor_ne
      hlog
  intro hzero
  have hexp_zero :
      Complex.exp
          (∑' i : ι,
            Complex.log (hadamardGenus1Factor (zeroLoc i) s))
        = 0 := by
    exact hprod.trans hzero
  exact Complex.exp_ne_zero _ hexp_zero

/-- 🌟🌟🌟 **PROVED — inverse-square zero distribution implies the
infinite genus-one product is nonzero away from the indexed zeros.** -/
theorem HadamardZeroInvSqSummability.infiniteProduct_ne_zero
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {s : ℂ} (hs_ne : ∀ i : ι, s ≠ zeroLoc i) :
    infiniteHadamardProduct zeroLoc s ≠ 0 := by
  refine
    infiniteHadamardProduct_ne_zero_of_summable_factor_sub_one
      (zeroLoc := zeroLoc) (s := s) ?_ ?_
  · intro i
    exact hadamardGenus1Factor_ne_zero (H.zero_ne i) (hs_ne i)
  · have h_one_sub :
        Summable fun i : ι =>
          1 - hadamardGenus1Factor (zeroLoc i) s :=
      summable_one_sub_hadamardGenus1Factor_of_inv_sq
        genusOneTaylorBoundData
        H.zero_ne
        H.inv_sq_summable
        (by
          filter_upwards [H.eventually_large s] with i hi
          have h_s_nn : 0 ≤ ‖s‖ := norm_nonneg s
          linarith)
    have h_neg := h_one_sub.neg
    simpa [neg_sub] using h_neg

/-- 🌟🌟🌟🌟 **PROVED — finite derivative convergence gives Hadamard
log-derivative limit data with product nonvanishing discharged by invSq.** -/
noncomputable def HadamardLogDerivLimitData.of_finiteDerivativeLimitData_invSq
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hderiv : HadamardFiniteDerivativeLimitData zeroLoc Hex)
    (Hdiff :
      ∀ s ∈ Hderiv.region,
        DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s)
    (Hno_collision :
      ∀ s ∈ Hderiv.region, ∀ i : ι, s ≠ zeroLoc i) :
    HadamardLogDerivLimitData zeroLoc :=
  HadamardLogDerivLimitData.of_finiteDerivativeLimitData
    Hinv
    Hderiv
    Hdiff
    Hno_collision
    (by
      intro s hs
      exact Hinv.infiniteProduct_ne_zero (Hno_collision s hs))

/-- 📦 **`HadamardProductLUCLogDerivData`** — the LUC + log-derivative
interchange data on `region : Set ℂ`. -/
structure HadamardProductLUCLogDerivData
    {ι : Type*} (zeroLoc : ι → ℂ) where
  region : Set ℂ
  locally_uniform_product :
    TendstoLocallyUniformlyOn
      (fun F : Finset ι => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc F s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      region
  infinite_differentiable_at :
    ∀ s ∈ region,
      DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s
  logDeriv_eq_tsum :
    ∀ s ∈ region,
      logDerivativeResponse (infiniteHadamardProduct zeroLoc) s
        = hadamardRegularizedLogDerivSeries zeroLoc s

/-- 🌟🌟🌟🌟 **PROVED — build the LUC/log-derivative data package from
finite derivative convergence.** -/
noncomputable def HadamardProductLUCLogDerivData.of_finiteDerivativeLimitData
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hderiv : HadamardFiniteDerivativeLimitData zeroLoc Hex)
    (HlucProduct :
      TendstoLocallyUniformlyOn
        (fun F : Finset ι => fun s : ℂ =>
          indexedFiniteHadamardProduct zeroLoc F s)
        (infiniteHadamardProduct zeroLoc)
        Filter.atTop
        Hderiv.region)
    (Hdiff :
      ∀ s ∈ Hderiv.region,
        DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s)
    (Hno_collision :
      ∀ s ∈ Hderiv.region, ∀ i : ι, s ≠ zeroLoc i)
    (Hprod_ne :
      ∀ s ∈ Hderiv.region,
        infiniteHadamardProduct zeroLoc s ≠ 0) :
    HadamardProductLUCLogDerivData zeroLoc :=
  { region := Hderiv.region
    locally_uniform_product := by
      simpa using HlucProduct
    infinite_differentiable_at := Hdiff
    logDeriv_eq_tsum := by
      intro s hs
      exact
        (HadamardLogDerivLimitData.of_finiteDerivativeLimitData
          Hinv Hderiv Hdiff Hno_collision Hprod_ne).logDeriv_eq_tsum_at s hs }

/-- 🌟🌟🌟🌟 **PROVED — build LUC/log-derivative data from finite
derivative convergence with product nonvanishing discharged by invSq.** -/
noncomputable def HadamardProductLUCLogDerivData.of_finiteDerivativeLimitData_invSq
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hderiv : HadamardFiniteDerivativeLimitData zeroLoc Hex)
    (HlucProduct :
      TendstoLocallyUniformlyOn
        (fun F : Finset ι => fun s : ℂ =>
          indexedFiniteHadamardProduct zeroLoc F s)
        (infiniteHadamardProduct zeroLoc)
        Filter.atTop
        Hderiv.region)
    (Hdiff :
      ∀ s ∈ Hderiv.region,
        DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s)
    (Hno_collision :
      ∀ s ∈ Hderiv.region, ∀ i : ι, s ≠ zeroLoc i) :
    HadamardProductLUCLogDerivData zeroLoc :=
  HadamardProductLUCLogDerivData.of_finiteDerivativeLimitData
    Hinv
    Hderiv
    HlucProduct
    Hdiff
    Hno_collision
    (by
      intro s hs
      exact Hinv.infiniteProduct_ne_zero (Hno_collision s hs))

/-- 🌟🌟🌟🌟🌟 **PROVED — build the LUC/log-derivative package directly
from locally-uniform finite Hadamard product convergence.** -/
noncomputable def
    HadamardProductLUCLogDerivData.of_locallyUniformProductLimitData
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (HlucSeq : HadamardProductLocallyUniformLimitData zeroLoc Hex)
    (HlucFinset :
      TendstoLocallyUniformlyOn
        (fun F : Finset ι => fun s : ℂ =>
          indexedFiniteHadamardProduct zeroLoc F s)
        (infiniteHadamardProduct zeroLoc)
        Filter.atTop
        HlucSeq.region)
    (Hno_collision :
      ∀ s ∈ HlucSeq.region, ∀ i : ι, s ≠ zeroLoc i)
    (Hprod_ne :
      ∀ s ∈ HlucSeq.region,
        infiniteHadamardProduct zeroLoc s ≠ 0) :
    HadamardProductLUCLogDerivData zeroLoc := by
  let Hderiv : HadamardFiniteDerivativeLimitData zeroLoc Hex :=
    HadamardFiniteDerivativeLimitData.of_locallyUniformProduct HlucSeq
  exact
    HadamardProductLUCLogDerivData.of_finiteDerivativeLimitData
      Hinv
      Hderiv
      (by
        simpa [Hderiv, HadamardFiniteDerivativeLimitData.of_locallyUniformProduct]
          using HlucFinset)
      (by
        intro s hs
        exact HlucSeq.infinite_differentiableAt
          (by
            simpa [Hderiv, HadamardFiniteDerivativeLimitData.of_locallyUniformProduct]
              using hs))
      (by
        intro s hs
        exact Hno_collision s
          (by
            simpa [Hderiv, HadamardFiniteDerivativeLimitData.of_locallyUniformProduct]
              using hs))
      (by
        intro s hs
        exact Hprod_ne s
          (by
            simpa [Hderiv, HadamardFiniteDerivativeLimitData.of_locallyUniformProduct]
              using hs))

/-- 🌟🌟🌟🌟🌟 **PROVED — build the LUC/log-derivative package directly
from locally-uniform product convergence with product nonvanishing
discharged by inverse-square zero distribution.** -/
noncomputable def
    HadamardProductLUCLogDerivData.of_locallyUniformProductLimitData_invSq
    {ι : Type*} {zeroLoc : ι → ℂ}
    {Hex : HadamardFiniteExhaustion zeroLoc}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (HlucSeq : HadamardProductLocallyUniformLimitData zeroLoc Hex)
    (HlucFinset :
      TendstoLocallyUniformlyOn
        (fun F : Finset ι => fun s : ℂ =>
          indexedFiniteHadamardProduct zeroLoc F s)
        (infiniteHadamardProduct zeroLoc)
        Filter.atTop
        HlucSeq.region)
    (Hno_collision :
      ∀ s ∈ HlucSeq.region, ∀ i : ι, s ≠ zeroLoc i) :
    HadamardProductLUCLogDerivData zeroLoc :=
  HadamardProductLUCLogDerivData.of_locallyUniformProductLimitData
    Hinv
    HlucSeq
    HlucFinset
    Hno_collision
    (by
      intro s hs
      exact Hinv.infiniteProduct_ne_zero (Hno_collision s hs))

/-- 🌟🌟🌟 **PROVED — `HadamardLogDerivLimitData` from LUC + inv-sq +
no-collision in region.** -/
noncomputable def HadamardLogDerivLimitData.of_productLUC_and_invSq
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hluc : HadamardProductLUCLogDerivData zeroLoc)
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (HnonzeroRegion : ∀ s ∈ Hluc.region, ∀ i, s ≠ zeroLoc i) :
    HadamardLogDerivLimitData zeroLoc :=
  { region := Hluc.region
    product_differentiable_at := Hluc.infinite_differentiable_at
    regularized_summable_at := fun s hs =>
      Hinv.summable_regularized (HnonzeroRegion s hs)
    logDeriv_eq_tsum_at := Hluc.logDeriv_eq_tsum }

end OverflowResidueRH
