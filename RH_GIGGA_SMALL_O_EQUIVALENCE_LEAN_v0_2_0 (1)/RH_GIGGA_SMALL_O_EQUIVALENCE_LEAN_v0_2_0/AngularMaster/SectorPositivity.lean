import AngularMaster.ComplexScaleProduct
import AngularMaster.ConjugateFactor
import AngularMaster.AngularCutoff
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual angular positivity from a complex-scale sector bound

The proof symmetrizes the evaluation variable before taking squared norms.
It therefore needs neither a conjugation pairing of zero indices nor RH.
Pointwise convergence of nonnegative monotone finite products yields
monotonicity of the square of the actual profile, hence of the profile itself.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators ComplexConjugate

namespace AngularMaster
open OverflowResidueRH

/-- The same-index symmetric factor used to represent the squared profile. -/
def actualSymmetricFactor (i : ActualPairIndex) (r x : ℝ) : ℝ :=
  Complex.normSq ((1 + circlePoint r x / actualComplexScale i) *
    (1 + conj (circlePoint r x) / actualComplexScale i))

theorem actualSymmetricFactor_nonnegative (i : ActualPairIndex) (r x : ℝ) :
    0 ≤ actualSymmetricFactor i r x :=
  Complex.normSq_nonneg _

theorem actualSymmetricFactor_monotoneOn (i : ActualPairIndex)
    {r a : ℝ} (hr : 0 ≤ r) (ha : -1 ≤ a) (ha0 : a ≤ 0)
    (hscale : (-actualComplexScale i).re / ‖actualComplexScale i‖ ≤ a) :
    MonotoneOn (actualSymmetricFactor i r) (Icc a 1) := by
  have hca : (-actualComplexScale i).re / ‖-actualComplexScale i‖ ≤ a := by
    simpa only [norm_neg] using hscale
  have hmono := monotoneOn_normSq_conjugateFactor_circle
    (neg_ne_zero.mpr (actualComplexScale_ne_zero i)) hr ha ha0 hca
  have heq (x : ℝ) : actualSymmetricFactor i r x =
      Complex.normSq ((1 - circlePoint r x / (-actualComplexScale i)) *
        (1 - circlePoint r x / conj (-actualComplexScale i))) := by
    simpa only [actualSymmetricFactor, div_neg, sub_neg_eq_add] using
      normSq_symmetricFactor_eq_conjugateFactor (-actualComplexScale i)
        (circlePoint r x)
  intro x hx y hy hxy
  rw [heq, heq]
  exact hmono hx hy hxy

theorem actual_origin_factor_normSq_at (C z : ℂ) :
    Complex.normSq (C * (-Complex.I * Complex.sqrt z) ^
      entireXiPullbackOriginMultiplicity) =
      Complex.normSq C * ‖z‖ ^ entireXiPullbackOriginMultiplicity := by
  rw [map_mul, map_pow]
  congr 1
  rw [Complex.normSq_eq_norm_sq, transformed_root_norm_sq]

/-- Finite products of the symmetric factors converge to the square of the
actual squared-modulus profile. This identification is unconditional. -/
theorem actualProfile_sq_symmetric_product_values :
    ∃ c : ℝ → ℝ, (∀ r, 0 < r → 0 ≤ c r) ∧
      ∀ r, 0 < r → ∀ x ∈ angularInterval,
        Tendsto (fun s : Finset ActualPairIndex =>
          c r * ∏ i ∈ s, actualSymmetricFactor i r x)
          atTop (𝓝 ((actualProfile r x) ^ 2)) := by
  obtain ⟨C, hC, hfactor⟩ := actual_theta_complex_factorization
  let c : ℝ → ℝ := fun r =>
    (Complex.normSq C * r ^ entireXiPullbackOriginMultiplicity) ^ 2
  refine ⟨c, ?_, ?_⟩
  · intro r hr
    exact sq_nonneg _
  · intro r hr x hx
    let z := circlePoint r x
    let k : ℂ := C * (-Complex.I * Complex.sqrt z) ^ entireXiPullbackOriginMultiplicity
    let kc : ℂ := C * (-Complex.I * Complex.sqrt (conj z)) ^
      entireXiPullbackOriginMultiplicity
    have hp : Tendsto (fun s : Finset ActualPairIndex =>
        ∏ i ∈ s, (1 + z / actualComplexScale i)) atTop
        (𝓝 (∏' i : ActualPairIndex, (1 + z / actualComplexScale i))) :=
      (actual_complexScaleProduct_multipliable z).hasProd
    have hpc : Tendsto (fun s : Finset ActualPairIndex =>
        ∏ i ∈ s, (1 + conj z / actualComplexScale i)) atTop
        (𝓝 (∏' i : ActualPairIndex, (1 + conj z / actualComplexScale i))) :=
      (actual_complexScaleProduct_multipliable (conj z)).hasProd
    have ht := hp.const_mul k
    have htc := hpc.const_mul kc
    have hk : k * (∏' i : ActualPairIndex, (1 + z / actualComplexScale i)) =
        AWPIRH.theta z := (hfactor z).symm
    have hkc : kc * (∏' i : ActualPairIndex,
        (1 + conj z / actualComplexScale i)) = AWPIRH.theta (conj z) :=
      (hfactor (conj z)).symm
    rw [hk] at ht
    rw [hkc] at htc
    have hlim := Complex.continuous_normSq.continuousAt.tendsto.comp (ht.mul htc)
    have hn : ‖z‖ = r := circlePoint_norm r x hr.le hx
    have hkn : Complex.normSq k =
        Complex.normSq C * r ^ entireXiPullbackOriginMultiplicity := by
      dsimp only [k]
      rw [actual_origin_factor_normSq_at, hn]
    have hkcn : Complex.normSq kc =
        Complex.normSq C * r ^ entireXiPullbackOriginMultiplicity := by
      dsimp only [kc]
      rw [actual_origin_factor_normSq_at, Complex.norm_conj, hn]
    convert hlim using 1
    · ext s
      simp only [Function.comp_apply, map_mul, map_prod, hkn, hkcn,
        actualSymmetricFactor, c]
      rw [Finset.prod_mul_distrib]
      dsimp only [z]
      ring
    · rw [map_mul, actual_theta_normSq_conj]
      congr 1
      change (actualProfile r x) ^ 2 = actualProfile r x * actualProfile r x
      ring

/-- Sector control of the literal complex zero scales makes the full actual
profile monotone above the cutoff, uniformly over every positive radius. -/
theorem actualProfile_monotoneOn_of_scale_sector {a : ℝ}
    (ha : -1 ≤ a) (ha0 : a ≤ 0)
    (hscale : ∀ i : ActualPairIndex,
      (-actualComplexScale i).re / ‖actualComplexScale i‖ ≤ a)
    (r : ℝ) (hr : 0 < r) :
    MonotoneOn (actualProfile r) (Icc a 1) := by
  obtain ⟨c, hc, hp⟩ := actualProfile_sq_symmetric_product_values
  intro x hx y hy hxy
  have hxg : x ∈ angularInterval := ⟨ha.trans hx.1, hx.2⟩
  have hyg : y ∈ angularInterval := ⟨ha.trans hy.1, hy.2⟩
  have hsq : (actualProfile r x) ^ 2 ≤ (actualProfile r y) ^ 2 := by
    apply le_of_tendsto_of_tendsto' (hp r hr x hxg) (hp r hr y hyg)
    intro s
    apply mul_le_mul_of_nonneg_left ?_ (hc r hr)
    apply Finset.prod_le_prod
    · intro i hi
      exact actualSymmetricFactor_nonnegative i r x
    · intro i hi
      exact actualSymmetricFactor_monotoneOn i hr.le ha ha0 (hscale i) hx hy hxy
  exact (sq_le_sq₀ (actualProfile_nonnegative_all r x)
    (actualProfile_nonnegative_all r y)).mp hsq

/-- The only premise is the stated sector geometry of the actual scales.
There is no RH hypothesis and no assumed profile or derivative identity. -/
theorem actual_cutoffDerivativeNonnegative_of_complexScale_sector {a : ℝ}
    (ha : -1 ≤ a) (ha0 : a ≤ 0)
    (hscale : ∀ i : ActualPairIndex,
      -(actualComplexScale i).re / ‖actualComplexScale i‖ ≤ a) :
    CutoffDerivativeNonnegative a := by
  intro r hr x hx
  have hscale' : ∀ i : ActualPairIndex,
      (-actualComplexScale i).re / ‖actualComplexScale i‖ ≤ a := by
    intro i
    simpa only [Complex.neg_re] using hscale i
  have hm := actualProfile_monotoneOn_of_scale_sector ha ha0 hscale' r hr
  have hd : 0 ≤ derivWithin (actualProfile r) (Icc a 1) x :=
    hm.derivWithin_nonneg
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)] at hd
  change 0 ≤ derivWithin (actualProfile r) (Icc (-1) 1) x
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds (lt_of_le_of_lt ha hx.1) hx.2)]
  exact hd

end AngularMaster
