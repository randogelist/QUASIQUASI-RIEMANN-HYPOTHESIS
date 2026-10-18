import Frontier.BKQRHardyCoeffFrontier
import Derivations.BKQR.DefectGramSquare

namespace NativeSolobolo.Derivations.BKQR

open NativeSolobolo
open NativeSolobolo.Frontier

/-- ! Every metric Cayley radius is nonnegative. -/
theorem CAYLEY_RADIUS_AT_METRIC_DEPTH_NONNEG (eta : ℝ) :
    0 ≤ cayleyRadiusAtMetricDepth eta := by
  unfold cayleyRadiusAtMetricDepth
  exact sq_nonneg _

/-- !! Strict increase of the Cayley radius on the sub-pi nonnegative gauge. -/
theorem CAYLEY_RADIUS_STRICT_MONO_SUBPI
    {eta xi : ℝ}
    (heta : 0 ≤ eta)
    (hEtaXi : eta < xi)
    (hXiPi : xi < Real.pi) :
    cayleyRadiusAtMetricDepth eta < cayleyRadiusAtMetricDepth xi := by
  unfold cayleyRadiusAtMetricDepth
  have hleft : -(Real.pi / 2) ≤ eta / 2 := by
    linarith [Real.pi_pos]
  have hright : xi / 2 ≤ Real.pi / 2 := by
    linarith
  have hhalf : eta / 2 < xi / 2 := by
    linarith
  have hsin : Real.sin (eta / 2) < Real.sin (xi / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two hleft hright hhalf
  have hsEta : 0 ≤ Real.sin (eta / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith [Real.pi_pos]
  have hsXi : 0 ≤ Real.sin (xi / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith [Real.pi_pos]
  nlinarith

/-- ! A strictly positive sub-pi metric depth has positive Cayley radius. -/
theorem CAYLEY_RADIUS_POS_OF_POS_SUBPI
    {eta : ℝ}
    (heta : 0 < eta)
    (hEtaPi : eta < Real.pi) :
    0 < cayleyRadiusAtMetricDepth eta := by
  unfold cayleyRadiusAtMetricDepth
  have hs : 0 < Real.sin (eta / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  positivity

/-- ! A nonnegative sub-pi metric depth has Cayley radius at most one. -/
theorem CAYLEY_RADIUS_LE_ONE_SUBPI
    {eta : ℝ}
    (heta : 0 ≤ eta)
    (hEtaPi : eta < Real.pi) :
    cayleyRadiusAtMetricDepth eta ≤ 1 := by
  unfold cayleyRadiusAtMetricDepth
  have hs0 : 0 ≤ Real.sin (eta / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith [Real.pi_pos]
  have hs1 : Real.sin (eta / 2) ≤ 1 := Real.sin_le_one _
  nlinarith

/--
!! Elementary geometric-transfer lemma.
A uniform coefficient envelope at a positive radius R implies absolute
summability at every strictly smaller nonnegative radius r.
-/
theorem WEIGHTED_COEFF_BOUND_IMPLIES_SUMMABLE_AT_SMALLER_RADIUS
    (u : Nat → ℝ)
    {r R C : ℝ}
    (hr0 : 0 ≤ r)
    (hR0 : 0 < R)
    (hrR : r < R)
    (hC0 : 0 ≤ C)
    (hBound : ∀ n : Nat, |u n| * R ^ n ≤ C) :
    Summable (fun n : Nat => |u n| * r ^ n) := by
  let q : ℝ := r / R
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hr0 (le_of_lt hR0)
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hR0).2 hrR
  have hGeom0 : Summable (fun n : Nat => q ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  have hGeom : Summable (fun n : Nat => C * q ^ n) :=
    Summable.mul_left C hGeom0
  refine Summable.of_norm_bounded hGeom ?_
  intro n
  have hqpow : 0 ≤ q ^ n := pow_nonneg hq0 n
  have hmul : (|u n| * R ^ n) * q ^ n ≤ C * q ^ n :=
    mul_le_mul_of_nonneg_right (hBound n) hqpow
  have hEq : |u n| * r ^ n = (|u n| * R ^ n) * q ^ n := by
    dsimp [q]
    rw [div_pow]
    field_simp [pow_ne_zero n (ne_of_gt hR0)]
  have hnonneg : 0 ≤ |u n| * r ^ n :=
    mul_nonneg (abs_nonneg _) (pow_nonneg hr0 n)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hEq]
  exact hmul

/--
!!! A weighted coefficient certificate at a strictly deeper metric depth gives
absolute convergence at every shallower target depth.
-/
theorem DEEPER_WEIGHTED_COEFF_BOUND_IMPLIES_ABSOLUTE_CAYLEY_SERIES
    {mu : ℝ → Nat → ℝ}
    {eta xi : ℝ}
    (heta : 0 ≤ eta)
    (hEtaXi : eta < xi)
    (hXiPi : xi < Real.pi)
    (hBound : WeightedCayleyCoeffBoundAt mu xi) :
    AbsoluteCayleySeriesRegularAt mu eta := by
  intro a ha
  obtain ⟨C, hC0, hC⟩ := hBound a ha
  have hXi0 : 0 < xi := lt_of_le_of_lt heta hEtaXi
  have hR0 : 0 < cayleyRadiusAtMetricDepth xi :=
    CAYLEY_RADIUS_POS_OF_POS_SUBPI hXi0 hXiPi
  have hr0 : 0 ≤ cayleyRadiusAtMetricDepth eta :=
    CAYLEY_RADIUS_AT_METRIC_DEPTH_NONNEG eta
  have hrR : cayleyRadiusAtMetricDepth eta < cayleyRadiusAtMetricDepth xi :=
    CAYLEY_RADIUS_STRICT_MONO_SUBPI heta hEtaXi hXiPi
  exact WEIGHTED_COEFF_BOUND_IMPLIES_SUMMABLE_AT_SMALLER_RADIUS
    (fun n => mu a n) hr0 hR0 hrR hC0 hC

/--
!!! Cofinal BKQR-pi coefficient envelopes therefore give absolute convergence
of the whole Cayley coefficient germ at every strict sub-pi metric depth.
-/
theorem BKQR_PI_COEFF_IMPLIES_ALL_SUBPI_ABSOLUTE_CAYLEY_SERIES
    {mu : ℝ → Nat → ℝ}
    (hPi : StrictBKQRPiCoeffFrontier mu) :
    MetricPi (AbsoluteCayleySeriesRegularAt mu) := by
  intro eta heta hEtaPi
  obtain ⟨xi, hEtaXi, hXiPi, hBound⟩ := hPi eta heta hEtaPi
  exact DEEPER_WEIGHTED_COEFF_BOUND_IMPLIES_ABSOLUTE_CAYLEY_SERIES
    heta hEtaXi hXiPi hBound

/--
!! A genuine contractive BKQR orbit automatically supplies a weighted
coefficient envelope at every sub-pi metric depth.
-/
theorem CONTRACTIVE_ORBIT_GIVES_WEIGHTED_CAYLEY_COEFF_BOUND
    {Vec : Type}
    {Q : RealGramGeometry Vec}
    {mu : ℝ → Nat → ℝ}
    (M : BKQRContractiveOrbit Q mu)
    {eta : ℝ}
    (heta : 0 ≤ eta)
    (hEtaPi : eta < Real.pi) :
    WeightedCayleyCoeffBoundAt mu eta := by
  intro a _ha
  refine ⟨|mu a 0|, abs_nonneg _, ?_⟩
  intro n
  have hsq : (mu a n) ^ 2 ≤ (mu a 0) ^ 2 :=
    MOMENT_SQ_LE_BASE_SQ M a n
  have habs : |mu a n| ≤ |mu a 0| := (sq_le_sq).mp hsq
  have hr0 : 0 ≤ cayleyRadiusAtMetricDepth eta :=
    CAYLEY_RADIUS_AT_METRIC_DEPTH_NONNEG eta
  have hr1 : cayleyRadiusAtMetricDepth eta ≤ 1 :=
    CAYLEY_RADIUS_LE_ONE_SUBPI heta hEtaPi
  have hrpow : (cayleyRadiusAtMetricDepth eta) ^ n ≤ 1 :=
    pow_le_one₀ hr0 hr1
  calc
    |mu a n| * (cayleyRadiusAtMetricDepth eta) ^ n
        ≤ |mu a 0| * (cayleyRadiusAtMetricDepth eta) ^ n :=
          mul_le_mul_of_nonneg_right habs (pow_nonneg hr0 n)
    _ ≤ |mu a 0| * 1 :=
          mul_le_mul_of_nonneg_left hrpow (abs_nonneg _)
    _ = |mu a 0| := by ring

/-- !!! The old contractive-orbit frontier implies the new cofinal coefficient frontier. -/
theorem CONTRACTIVE_ORBIT_FRONTIER_IMPLIES_STRICT_BKQR_PI_COEFF
    {mu : ℝ → Nat → ℝ}
    (hOrbit : BKQRContractiveOrbitFrontier mu) :
    StrictBKQRPiCoeffFrontier mu := by
  intro eta heta hEtaPi
  let xi : ℝ := (eta + Real.pi) / 2
  have hEtaXi : eta < xi := by
    dsimp [xi]
    linarith
  have hXiPi : xi < Real.pi := by
    dsimp [xi]
    linarith
  have hXi0 : 0 ≤ xi := le_trans heta (le_of_lt hEtaXi)
  obtain ⟨Vec, Q, hM⟩ := hOrbit
  let M : BKQRContractiveOrbit Q mu := Classical.choice hM
  refine ⟨xi, hEtaXi, hXiPi, ?_⟩
  exact CONTRACTIVE_ORBIT_GIVES_WEIGHTED_CAYLEY_COEFF_BOUND M hXi0 hXiPi

end NativeSolobolo.Derivations.BKQR
