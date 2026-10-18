import Derivations.Geometry.ActualCayleyObservable
import Frontier.BKQRPiFrontier

namespace NativeSolobolo.Derivations.Geometry

open NativeSolobolo
open NativeSolobolo.Frontier

/-- ! The inverse metric depth of an interior Cayley radius is nonnegative. -/
theorem METRIC_DEPTH_OF_INTERIOR_RADIUS_NONNEG
    {r : ℝ}
    (hr : InteriorRadius r) :
    0 ≤ metricDepthOfCayleyRadius r := by
  unfold metricDepthOfCayleyRadius
  have hs : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have ha : 0 ≤ Real.arcsin (Real.sqrt r) := (Real.arcsin_nonneg).2 hs
  linarith

/-- !! An interior Cayley radius corresponds to a strict sub-pi metric depth. -/
theorem METRIC_DEPTH_OF_INTERIOR_RADIUS_LT_PI
    {r : ℝ}
    (hr : InteriorRadius r) :
    metricDepthOfCayleyRadius r < Real.pi := by
  unfold metricDepthOfCayleyRadius
  have hr0 : 0 ≤ r := le_of_lt hr.1
  have hs0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr0
  have hs1 : Real.sqrt r < 1 := by
    by_contra hnot
    have hge : 1 ≤ Real.sqrt r := le_of_not_gt hnot
    have hsqge : 1 ≤ (Real.sqrt r) ^ 2 := by
      nlinarith
    rw [hsq] at hsqge
    exact (not_lt_of_ge hsqge) hr.2
  have ha : Real.arcsin (Real.sqrt r) < Real.pi / 2 :=
    (Real.arcsin_lt_pi_div_two).2 hs1
  linarith

/-- !!! Exact round trip r -> 2 asin(sqrt r) -> sin^2(eta/2) on the open unit interval. -/
theorem CAYLEY_RADIUS_METRIC_DEPTH_ROUNDTRIP
    {r : ℝ}
    (hr : InteriorRadius r) :
    cayleyRadiusAtMetricDepth (metricDepthOfCayleyRadius r) = r := by
  unfold cayleyRadiusAtMetricDepth metricDepthOfCayleyRadius
  have hr0 : 0 ≤ r := le_of_lt hr.1
  have hs0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr0
  have hs1 : Real.sqrt r < 1 := by
    by_contra hnot
    have hge : 1 ≤ Real.sqrt r := le_of_not_gt hnot
    have hsqge : 1 ≤ (Real.sqrt r) ^ 2 := by
      nlinarith
    rw [hsq] at hsqge
    exact (not_lt_of_ge hsqge) hr.2
  have hsm1 : -1 ≤ Real.sqrt r := by
    linarith
  have hsle1 : Real.sqrt r ≤ 1 := le_of_lt hs1
  have hhalf : (2 * Real.arcsin (Real.sqrt r)) / 2 = Real.arcsin (Real.sqrt r) := by
    ring
  rw [hhalf, Real.sin_arcsin hsm1 hsle1]
  exact hsq

/--
!!! Any literal interior pole of the actual Theta Cayley observable is a failure
of actual metric regularity at a strict sub-pi depth.
-/
theorem ACTUAL_INTERIOR_CAYLEY_POLE_GIVES_SUBPI_METRIC_IRREGULARITY
    (T : CenteredThetaData)
    {a r : ℝ}
    (ha : PositiveAnchor a)
    (hr : InteriorRadius r)
    (hpole : (actualThetaCayleyObservable T).eval a r = none) :
    ∃ eta : ℝ,
      0 ≤ eta ∧ eta < Real.pi ∧ ¬ ActualCayleyMetricRegularAt T eta := by
  let eta : ℝ := metricDepthOfCayleyRadius r
  refine ⟨eta,
    METRIC_DEPTH_OF_INTERIOR_RADIUS_NONNEG hr,
    METRIC_DEPTH_OF_INTERIOR_RADIUS_LT_PI hr, ?_⟩
  intro hreg
  have hne := hreg a ha
  have hround : cayleyRadiusAtMetricDepth eta = r := by
    dsimp [eta]
    exact CAYLEY_RADIUS_METRIC_DEPTH_ROUNDTRIP hr
  rw [hround] at hne
  exact hne hpole

/--
!!! ACTUAL NON-RH -> SUB-PI METRIC IRREGULARITY.
This derives the former obstruction interface directly from the already proved
actual interior Cayley pole theorem and the exact metric gauge.
-/
theorem NOT_RH_IMPLIES_ACTUAL_SUBPI_METRIC_IRREGULARITY
    (T : CenteredThetaData)
    (hNotRH : ¬ RiemannHypothesis T.geometry) :
    ∃ eta : ℝ,
      0 ≤ eta ∧ eta < Real.pi ∧ ¬ ActualCayleyMetricRegularAt T eta := by
  obtain ⟨a, r, ha, hr, hpole⟩ :=
    NOT_RH_IMPLIES_ACTUAL_INTERIOR_CAYLEY_POLE T hNotRH
  exact ACTUAL_INTERIOR_CAYLEY_POLE_GIVES_SUBPI_METRIC_IRREGULARITY
    T ha hr hpole

/-- !!! The generic metric-pi obstruction is now canonically constructed. -/
def ACTUAL_CAYLEY_METRIC_PI_OBSTRUCTION
    (T : CenteredThetaData) :
    ActualMetricPiObstruction T (ActualCayleyMetricRegularAt T) where
  notRH_bad_depth := NOT_RH_IMPLIES_ACTUAL_SUBPI_METRIC_IRREGULARITY T

end NativeSolobolo.Derivations.Geometry
