import Frontier.BKQRStrictPiFrontier

namespace NativeSolobolo

/--
A weighted coefficient envelope at metric depth `eta`.
For each positive anchor, one constant bounds every Cayley/Widder coefficient
weighted by the radius `r(eta)^n`.
-/
def WeightedCayleyCoeffBoundAt
    (mu : ℝ → Nat → ℝ) (eta : ℝ) : Prop :=
  ∀ a : ℝ, PositiveAnchor a →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : Nat,
        |mu a n| * (cayleyRadiusAtMetricDepth eta) ^ n ≤ C

/-- Absolute convergence of the coefficient germ at every positive anchor. -/
def AbsoluteCayleySeriesRegularAt
    (mu : ℝ → Nat → ℝ) (eta : ℝ) : Prop :=
  ∀ a : ℝ, PositiveAnchor a →
    Summable (fun n : Nat =>
      |mu a n| * (cayleyRadiusAtMetricDepth eta) ^ n)

/--
!!! COFINAL BKQR-PI COEFFICIENT FRONTIER.
Every target sub-pi depth is strictly dominated by another sub-pi depth where
all weighted GP/Widder coefficients have a uniform-in-depth envelope.
-/
def StrictBKQRPiCoeffFrontier (mu : ℝ → Nat → ℝ) : Prop :=
  StrictBKQRPiApprox (WeightedCayleyCoeffBoundAt mu)

namespace Frontier

/--
The remaining local analytic identification interface.
Once the actual Cayley/Widder coefficients are known to have an absolutely
convergent germ at a metric depth, the literal theta'/theta Cayley observable
is finite there.

This deliberately contains no energy estimate and no RH statement.
-/
structure ActualCayleyJetBridge
    (T : CenteredThetaData)
    (mu : ℝ → Nat → ℝ) where
  absolute_series_to_actual : ∀ eta : ℝ,
    0 ≤ eta → eta < Real.pi →
    AbsoluteCayleySeriesRegularAt mu eta →
    ActualCayleyMetricRegularAt T eta

end Frontier
end NativeSolobolo
