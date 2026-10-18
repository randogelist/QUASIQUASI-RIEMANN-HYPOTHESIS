import Bridge.XiWidderIdentification
import Derivations.Hausdorff.CentralCell
import Mathlib

namespace NativeSoloboloNegativity

open Filter
open scoped Topology BigOperators

noncomputable section

/-- The Mersenne Widder depth whose moment exponent is a power of two. -/
def mersenneDepth (k : ℕ) : ℕ := 2^k - 1

/-- Explicit statement that every positive anchor belongs to the actual xi regular domain.
    This is intentionally an input until positive-real-axis xi nonvanishing is formalized. -/
def AllPositiveXiRegular : Prop :=
  ∀ a : ℝ, 0 < a → a ∈ xiRegularAnchors

/-- Actual xi direct formula = exact near-central Hausdorff cell on every regular anchor. -/
theorem XI_DIRECT_EQ_CENTRAL_HAUSDORFF_ON_REGULAR_ANCHORS
    (a : ℝ) (ha : a ∈ xiRegularAnchors) (n : ℕ) :
    xiWidderDirect a n = centralWidderMoment xiR n a := by
  rw [← XI_DIRECT_SCALED_EQ_DIRECT a n]
  exact WIDDER_DIRECT_EQ_CENTRAL_HAUSDORFF_ON_OPEN
    XI_REGULAR_ANCHORS_OPEN XI_R_ANALYTIC_ON_REGULAR_ANCHORS n ha

/-- !!! Actual recursive xi Widder moment = 4^(N+1) H_a(N,N+1)
    on the explicit regular-anchor domain. -/
theorem XI_RECURSIVE_EQ_CENTRAL_HAUSDORFF_ON_REGULAR_ANCHORS
    (a : ℝ) (ha : a ∈ xiRegularAnchors) (n : ℕ) :
    xiWidderMoment a n = centralWidderMoment xiR n a := by
  rw [← XI_WIDDER_DIRECT_EQ_RECURSIVE_ON_REGULAR_ANCHORS a ha n]
  exact XI_DIRECT_EQ_CENTRAL_HAUSDORFF_ON_REGULAR_ANCHORS a ha n

/-- The normalization is exposed literally: the central object is 4^(N+1) H(N,N+1). -/
theorem XI_CENTRAL_HAUSDORFF_NORMALIZATION (a : ℝ) (n : ℕ) :
    centralWidderMoment xiR n a =
      (4 : ℝ)^(n + 1) * jetHausdorffCell xiR n (n + 1) a := rfl

/-- Cofinal positivity only on Mersenne depths. This is the sparse certificate,
    not all-depth Hausdorff positivity. -/
def CofinalMersenneCentralPositive : Prop :=
  ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
    ∀ a : ℝ, 0 < a → 0 ≤ centralWidderMoment xiR (mersenneDepth k) a

/-- !!! Cofinal Mersenne central-cell positivity already gives the existing
    cofinal uniform-depth positivity, once all positive anchors are regular. -/
theorem MERSENNE_CENTRAL_POSITIVITY_GIVES_COFINAL_WIDDER
    (hreg : AllPositiveXiRegular)
    (hpos : CofinalMersenneCentralPositive) :
    CofinalUniformDepthPositive := by
  intro K
  rcases hpos (K + 1) with ⟨k, hk, hkpos⟩
  have hkposNat : 0 < k := by omega
  have hkpow : k < 2^k := (Nat.lt_two_pow_self : k < 2^k)
  have hKpow : K < 2^k := lt_of_lt_of_le (by omega) (Nat.le_of_lt hkpow)
  have hdepth : K ≤ mersenneDepth k := by
    unfold mersenneDepth
    omega
  refine ⟨mersenneDepth k, hdepth, ?_⟩
  intro a ha
  have hregular := hreg a ha
  rw [XI_RECURSIVE_EQ_CENTRAL_HAUSDORFF_ON_REGULAR_ANCHORS a hregular]
  exact hkpos a ha

/-- !!! Sparse Mersenne central-cell positivity + the existing explicit
    off-line channel analysis is already enough for native Mathlib RH. -/
theorem MERSENNE_CENTRAL_POSITIVITY_AND_CHANNEL_ANALYSIS_IMPLY_RH
    (hchannel : ActualOffLineChannelAnalysis)
    (hreg : AllPositiveXiRegular)
    (hpos : CofinalMersenneCentralPositive) :
    _root_.RiemannHypothesis :=
  COFINAL_POSITIVITY_AND_CHANNEL_ANALYSIS_IMPLY_RH hchannel
    (MERSENNE_CENTRAL_POSITIVITY_GIVES_COFINAL_WIDDER hreg hpos)

/-- A finite Q-square certificate for one scalar cell. -/
structure FiniteQSquare (x : ℝ) where
  dim : ℕ
  coord : Fin dim → ℝ
  value_eq : x = ∑ i : Fin dim, (coord i)^2

/-- Every finite Q-square is nonnegative. -/
theorem FiniteQSquare.nonneg {x : ℝ} (Q : FiniteQSquare x) : 0 ≤ x := by
  rw [Q.value_eq]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (Q.coord i))

/-- Minimal exact BKQR construction target: Q-squares only on an unbounded
    Mersenne subsequence of the near-central cells. -/
def CofinalMersenneQSquareConstruction : Prop :=
  ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
    ∀ a : ℝ, 0 < a → Nonempty
      (FiniteQSquare (centralWidderMoment xiR (mersenneDepth k) a))

/-- Exact finite Q-squares imply the sparse positivity certificate. -/
theorem MERSENNE_QSQUARE_GIVES_CENTRAL_POSITIVITY
    (hQ : CofinalMersenneQSquareConstruction) :
    CofinalMersenneCentralPositive := by
  intro K
  rcases hQ K with ⟨k, hk, hka⟩
  refine ⟨k, hk, ?_⟩
  intro a ha
  rcases hka a ha with ⟨Q⟩
  exact Q.nonneg

/-- !!! Exact finite BKQR Q-squares on arbitrarily large Mersenne central cells
    are sufficient for RH, modulo only the separately printed analytic bindings. -/
theorem MERSENNE_QSQUARE_AND_CHANNEL_ANALYSIS_IMPLY_RH
    (hchannel : ActualOffLineChannelAnalysis)
    (hreg : AllPositiveXiRegular)
    (hQ : CofinalMersenneQSquareConstruction) :
    _root_.RiemannHypothesis :=
  MERSENNE_CENTRAL_POSITIVITY_AND_CHANNEL_ANALYSIS_IMPLY_RH
    hchannel hreg (MERSENNE_QSQUARE_GIVES_CENTRAL_POSITIVITY hQ)

/-- A weaker finite-approximation certificate: only nonnegative scalar
    approximants converging to the target central cell are required. -/
structure NonnegativeApproximation (x : ℝ) where
  value : ℕ → ℝ
  nonnegative : ∀ M : ℕ, 0 ≤ value M
  converges : Tendsto value atTop (𝓝 x)

/-- Closedness of [0,∞) passes positivity to the approximation limit. -/
theorem NonnegativeApproximation.nonneg {x : ℝ}
    (A : NonnegativeApproximation x) : 0 ≤ x := by
  exact ge_of_tendsto' A.converges A.nonnegative

/-- Weak finite BKQR frontier: convergence of nonnegative finite readouts only
    on a cofinal Mersenne subsequence. -/
def CofinalMersenneFiniteApproximation : Prop :=
  ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
    ∀ a : ℝ, 0 < a → Nonempty
      (NonnegativeApproximation (centralWidderMoment xiR (mersenneDepth k) a))

/-- Finite nonnegative approximants already imply sparse Mersenne positivity. -/
theorem MERSENNE_FINITE_APPROXIMATION_GIVES_CENTRAL_POSITIVITY
    (hA : CofinalMersenneFiniteApproximation) :
    CofinalMersenneCentralPositive := by
  intro K
  rcases hA K with ⟨k, hk, hka⟩
  refine ⟨k, hk, ?_⟩
  intro a ha
  rcases hka a ha with ⟨A⟩
  exact A.nonneg

/-- !!! Strongest finite construction anchor in this package:
    cofinally many Mersenne central cells need only be limits of nonnegative
    finite readouts. Full Hausdorff positivity and a global operator are not inputs. -/
theorem MERSENNE_FINITE_APPROXIMATION_AND_CHANNEL_ANALYSIS_IMPLY_RH
    (hchannel : ActualOffLineChannelAnalysis)
    (hreg : AllPositiveXiRegular)
    (hA : CofinalMersenneFiniteApproximation) :
    _root_.RiemannHypothesis :=
  MERSENNE_CENTRAL_POSITIVITY_AND_CHANNEL_ANALYSIS_IMPLY_RH
    hchannel hreg (MERSENNE_FINITE_APPROXIMATION_GIVES_CENTRAL_POSITIVITY hA)

end
end NativeSoloboloNegativity
