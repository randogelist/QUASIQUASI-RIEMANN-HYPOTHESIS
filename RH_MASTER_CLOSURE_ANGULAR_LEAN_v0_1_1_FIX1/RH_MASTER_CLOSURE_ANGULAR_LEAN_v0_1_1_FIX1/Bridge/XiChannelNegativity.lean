import Core.EntireXiWidder
import Derivations.Negativity.UniformChannelBounds
import Derivations.Negativity.GeometricDominance
import Derivations.Negativity.UniformGap
import Derivations.Negativity.TunedChannelAlgebra

namespace NativeSoloboloNegativity

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Explicit spectral inputs for a real moment family.

This structure does NOT contain an eventual-negativity conclusion, a positive
moment hypothesis, or RH. It exposes the unresolved analytic work:
  * exact reconstruction of the given moments by literal Cayley channels;
  * a finite cluster whose channel phases are tuned;
  * a summable first-power envelope and pointwise strictness at the limit anchor.

The envelope is for the countably infinite complement of the finite cluster.
A,B eta^N is not a field: the package derives that bound from the envelope.
-/
structure ChannelPeakData (mu : ℝ → ℕ → ℝ) where
  headCount : ℕ
  headPoint : Fin headCount → ℂ
  headMultiplicity : Fin headCount → ℕ
  headMassPositive : 0 < ∑ i : Fin headCount, (headMultiplicity i : ℝ)
  tailPoint : ℕ → ℂ
  tailMultiplicity : ℕ → ℕ
  tailMultiplicityPositive : ∀ j, 0 < tailMultiplicity j
  baseAnchor : ℝ
  anchor : ℕ → ℝ
  anchorLimit : Tendsto anchor atTop (𝓝 baseAnchor)
  anchorPositive : ∀ᶠ n : ℕ in atTop, 0 < anchor n
  amplitude : ℕ → ℝ
  peak : ℝ
  peakAboveOne : 1 < peak
  tailNoPoleAtBase : ∀ j, (baseAnchor : ℂ) + tailPoint j ≠ 0
  tailStrictAtBase : ∀ j, ‖channelQ baseAnchor (tailPoint j)‖ < peak
  amplitudeLimit : Tendsto amplitude atTop (𝓝 peak)
  envelope : ℕ → ℝ
  envelopeNonnegative : ∀ j, 0 ≤ envelope j
  envelopeSummable : Summable envelope
  tailEnvelope : ∀ n j : ℕ,
    (tailMultiplicity j : ℝ) * ‖channelQ (anchor n) (tailPoint j)‖ ≤ envelope j
  headPhase : ∀ᶠ n : ℕ in atTop, ∀ i : Fin headCount,
    channelQ (anchor n) (headPoint i) ^ (n + 1) =
      -((amplitude n ^ (n + 1) : ℝ) : ℂ)
  reconstruction : ∀ᶠ n : ℕ in atTop,
    (mu (anchor n) n : ℂ) =
      (∑ i : Fin headCount,
        (headMultiplicity i : ℂ) * channelQ (anchor n) (headPoint i) ^ (n + 1)) +
      ∑' j : ℕ,
        (tailMultiplicity j : ℂ) * channelQ (anchor n) (tailPoint j) ^ (n + 1)

/-- The uniform strict spectral gap follows from pointwise strictness,
    continuity of the literal rational channel, and a summable envelope. -/
theorem PEAK_DATA_HAVE_UNIFORM_GAP
    {mu : ℝ → ℕ → ℝ} (P : ChannelPeakData mu) :
    ∃ eta : ℝ, 0 ≤ eta ∧ eta < P.peak ∧
      ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
        ‖channelQ (P.anchor n) (P.tailPoint j)‖ ≤ eta := by
  have hlim : ∀ j : ℕ,
      Tendsto (fun n => ‖channelQ (P.anchor n) (P.tailPoint j)‖) atTop
        (𝓝 ‖channelQ P.baseAnchor (P.tailPoint j)‖) := by
    intro j
    have hd : ((P.baseAnchor : ℂ) + P.tailPoint j) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (P.tailNoPoleAtBase j)
    have hc : ContinuousAt
        (fun a : ℝ => ‖channelQ a (P.tailPoint j)‖) P.baseAnchor := by
      unfold channelQ NativeSolobolo.Derivations.Geometry.cayleyChannelQ
      fun_prop
    exact hc.tendsto.comp P.anchorLimit
  have he : ∀ n j : ℕ,
      ‖channelQ (P.anchor n) (P.tailPoint j)‖ ≤ P.envelope j := by
    intro n j
    have hwNat : 1 ≤ P.tailMultiplicity j := P.tailMultiplicityPositive j
    have hw : (1 : ℝ) ≤ (P.tailMultiplicity j : ℝ) := by
      exact_mod_cast hwNat
    have hmul := mul_le_mul_of_nonneg_right hw
      (norm_nonneg (channelQ (P.anchor n) (P.tailPoint j)))
    exact le_trans (by simpa using hmul) (P.tailEnvelope n j)
  exact UNIFORM_GAP_FROM_VANISHING_ENVELOPE
    (fun n j => ‖channelQ (P.anchor n) (P.tailPoint j)‖)
    (fun j => ‖channelQ P.baseAnchor (P.tailPoint j)‖)
    P.envelope P.peak (by linarith [P.peakAboveOne]) hlim
    P.tailStrictAtBase he P.envelopeSummable.tendsto_atTop_zero

/-- The infinite remainder has the advertised bound B eta^n. -/
theorem PEAK_DATA_REMAINDER_BOUND
    {mu : ℝ → ℕ → ℝ} (P : ChannelPeakData mu) (eta : ℝ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      ‖channelQ (P.anchor n) (P.tailPoint j)‖ ≤ eta) :
    ∀ᶠ n : ℕ in atTop,
      Summable (fun j : ℕ =>
        (P.tailMultiplicity j : ℂ) *
          channelQ (P.anchor n) (P.tailPoint j) ^ (n + 1)) ∧
      ‖∑' j : ℕ, (P.tailMultiplicity j : ℂ) *
          channelQ (P.anchor n) (P.tailPoint j) ^ (n + 1)‖ ≤
        (∑' j : ℕ, P.envelope j) * eta ^ n := by
  filter_upwards [hgap] with n hn
  simpa using SUMMABLE_CHANNEL_POWER_REMAINDER_BOUND
    (fun j : ℕ => (P.tailMultiplicity j : ℝ))
    (fun j : ℕ => channelQ (P.anchor n) (P.tailPoint j))
    P.envelope eta n (by intro j; positivity)
    P.envelopeNonnegative P.envelopeSummable hn (P.tailEnvelope n)

/-- The finite cluster and infinite tail combine into a quantitative inequality. -/
theorem PEAK_DATA_MOMENT_UPPER_BOUND
    {mu : ℝ → ℕ → ℝ} (P : ChannelPeakData mu) (eta : ℝ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      ‖channelQ (P.anchor n) (P.tailPoint j)‖ ≤ eta) :
    ∀ᶠ n : ℕ in atTop,
      mu (P.anchor n) n ≤
        -(∑ i : Fin P.headCount, (P.headMultiplicity i : ℝ)) *
          P.amplitude n ^ (n + 1) +
        (∑' j : ℕ, P.envelope j) * eta ^ n := by
  filter_upwards [P.reconstruction, P.headPhase, PEAK_DATA_REMAINDER_BOUND P eta hgap]
    with n hrec hphase hrem
  let A : ℝ := ∑ i : Fin P.headCount, (P.headMultiplicity i : ℝ)
  let tail : ℂ := ∑' j : ℕ, (P.tailMultiplicity j : ℂ) *
    channelQ (P.anchor n) (P.tailPoint j) ^ (n + 1)
  have hhead :
      (∑ i : Fin P.headCount,
        (P.headMultiplicity i : ℂ) * channelQ (P.anchor n) (P.headPoint i) ^ (n + 1)) =
        -((A * P.amplitude n ^ (n + 1) : ℝ) : ℂ) := by
    simpa [A] using FINITE_CLUSTER_REINFORCES Finset.univ
      (fun i : Fin P.headCount => (P.headMultiplicity i : ℝ))
      (fun i : Fin P.headCount => channelQ (P.anchor n) (P.headPoint i))
      (P.amplitude n) n (fun i _ => hphase i)
  have hre : tail.re ≤ (∑' j : ℕ, P.envelope j) * eta ^ n := by
    exact le_trans (le_trans (le_abs_self tail.re) (Complex.abs_re_le_norm tail)) hrem.2
  have heq : mu (P.anchor n) n = -A * P.amplitude n ^ (n + 1) + tail.re := by
    have hh := congrArg Complex.re (hrec.trans (congrArg (fun z : ℂ => z + tail) hhead))
    -- Keep the cast around the whole real amplitude while taking its real part.
    -- Unrestricted simplification would instead push that cast into the power.
    simpa only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, neg_mul] using hh
  change mu (P.anchor n) n ≤ -A * P.amplitude n ^ (n + 1) + _
  rw [heq]
  -- Add the same cluster contribution on both sides, in the goal's order.
  exact add_le_add (le_refl (-A * P.amplitude n ^ (n + 1))) hre

/-- The complete dominance argument. All sufficiently large depths have
    a negative moment at the moving anchor. -/
theorem PEAK_DATA_GIVE_EVENTUAL_NEGATIVE_ANCHORS
    {mu : ℝ → ℕ → ℝ} (P : ChannelPeakData mu) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      ∃ a : ℝ, 0 < a ∧ mu a n < 0 := by
  rcases PEAK_DATA_HAVE_UNIFORM_GAP P with ⟨eta, he0, hePeak, heGap⟩
  have hnegative : ∀ᶠ n : ℕ in atTop, mu (P.anchor n) n < 0 :=
    NEGATIVE_CLUSTER_FROM_AMPLITUDE_LIMIT
      (fun n => mu (P.anchor n) n) P.amplitude
      (∑ i : Fin P.headCount, (P.headMultiplicity i : ℝ))
      (∑' j : ℕ, P.envelope j) eta P.peak
      P.headMassPositive he0 hePeak P.amplitudeLimit
      (PEAK_DATA_MOMENT_UPPER_BOUND P eta heGap)
  have hev : ∀ᶠ n : ℕ in atTop, ∃ a : ℝ, 0 < a ∧ mu a n < 0 := by
    filter_upwards [P.anchorPositive, hnegative] with n hn hp
    exact ⟨P.anchor n, hn, hp⟩
  exact Filter.eventually_atTop.1 hev

/-- Specialization to the repaired, actually defined xi-Widder sequence. -/
abbrev ActualXiPeakData := ChannelPeakData xiWidderMoment

theorem ACTUAL_XI_PEAK_DATA_IMPLY_EVENTUAL_NEGATIVITY
    (P : ActualXiPeakData) : EventuallyDepthNegative :=
  PEAK_DATA_GIVE_EVENTUAL_NEGATIVE_ANCHORS P

/-- This is an explicitly OPEN analytic binding, not a project axiom.
To prove it one must establish the actual zero expansion, maximal-cluster
selection, a summable compact-anchor envelope, and exact phase tuning for the repaired xi moments.
It is deliberately printed in the top-level theorem's hypothesis list. -/
def ActualOffLineChannelAnalysis : Prop :=
  ¬ _root_.RiemannHypothesis → Nonempty ActualXiPeakData

/-- The old eventual-negativity input is derived from lower-level spectral
    data, but construction of those data for actual xi remains explicit. -/
theorem OFFLINE_CHANNEL_ANALYSIS_IMPLIES_EVENTUAL_NEGATIVITY
    (hchannel : ActualOffLineChannelAnalysis) :
    ¬ _root_.RiemannHypothesis → EventuallyDepthNegative := by
  intro hnot
  rcases hchannel hnot with ⟨P⟩
  exact ACTUAL_XI_PEAK_DATA_IMPLY_EVENTUAL_NEGATIVITY P

/-- Conditional Mathlib-RH closure. No standalone RH proof is claimed. -/
theorem COFINAL_POSITIVITY_AND_CHANNEL_ANALYSIS_IMPLY_RH
    (hchannel : ActualOffLineChannelAnalysis)
    (hpositive : CofinalUniformDepthPositive) :
    _root_.RiemannHypothesis := by
  by_contra hnot
  exact COFINAL_POSITIVITY_EXCLUDES_EVENTUAL_NEGATIVITY hpositive
    (OFFLINE_CHANNEL_ANALYSIS_IMPLIES_EVENTUAL_NEGATIVITY hchannel hnot)

end
end NativeSoloboloNegativity
