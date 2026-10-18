import Derivations.Widder.DirectTower
import Bridge.XiChannelNegativity

namespace NativeSoloboloNegativity

open Filter
open scoped Topology

noncomputable section

/-- The pole-removed centered xi slice is real analytic on the entire real axis. -/
theorem XI_REAL_SLICE_ANALYTIC (x : ℝ) : AnalyticAt ℝ xiRealSlice x := by
  -- MERGER05_XI_REAL_SLICE_PROOF_REVISION=V0_21_5_FIX5
  have hcomplex : AnalyticAt ℂ xiEntire ((1 / 2 : ℂ) + (x : ℂ)) :=
    XI_ENTIRE_DIFFERENTIABLE.analyticAt _
  have hreal : AnalyticAt ℝ xiEntire ((1 / 2 : ℂ) + (x : ℂ)) :=
    hcomplex.restrictScalars
  have hshift : AnalyticAt ℝ (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) x :=
    analyticAt_const.add (Complex.ofRealCLM.analyticAt x)
  have hcomp : AnalyticAt ℝ
      (fun t : ℝ => xiEntire ((1 / 2 : ℂ) + (t : ℂ))) x := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp
        (𝕜 := ℝ) (E := ℝ) (F := ℂ) (G := ℂ)
        (g := xiEntire)
        (f := fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ))
        (x := x) hreal hshift)
  -- First prove analyticity for the literal bundled-projection function.
  have hprojected : AnalyticAt ℝ
      (fun t : ℝ => Complex.reCLM (xiEntire ((1 / 2 : ℂ) + (t : ℂ)))) x :=
    AnalyticAt.comp
      (𝕜 := ℝ) (E := ℝ) (F := ℂ) (G := ℝ)
      (g := (Complex.reCLM : ℂ → ℝ))
      (f := fun t : ℝ => xiEntire ((1 / 2 : ℂ) + (t : ℂ)))
      (x := x)
      (Complex.reCLM.analyticAt (xiEntire ((1 / 2 : ℂ) + (x : ℂ))))
      hcomp
  -- Identify whole functions before transporting the analytic proposition.
  have hprojection_eq_slice :
      (fun t : ℝ => Complex.reCLM (xiEntire ((1 / 2 : ℂ) + (t : ℂ)))) =
        xiRealSlice := by
    funext t
    change Complex.reCLM (xiEntire ((1 / 2 : ℂ) + (t : ℂ))) =
      (xiEntire ((1 / 2 : ℂ) + (t : ℂ))).re
    exact Complex.reCLM_apply _
  exact Eq.mp
    (congrArg (fun g : ℝ → ℝ => AnalyticAt ℝ g x) hprojection_eq_slice)
    hprojected

/-- This set makes the denominator needed for xiR explicit.
    Membership is not a positivity or zero-location assumption. -/
def xiRegularAnchors : Set ℝ :=
  {a : ℝ | 0 < a ∧ xiRealSlice (Real.sqrt a) ≠ 0}

theorem XI_REGULAR_ANCHORS_OPEN : IsOpen xiRegularAnchors := by
  have hslice : Continuous xiRealSlice :=
    continuous_iff_continuousAt.mpr (fun x => (XI_REAL_SLICE_ANALYTIC x).continuousAt)
  have hcomp : Continuous (fun a : ℝ => xiRealSlice (Real.sqrt a)) :=
    hslice.comp Real.continuous_sqrt
  change IsOpen (Set.Ioi (0 : ℝ) ∩
    (fun a : ℝ => xiRealSlice (Real.sqrt a)) ⁻¹' ({0} : Set ℝ)ᶜ)
  exact isOpen_Ioi.inter (hcomp.isOpen_preimage _ isClosed_singleton.isOpen_compl)

/-- Local regularity of the literal R-channel follows from the actual xi slice,
    the square root, and the displayed nonzero denominator. -/
theorem XI_R_ANALYTIC_AT (a : ℝ) (ha : 0 < a)
    (hF : xiRealSlice (Real.sqrt a) ≠ 0) : AnalyticAt ℝ xiR a := by
  have hsmooth : ContDiffAt ℝ ⊤ Real.sqrt a :=
    Real.contDiffAt_sqrt (ne_of_gt ha)
  have hsqrt : AnalyticAt ℝ Real.sqrt a := hsmooth.analyticAt
  have hslice := XI_REAL_SLICE_ANALYTIC (Real.sqrt a)
  have hnum : AnalyticAt ℝ (fun t : ℝ => deriv xiRealSlice (Real.sqrt t)) a := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp
        (𝕜 := ℝ) (E := ℝ) (F := ℝ) (G := ℝ)
        (g := deriv xiRealSlice) (f := Real.sqrt) (x := a)
        hslice.deriv hsqrt)
  have hvalue : AnalyticAt ℝ (fun t : ℝ => xiRealSlice (Real.sqrt t)) a := by
    simpa only [Function.comp_def] using
      (AnalyticAt.comp
        (𝕜 := ℝ) (E := ℝ) (F := ℝ) (G := ℝ)
        (g := xiRealSlice) (f := Real.sqrt) (x := a)
        hslice hsqrt)
  have hden : AnalyticAt ℝ
      (fun t : ℝ => 2 * Real.sqrt t * xiRealSlice (Real.sqrt t)) a :=
    (analyticAt_const.mul hsqrt).mul hvalue
  have hden0 : 2 * Real.sqrt a * xiRealSlice (Real.sqrt a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr ha))) hF
  change AnalyticAt ℝ
    (fun t : ℝ => deriv xiRealSlice (Real.sqrt t) /
      (2 * Real.sqrt t * xiRealSlice (Real.sqrt t))) a
  exact hnum.div hden hden0

theorem XI_R_ANALYTIC_ON_REGULAR_ANCHORS :
    AnalyticOnNhd ℝ xiR xiRegularAnchors := by
  intro a ha
  exact XI_R_ANALYTIC_AT a ha.1 ha.2

/-- The factored generic direct formula is literally the existing xiWidderDirect. -/
theorem XI_DIRECT_SCALED_EQ_DIRECT (a : ℝ) (n : ℕ) :
    widderDirectScaled xiR n a = xiWidderDirect a n :=
  WIDDER_DIRECT_SCALED_EQ_FORMULA xiR n a

/-- Main all-depth identification on the explicit actual analytic domain.
    This does not redefine the direct expression to be the recursive tower. -/
theorem XI_WIDDER_DIRECT_EQ_RECURSIVE_ON_REGULAR_ANCHORS
    (a : ℝ) (ha : a ∈ xiRegularAnchors) (n : ℕ) :
    xiWidderDirect a n = xiWidderMoment a n := by
  rw [← XI_DIRECT_SCALED_EQ_DIRECT a n]
  exact WIDDER_DIRECT_EQUALS_TOWER_ON_OPEN
    XI_REGULAR_ANCHORS_OPEN XI_R_ANALYTIC_ON_REGULAR_ANCHORS n ha

/-- Same theorem with the exact local assumptions displayed at the call site. -/
theorem XI_WIDDER_DIRECT_EQ_RECURSIVE
    (a : ℝ) (ha : 0 < a) (hF : xiRealSlice (Real.sqrt a) ≠ 0) (n : ℕ) :
    xiWidderDirect a n = xiWidderMoment a n :=
  XI_WIDDER_DIRECT_EQ_RECURSIVE_ON_REGULAR_ANCHORS a ⟨ha, hF⟩ n

/-- The normalization-sensitive anchor a=1/4 is included, with no nonvanishing
    input: the repaired entire xi has the exact value 1/2 there. -/
theorem XI_QUARTER_ANCHOR_REGULAR : (1 / 4 : ℝ) ∈ xiRegularAnchors := by
  have hs : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    calc
      Real.sqrt (1 / 4 : ℝ) = Real.sqrt ((1 / 2 : ℝ)^2) := by norm_num
      _ = |(1 / 2 : ℝ)| := Real.sqrt_sq_eq_abs _
      _ = 1 / 2 := by norm_num
  change 0 < (1 / 4 : ℝ) ∧ xiRealSlice (Real.sqrt (1 / 4 : ℝ)) ≠ 0
  rw [hs, XI_REAL_SLICE_HALF]
  norm_num

theorem XI_WIDDER_DIRECT_EQ_RECURSIVE_AT_QUARTER (n : ℕ) :
    xiWidderDirect (1 / 4) n = xiWidderMoment (1 / 4) n :=
  XI_WIDDER_DIRECT_EQ_RECURSIVE_ON_REGULAR_ANCHORS
    (1 / 4) XI_QUARTER_ANCHOR_REGULAR n

/-- No new spectral input: channel data transport along eventual equality
    of the moment values at the same supplied moving anchors. -/
def ChannelPeakData.transferMoments
    {mu nu : ℝ → ℕ → ℝ} (P : ChannelPeakData mu)
    (heq : ∀ᶠ n : ℕ in atTop, mu (P.anchor n) n = nu (P.anchor n) n) :
    ChannelPeakData nu where
  headCount := P.headCount
  headPoint := P.headPoint
  headMultiplicity := P.headMultiplicity
  headMassPositive := P.headMassPositive
  tailPoint := P.tailPoint
  tailMultiplicity := P.tailMultiplicity
  tailMultiplicityPositive := P.tailMultiplicityPositive
  baseAnchor := P.baseAnchor
  anchor := P.anchor
  anchorLimit := P.anchorLimit
  anchorPositive := P.anchorPositive
  amplitude := P.amplitude
  peak := P.peak
  peakAboveOne := P.peakAboveOne
  tailNoPoleAtBase := P.tailNoPoleAtBase
  tailStrictAtBase := P.tailStrictAtBase
  amplitudeLimit := P.amplitudeLimit
  envelope := P.envelope
  envelopeNonnegative := P.envelopeNonnegative
  envelopeSummable := P.envelopeSummable
  tailEnvelope := P.tailEnvelope
  headPhase := P.headPhase
  reconstruction := by
    filter_upwards [P.reconstruction, heq] with n hrec hsame
    rw [← hsame]
    exact hrec

/-- Thus the Hadamard/channel expansion may now be proved for the direct
    derivative formula, then transported to the already-passing negativity layer. -/
def directPeakDataToRecursive
    (P : ChannelPeakData xiWidderDirect)
    (hreg : ∀ᶠ n : ℕ in atTop, P.anchor n ∈ xiRegularAnchors) :
    ActualXiPeakData :=
  P.transferMoments (by
    filter_upwards [hreg] with n hn
    exact XI_WIDDER_DIRECT_EQ_RECURSIVE_ON_REGULAR_ANCHORS (P.anchor n) hn n)

theorem DIRECT_XI_PEAK_DATA_IMPLY_EVENTUAL_NEGATIVITY
    (P : ChannelPeakData xiWidderDirect)
    (hreg : ∀ᶠ n : ℕ in atTop, P.anchor n ∈ xiRegularAnchors) :
    EventuallyDepthNegative :=
  ACTUAL_XI_PEAK_DATA_IMPLY_EVENTUAL_NEGATIVITY (directPeakDataToRecursive P hreg)

/-- Openness plus the packet's anchor limit supplies eventual regularity from
    one explicit regular base anchor. -/
theorem DIRECT_PEAK_DATA_REGULAR_BASE_EVENTUAL_NEGATIVITY
    (P : ChannelPeakData xiWidderDirect) (hbase : P.baseAnchor ∈ xiRegularAnchors) :
    EventuallyDepthNegative := by
  have hreg : ∀ᶠ n : ℕ in atTop, P.anchor n ∈ xiRegularAnchors :=
    P.anchorLimit.eventually (XI_REGULAR_ANCHORS_OPEN.mem_nhds hbase)
  exact DIRECT_XI_PEAK_DATA_IMPLY_EVENTUAL_NEGATIVITY P hreg

end
end NativeSoloboloNegativity
