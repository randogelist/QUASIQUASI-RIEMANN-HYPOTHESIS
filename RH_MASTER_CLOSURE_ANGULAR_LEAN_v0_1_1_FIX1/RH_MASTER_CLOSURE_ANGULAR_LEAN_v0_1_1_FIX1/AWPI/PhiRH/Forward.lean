import AWPI.PhiRH.Geometry

namespace AWPI.PhiRH.Forward

open AWPI.PhiRH

universe u v
variable {Point : Type u} {Jet : Type v}
variable {M : Model Point Jet}

/-- Exact Rocq PHIRH270: actual KQ plus tail is a square. -/
theorem PHIRH270_ACTUAL_PLUS_TAIL_NONNEGATIVE
    (n : ℕ) (rho : Point) : 0 ≤ M.plusTail n rho := by
  simpa [Model.plusTail, pow_two] using sq_nonneg (M.plusTailSource n rho)

/-- Exact Rocq PHIRH271: actual KQ minus tail is a square. -/
theorem PHIRH271_ACTUAL_MINUS_TAIL_NONNEGATIVE
    (n : ℕ) (rho : Point) : 0 ≤ M.minusTail n rho := by
  simpa [Model.minusTail, pow_two] using sq_nonneg (M.minusTailSource n rho)

/-- Exact Lean port of Rocq PHIRH272. -/
theorem PHIRH272_NEGATIVE_SQUARE_GIVES_FINITE_PLUS_PASSIVITY
    {fdP fdM sqP sqM : ℕ → Point → ℝ}
    (src : SourceConstructor M fdP fdM sqP sqM)
    (n : ℕ) (rho : Point) (hz : M.isZero rho) : fdP n rho ≤ 0 := by
  have hsq : 0 ≤ (sqP n rho) ^ 2 := sq_nonneg (sqP n rho)
  have hid := src.finitePlusNegativeSquare n rho hz
  nlinarith

/-- Exact Lean port of Rocq PHIRH273. -/
theorem PHIRH273_NEGATIVE_SQUARE_GIVES_FINITE_MINUS_PASSIVITY
    {fdP fdM sqP sqM : ℕ → Point → ℝ}
    (src : SourceConstructor M fdP fdM sqP sqM)
    (n : ℕ) (rho : Point) (hz : M.isZero rho) : fdM n rho ≤ 0 := by
  have hsq : 0 ≤ (sqM n rho) ^ 2 := sq_nonneg (sqM n rho)
  have hid := src.finiteMinusNegativeSquare n rho hz
  nlinarith

/-- Exact Lean port of Rocq PHIRH274, depending only on imported v0.23 PHIRH233. -/
theorem PHIRH274_NORMALIZED_PHI_SOURCE_GIVES_ACTUAL_JOINT_TAIL_DECAY
    (v23 : NormalizedDyadicMultiplierFacts M)
    {fdP fdM sqP sqM : ℕ → Point → ℝ}
    (src : SourceConstructor M fdP fdM sqP sqM)
    (rho : Point) (eps : ℝ) (hz : M.isZero rho) (heps : 0 < eps) :
    ∃ n : ℕ, M.plusTail n rho ≤ eps ∧ M.minusTail n rho ≤ eps := by
  exact v23.PHIRH233_NORMALIZED_DYADIC_MULTIPLIER_SOURCE_GIVES_TAIL_DECAY
    src.normalizedSourceFormula src.zeroInPositiveStrip rho eps hz heps

/-- Exact Lean port of Rocq PHIRH275. -/
theorem PHIRH275_POINTWISE_SOURCE_CONSTRUCTOR_GIVES_ACTUAL_TAIL_CERTIFICATE
    (v23 : NormalizedDyadicMultiplierFacts M)
    {fdP fdM sqP sqM : ℕ → Point → ℝ}
    (src : SourceConstructor M fdP fdM sqP sqM) :
    ActualTailCertificate M fdP fdM := by
  refine
    { exactPlusActive := src.exactPlusActive
      exactMinusActive := src.exactMinusActive
      finitePlusPassive := ?_
      finiteMinusPassive := ?_
      plusTailNonnegative := PHIRH270_ACTUAL_PLUS_TAIL_NONNEGATIVE
      minusTailNonnegative := PHIRH271_ACTUAL_MINUS_TAIL_NONNEGATIVE
      plusToLimitTailUpper := src.plusToLimitTailUpper
      minusToLimitTailUpper := src.minusToLimitTailUpper
      jointTailDecay := ?_ }
  · intro n rho hz
    exact PHIRH272_NEGATIVE_SQUARE_GIVES_FINITE_PLUS_PASSIVITY src n rho hz
  · intro n rho hz
    exact PHIRH273_NEGATIVE_SQUARE_GIVES_FINITE_MINUS_PASSIVITY src n rho hz
  · intro rho eps hz heps
    exact PHIRH274_NORMALIZED_PHI_SOURCE_GIVES_ACTUAL_JOINT_TAIL_DECAY
      v23 src rho eps hz heps

/-- Analytic passivity extraction used inside the v0.24/v0.25 closure. -/
theorem TAIL_CERTIFICATE_IMPLIES_EXACT_TWO_SIDED_PASSIVITY
    {fdP fdM : ℕ → Point → ℝ}
    (cert : ActualTailCertificate M fdP fdM) : ExactTwoSidedPassivity M := by
  intro rho hz
  constructor
  · by_contra hnot
    have hpos : 0 < M.exactPlusDefect rho := lt_of_not_ge hnot
    have heps : 0 < M.exactPlusDefect rho / 2 := by linarith
    obtain ⟨n, htailP, _htailM⟩ :=
      cert.jointTailDecay rho (M.exactPlusDefect rho / 2) hz heps
    have hfinite : fdP n rho ≤ 0 := cert.finitePlusPassive n rho hz
    have hlimit := cert.plusToLimitTailUpper n rho hz
    linarith
  · by_contra hnot
    have hpos : 0 < M.exactMinusDefect rho := lt_of_not_ge hnot
    have heps : 0 < M.exactMinusDefect rho / 2 := by linarith
    obtain ⟨n, _htailP, htailM⟩ :=
      cert.jointTailDecay rho (M.exactMinusDefect rho / 2) hz heps
    have hfinite : fdM n rho ≤ 0 := cert.finiteMinusPassive n rho hz
    have hlimit := cert.minusToLimitTailUpper n rho hz
    linarith

private theorem plusGainLeOne
    (rho : Point) (hactive : 0 < M.exactPlusEnergy rho)
    (hpass : M.exactPlusDefect rho ≤ 0) : M.gainPlus rho ≤ 1 := by
  unfold Model.exactPlusDefect at hpass
  nlinarith

private theorem minusGainLeOne
    (rho : Point) (hactive : 0 < M.exactMinusEnergy rho)
    (hpass : M.exactMinusDefect rho ≤ 0) : M.gainMinus rho ≤ 1 := by
  unfold Model.exactMinusDefect at hpass
  nlinarith

/-- Lean counterpart of imported Rocq A25.PHIRH264, now using the explicit
    v0.24 scalar theorem chain instead of generic Laws fields. -/
theorem PHIRH264_ACTUAL_POINTWISE_KQ_TAIL_CERTIFICATE_IMPLIES_RH
    (scale : Scale2Facts M)
    {fdP fdM : ℕ → Point → ℝ}
    (cert : ActualTailCertificate M fdP fdM) : M.RH := by
  intro rho hz
  have hp := TAIL_CERTIFICATE_IMPLIES_EXACT_TWO_SIDED_PASSIVITY cert rho hz
  have hgp : M.gainPlus rho ≤ 1 :=
    plusGainLeOne rho (cert.exactPlusActive rho hz) hp.1
  have hgm : M.gainMinus rho ≤ 1 :=
    minusGainLeOne rho (cert.exactMinusActive rho hz) hp.2
  have hle : M.centered rho ≤ 0 :=
    Geometry.FORWARD_GAIN_LE_ONE_IMPLIES_CENTERED_NONPOSITIVE scale rho hgp
  have hge : 0 ≤ M.centered rho :=
    Geometry.BACKWARD_GAIN_LE_ONE_IMPLIES_CENTERED_NONNEGATIVE scale rho hgm
  have hzero : M.centered rho = 0 := le_antisymm hle hge
  exact (Geometry.PHIRH240_CENTERED_ZERO_IFF_CRITICAL_LINE rho).1 hzero

/-- Exact Lean port of Rocq PHIRH276. -/
theorem PHIRH276_ACTUAL_POINTWISE_SOURCE_CONSTRUCTOR_IMPLIES_RH
    (v23 : NormalizedDyadicMultiplierFacts M) (scale : Scale2Facts M)
    {fdP fdM sqP sqM : ℕ → Point → ℝ}
    (src : SourceConstructor M fdP fdM sqP sqM) : M.RH := by
  apply PHIRH264_ACTUAL_POINTWISE_KQ_TAIL_CERTIFICATE_IMPLIES_RH scale
  exact PHIRH275_POINTWISE_SOURCE_CONSTRUCTOR_GIVES_ACTUAL_TAIL_CERTIFICATE v23 src

/-- v0.28 PHIRH285.  The gain-neutrality fields of B are now proved from
    PHIRH240/242 rather than injected through Laws. -/
theorem PHIRH285_C_IMPLIES_B
    (scale : Scale2Facts M) (hC : Constructor M) : Background M := by
  rcases hC with ⟨fdP, fdM, sqP, sqM, src⟩
  exact
    { normalizedSourceFormula := src.normalizedSourceFormula
      zeroInPositiveStrip := src.zeroInPositiveStrip
      exactPlusActive := src.exactPlusActive
      exactMinusActive := src.exactMinusActive
      criticalLineForwardGainOne :=
        Geometry.PHIRH283_CRITICAL_LINE_GIVES_FORWARD_GAIN_ONE scale
      criticalLineBackwardGainOne :=
        Geometry.PHIRH284_CRITICAL_LINE_GIVES_BACKWARD_GAIN_ONE scale }

/-- v0.28 PHIRH286. -/
theorem PHIRH286_C_IMPLIES_RH
    (v23 : NormalizedDyadicMultiplierFacts M) (scale : Scale2Facts M)
    (hC : Constructor M) : M.RH := by
  rcases hC with ⟨fdP, fdM, sqP, sqM, src⟩
  exact PHIRH276_ACTUAL_POINTWISE_SOURCE_CONSTRUCTOR_IMPLIES_RH v23 scale src

end AWPI.PhiRH.Forward
