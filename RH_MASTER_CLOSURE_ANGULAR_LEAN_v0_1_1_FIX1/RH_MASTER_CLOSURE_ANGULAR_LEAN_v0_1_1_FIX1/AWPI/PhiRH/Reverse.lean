import AWPI.PhiRH.Forward

namespace AWPI.PhiRH.Reverse

open AWPI.PhiRH

universe u v
variable {Point : Type u} {Jet : Type v}
variable {M : Model Point Jet}

/-- Internal v0.28 reverse step: B + RH makes both exact defects zero. -/
theorem BACKGROUND_AND_RH_GIVE_EXACT_TWO_SIDED_PASSIVITY
    (hB : Background M) (hRH : M.RH) : ExactTwoSidedPassivity M := by
  intro rho hz
  have hcrit : M.criticalLine rho := hRH rho hz
  have hgp : M.gainPlus rho = 1 := hB.criticalLineForwardGainOne rho hcrit
  have hgm : M.gainMinus rho = 1 := hB.criticalLineBackwardGainOne rho hcrit
  constructor
  · simp [Model.exactPlusDefect, hgp]
  · simp [Model.exactMinusDefect, hgm]

/-- Exact Rocq PHIRH290.  No imported facts are required: the canonical finite
    witnesses are zero and the actual tails are literal squares. -/
theorem PHIRH290_BACKGROUND_PLUS_PASSIVITY_GIVES_CANONICAL_CONSTRUCTOR
    (hB : Background M) (hP : ExactTwoSidedPassivity M) :
    SourceConstructor M
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
  refine
    { normalizedSourceFormula := hB.normalizedSourceFormula
      zeroInPositiveStrip := hB.zeroInPositiveStrip
      exactPlusActive := hB.exactPlusActive
      exactMinusActive := hB.exactMinusActive
      finitePlusNegativeSquare := ?_
      finiteMinusNegativeSquare := ?_
      plusToLimitTailUpper := ?_
      minusToLimitTailUpper := ?_ }
  · intro n rho hz
    norm_num
  · intro n rho hz
    norm_num
  · intro n rho hz
    have hdef : M.exactPlusDefect rho ≤ 0 := (hP rho hz).1
    have htail : 0 ≤ M.plusTail n rho :=
      Forward.PHIRH270_ACTUAL_PLUS_TAIL_NONNEGATIVE n rho
    linarith
  · intro n rho hz
    have hdef : M.exactMinusDefect rho ≤ 0 := (hP rho hz).2
    have htail : 0 ≤ M.minusTail n rho :=
      Forward.PHIRH271_ACTUAL_MINUS_TAIL_NONNEGATIVE n rho
    linarith

/-- Exact Rocq PHIRH291. -/
theorem PHIRH291_BACKGROUND_PLUS_PASSIVITY_GIVES_C
    (hB : Background M) (hP : ExactTwoSidedPassivity M) : Constructor M := by
  refine ⟨(fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0), ?_⟩
  exact PHIRH290_BACKGROUND_PLUS_PASSIVITY_GIVES_CANONICAL_CONSTRUCTOR hB hP

/-- v0.28 PHIRH287.  This now has exactly the guarded premises B and RH;
    no Lean-only Laws parameter remains. -/
theorem PHIRH287_BACKGROUND_AND_RH_IMPLIES_C
    (hB : Background M) (hRH : M.RH) : Constructor M := by
  have hP : ExactTwoSidedPassivity M :=
    BACKGROUND_AND_RH_GIVE_EXACT_TWO_SIDED_PASSIVITY hB hRH
  exact PHIRH291_BACKGROUND_PLUS_PASSIVITY_GIVES_C hB hP

/-- Exact Rocq PHIRH289.  Only imported PHIRH233 is needed. -/
theorem PHIRH289_C_IMPLIES_EXACT_TWO_SIDED_PASSIVITY
    (v23 : NormalizedDyadicMultiplierFacts M) (hC : Constructor M) :
    ExactTwoSidedPassivity M := by
  rcases hC with ⟨fdP, fdM, sqP, sqM, src⟩
  have cert : ActualTailCertificate M fdP fdM :=
    Forward.PHIRH275_POINTWISE_SOURCE_CONSTRUCTOR_GIVES_ACTUAL_TAIL_CERTIFICATE v23 src
  exact Forward.TAIL_CERTIFICATE_IMPLIES_EXACT_TWO_SIDED_PASSIVITY cert

/-- Exact Rocq PHIRH292. -/
theorem PHIRH292_C_IFF_BACKGROUND_AND_PASSIVITY
    (v23 : NormalizedDyadicMultiplierFacts M) (scale : Scale2Facts M) :
    Constructor M ↔ Background M ∧ ExactTwoSidedPassivity M := by
  constructor
  · intro hC
    exact ⟨Forward.PHIRH285_C_IMPLIES_B scale hC,
      PHIRH289_C_IMPLIES_EXACT_TWO_SIDED_PASSIVITY v23 hC⟩
  · intro h
    exact PHIRH291_BACKGROUND_PLUS_PASSIVITY_GIVES_C h.1 h.2

/-- Exact Rocq PHIRH293. -/
theorem PHIRH293_BACKGROUND_GIVES_C_IFF_PASSIVITY
    (v23 : NormalizedDyadicMultiplierFacts M) (hB : Background M) :
    Constructor M ↔ ExactTwoSidedPassivity M := by
  constructor
  · exact PHIRH289_C_IMPLIES_EXACT_TWO_SIDED_PASSIVITY v23
  · intro hP
    exact PHIRH291_BACKGROUND_PLUS_PASSIVITY_GIVES_C hB hP

/-- Exact Rocq PHIRH294. -/
theorem PHIRH294_B_TO_C_IFF_B_TO_PASSIVITY
    (v23 : NormalizedDyadicMultiplierFacts M) :
    (Background M → Constructor M) ↔
    (Background M → ExactTwoSidedPassivity M) := by
  constructor
  · intro hBC hB
    exact PHIRH289_C_IMPLIES_EXACT_TWO_SIDED_PASSIVITY v23 (hBC hB)
  · intro hBP hB
    exact PHIRH291_BACKGROUND_PLUS_PASSIVITY_GIVES_C hB (hBP hB)

/-- Exact Rocq PHIRH295. -/
theorem PHIRH295_B_TO_C_IFF_B_TO_RH
    (v23 : NormalizedDyadicMultiplierFacts M) (scale : Scale2Facts M) :
    (Background M → Constructor M) ↔ (Background M → M.RH) := by
  constructor
  · intro hBC hB
    exact Forward.PHIRH286_C_IMPLIES_RH v23 scale (hBC hB)
  · intro hBRH hB
    exact PHIRH287_BACKGROUND_AND_RH_IMPLIES_C hB (hBRH hB)

/-- Exact Rocq PHIRH296, with the same P->C->RH and RH->C->P factorization. -/
theorem PHIRH296_BACKGROUND_GIVES_PASSIVITY_IFF_RH
    (v23 : NormalizedDyadicMultiplierFacts M) (scale : Scale2Facts M)
    (hB : Background M) : ExactTwoSidedPassivity M ↔ M.RH := by
  constructor
  · intro hP
    exact Forward.PHIRH286_C_IMPLIES_RH v23 scale
      (PHIRH291_BACKGROUND_PLUS_PASSIVITY_GIVES_C hB hP)
  · intro hRH
    exact PHIRH289_C_IMPLIES_EXACT_TWO_SIDED_PASSIVITY v23
      (PHIRH287_BACKGROUND_AND_RH_IMPLIES_C hB hRH)

end AWPI.PhiRH.Reverse
