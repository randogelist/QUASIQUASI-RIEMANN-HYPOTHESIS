import AWPI.PhiRH.Final

/-!
# Native RH routes through the canonical AWPI scalar and tail frontiers

These wrappers preserve the explicit open hypothesis in each source route.
The canonical transverse jet is defined as a norm-square product in
`AWPI.PhiRH.CanonicalTransverseJet`; its identity is a concrete model choice.
It is not a formal identification with an independently defined historical
Phi derivative. The two binding scales are canonically chosen to be one.

Every RH conclusion below still needs its displayed positivity/upper-bound
premise. The equivalences themselves do not discharge those premises.
-/

namespace RHMaster

/-- Nonpositivity of the canonical exact plus defect at every nontrivial zero. -/
def AWPIPlusPassivity : Prop :=
  AWPI.PhiRH.ScalarConcreteFrontier.PlusPassivityCore

/-- The canonical exact plus defect is bounded by every squared KQ tail. -/
def AWPIExactTailUpper : Prop :=
  AWPI.PhiRH.CanonicalOneSidedTail.CanonicalPlusExactTailUpper

/-- Expose the literal scalar premise; no new analytic assumption is hidden. -/
theorem awpi_plus_passivity_def :
    AWPIPlusPassivity ↔
      ∀ rho : ℂ, AWPI.PhiRH.MathlibBridge.NontrivialZetaZero rho →
        AWPI.PhiRH.CanonicalOneSidedTail.canonicalPlusExactDefect rho ≤ 0 :=
  Iff.rfl

/-- Expose the literal exact-to-tail premise. -/
theorem awpi_exact_tail_upper_def :
    AWPIExactTailUpper ↔
      ∀ (n : ℕ) (rho : ℂ), AWPI.PhiRH.MathlibBridge.NontrivialZetaZero rho →
        AWPI.PhiRH.CanonicalOneSidedTail.canonicalPlusExactDefect rho ≤
          AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource n rho.re rho.im *
            AWPI.PhiRH.RocqSourceLayer.canonicalKQPlusSource n rho.re rho.im :=
  Iff.rfl

theorem awpi_plus_passivity_iff_rh :
    AWPIPlusPassivity ↔ _root_.RiemannHypothesis :=
  AWPI.PhiRH.ScalarConcreteFrontier.plusPassivityCore_iff_RiemannHypothesis

theorem awpi_exact_tail_upper_iff_rh :
    AWPIExactTailUpper ↔ _root_.RiemannHypothesis :=
  AWPI.PhiRH.CanonicalOneSidedTail.canonicalPlusExactTailUpper_iff_RiemannHypothesis

theorem rh_of_awpi_plus_passivity (h : AWPIPlusPassivity) :
    _root_.RiemannHypothesis :=
  awpi_plus_passivity_iff_rh.mp h

theorem rh_of_awpi_exact_tail_upper (h : AWPIExactTailUpper) :
    _root_.RiemannHypothesis :=
  awpi_exact_tail_upper_iff_rh.mp h

theorem awpi_exact_tail_upper_iff_plus_passivity :
    AWPIExactTailUpper ↔ AWPIPlusPassivity :=
  awpi_exact_tail_upper_iff_rh.trans awpi_plus_passivity_iff_rh.symm

end RHMaster
