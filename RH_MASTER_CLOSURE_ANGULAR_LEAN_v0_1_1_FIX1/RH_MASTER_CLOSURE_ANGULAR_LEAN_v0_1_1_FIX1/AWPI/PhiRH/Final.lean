import AWPI.PhiRH.ScalarConcreteFrontier

/-!
# AWPI Phi/RH final portable surface (v0.2.16)

This module exports the final kernel-checked scalar normal form over Mathlib's
native `RiemannHypothesis` proposition.

It does **not** assert RH unconditionally.  It proves the exact equivalence
between the explicit project proposition `PlusPassivityCore` and Mathlib RH.
-/

namespace AWPI.PhiRH.Final

open AWPI.PhiRH

/-- Final explicit scalar proposition. -/
abbrev PlusPassivityCore : Prop :=
  ScalarConcreteFrontier.PlusPassivityCore

/-- PlusPassivityCore implies Mathlib's native Riemann Hypothesis. -/
theorem riemannHypothesis_of_plusPassivityCore
    (h : PlusPassivityCore) : RiemannHypothesis :=
  ScalarConcreteFrontier.MATHLIB_RH_OF_PLUS_PASSIVITY_CORE h

/-- Mathlib's native Riemann Hypothesis implies PlusPassivityCore. -/
theorem plusPassivityCore_of_riemannHypothesis
    (h : RiemannHypothesis) : PlusPassivityCore :=
  ScalarConcreteFrontier.plusPassivityCore_of_RH h

/-- Final scalar normal form: PlusPassivityCore is logically equivalent to
Mathlib's native Riemann Hypothesis. -/
theorem plusPassivityCore_iff_riemannHypothesis :
    PlusPassivityCore ↔ RiemannHypothesis :=
  ScalarConcreteFrontier.plusPassivityCore_iff_RiemannHypothesis

end AWPI.PhiRH.Final
