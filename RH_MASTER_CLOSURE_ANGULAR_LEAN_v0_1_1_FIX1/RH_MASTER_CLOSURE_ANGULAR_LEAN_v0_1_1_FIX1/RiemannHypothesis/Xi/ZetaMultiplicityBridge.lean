/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.Xi.CanonicalDivisor
import RiemannHypothesis.Xi.RiemannHypothesisBridge

/-!
# Exact multiplicity across the centered xi--zeta correspondence

This module combines two unconditional local facts:

* the affine map `z ↦ 1 / 2 + I * z` preserves analytic order; and
* at every zero of `entireRiemannXi`, the entire xi function is locally a
  nonvanishing analytic unit times `riemannZeta`.

Consequently, each canonical pullback-zero occurrence has exactly the
analytic multiplicity used by the corresponding zeta zero count.  No
xi-specific zero-distribution or Hadamard-product package is assumed.
-/

namespace OverflowResidueRH

/-- At a zero of the centered pullback, analytic order is exactly the order
of `riemannZeta` at the corresponding point `1 / 2 + I * z`. -/
theorem entireXiPullback_analyticOrderAt_eq_riemannZeta_of_zero
    {z : ℂ} (hz : EntireXiPullback z = 0) :
    analyticOrderAt EntireXiPullback z =
      analyticOrderAt riemannZeta
        ((1 / 2 : ℂ) + Complex.I * z) :=
  (entireXiPullback_analyticOrderAt_eq_entireRiemannXi z).trans
    (entireRiemannXi_analyticOrderAt_eq_riemannZeta_of_zero hz)

/-- Natural-number form of exact pullback--zeta multiplicity preservation. -/
theorem entireXiPullback_analyticOrderNatAt_eq_riemannZeta_of_zero
    {z : ℂ} (hz : EntireXiPullback z = 0) :
    analyticOrderNatAt EntireXiPullback z =
      analyticOrderNatAt riemannZeta
        ((1 / 2 : ℂ) + Complex.I * z) :=
  congrArg ENat.toNat
    (entireXiPullback_analyticOrderAt_eq_riemannZeta_of_zero hz)

/-- The canonical occurrence fiber over a nonzero pullback zero has cardinal
equal to the analytic multiplicity of the corresponding zeta zero.  This is
the precise local bridge needed by multiplicity-weighted height counts. -/
theorem entireXiPullbackZeroOccurrence_fiber_natCard_eq_riemannZeta_order
    (z : EntireXiPullbackNonzeroZero) :
    Nat.card {i : EntireXiPullbackZeroOccurrence // i.1 = z} =
      analyticOrderNatAt riemannZeta
        ((1 / 2 : ℂ) + Complex.I * z.1) :=
  (entireXiPullbackZeroOccurrence_fiber_natCard z).trans
    (entireXiPullback_analyticOrderNatAt_eq_riemannZeta_of_zero z.2.1)

end OverflowResidueRH
