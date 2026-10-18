import TaylorProdigy
import Lean.Util.CollectAxioms

open Lean Elab Command

#print RiemannHypothesis
#print AWPIRH.xi
#print AWPIRH.theta
#print TaylorsProdigy.H
#print TaylorsProdigy.F
#print TaylorsProdigy.TAYLORS_PRODIGY_PREMISE
#check TaylorsProdigy.positive_of_integrable_relative_decay
#check TaylorsProdigy.lower_bound_of_integrable_relative_decay
#check TaylorsProdigy.deriv_F
#check TaylorsProdigy.F_positive_propagates
#check TaylorsProdigy.actual_no_zero_on_interior_circle
#check TaylorsProdigy.actual_theta_no_zero_interior_of_premise
#check TaylorsProdigy.theta_zeros_nonpositive_of_premise
#check TaylorsProdigy.native_RH_of_TAYLORS_PRODIGY_PREMISE
#check TaylorsProdigy.relative_decay_rate_of_positive_extension
#check TaylorsProdigy.TAYLORS_PRODIGY_PREMISE_of_native_RH
#check TaylorsProdigy.TAYLORS_PRODIGY_PREMISE_iff_RH

example : TaylorsProdigy.TAYLORS_PRODIGY_PREMISE → RiemannHypothesis :=
  TaylorsProdigy.native_RH_of_TAYLORS_PRODIGY_PREMISE

example : RiemannHypothesis → TaylorsProdigy.TAYLORS_PRODIGY_PREMISE :=
  TaylorsProdigy.TAYLORS_PRODIGY_PREMISE_of_native_RH

example : TaylorsProdigy.TAYLORS_PRODIGY_PREMISE ↔ RiemannHypothesis :=
  TaylorsProdigy.TAYLORS_PRODIGY_PREMISE_iff_RH

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[`TaylorsProdigy, `_private.TaylorProdigy]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := env.constants.toList.filterMap fun (name, _) =>
    if roots.any (fun root => root.isPrefixOf name) then some name else none
  for name in declarations do
    let dependencies ← Lean.collectAxioms name
    logInfo m!"AXIOM_DEPENDENCIES {name}: {dependencies}"
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError m!"UNAPPROVED_DEPENDENCY {name}: {dependency}"
  logInfo m!"TAYLORS_PRODIGY_AXIOM_AUDIT=PASS COUNT={declarations.length}"

#print axioms TaylorsProdigy.native_RH_of_TAYLORS_PRODIGY_PREMISE
#print axioms TaylorsProdigy.TAYLORS_PRODIGY_PREMISE_of_native_RH
#print axioms TaylorsProdigy.TAYLORS_PRODIGY_PREMISE_iff_RH
