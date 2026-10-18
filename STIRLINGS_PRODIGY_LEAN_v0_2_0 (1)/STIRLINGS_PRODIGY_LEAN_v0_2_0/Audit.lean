import StirlingsProdigy

open Lean Elab Command

#print RiemannHypothesis
#print AWPIRH.xi
#print AWPIRH.theta
#print AngularMaster.actualProfile
#print StirlingsProdigy.U
#print StirlingsProdigy.A
#print StirlingsProdigy.B
#print StirlingsProdigy.taylorRemainder
#print StirlingsProdigy.STIRLINGS_PRODIGY
#print StirlingsProdigy.RH_of_STIRLINGS_PRODIGY
#print StirlingsProdigy.STIRLINGS_PRODIGY_IMP_RH
#print StirlingsProdigy.LocalFirstOrderAt
#print StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL
#print StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL_IFF_RH
#print StirlingsProdigy.RH_IFF_STIRLINGS_PRODIGY_LOCAL

example : StirlingsProdigy.STIRLINGS_PRODIGY → RiemannHypothesis :=
  StirlingsProdigy.STIRLINGS_PRODIGY_IMP_RH

example : RiemannHypothesis ↔ StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL :=
  StirlingsProdigy.RH_IFF_STIRLINGS_PRODIGY_LOCAL

run_cmd do
  let declarations : Array Name := #[
    ``AWPIRH.xi,
    ``AWPIRH.theta,
    ``AWPIRH.theta_entire,
    ``AngularMaster.actualProfile,
    ``AngularMaster.native_RH_iff_theta_zeros_nonpositive,
    ``AngularMaster.native_RH_of_actual_angular_monotone,
    ``StirlingsProdigy.U,
    ``StirlingsProdigy.A,
    ``StirlingsProdigy.B,
    ``StirlingsProdigy.taylorRemainder,
    ``StirlingsProdigy.STIRLINGS_PRODIGY,
    ``StirlingsProdigy.taylor_decomposition,
    ``StirlingsProdigy.U_eq_deriv,
    ``StirlingsProdigy.affine_lower_bound,
    ``StirlingsProdigy.U_lower_bound_of_STIRLINGS_PRODIGY,
    ``StirlingsProdigy.U_positive_of_STIRLINGS_PRODIGY,
    ``StirlingsProdigy.actual_deriv_positive_of_STIRLINGS_PRODIGY,
    ``StirlingsProdigy.actual_profile_monotone_of_STIRLINGS_PRODIGY,
    ``StirlingsProdigy.RH_of_STIRLINGS_PRODIGY,
    ``StirlingsProdigy.STIRLINGS_PRODIGY_IMP_RH,
    ``StirlingsProdigy.LocalFirstOrderAt,
    ``StirlingsProdigy.derivative_nonnegative_of_localFirstOrderAt,
    ``StirlingsProdigy.localFirstOrderAt_of_monotoneOn,
    ``StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL,
    ``StirlingsProdigy.actual_deriv_nonnegative_of_STIRLINGS_PRODIGY_LOCAL,
    ``StirlingsProdigy.actual_profile_monotone_of_STIRLINGS_PRODIGY_LOCAL,
    ``StirlingsProdigy.RH_of_STIRLINGS_PRODIGY_LOCAL,
    ``StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL_of_STIRLINGS_PRODIGY,
    ``AngularMaster.actual_profileMaster_of_native_RH,
    ``StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL_of_RH,
    ``StirlingsProdigy.STIRLINGS_PRODIGY_LOCAL_IFF_RH,
    ``StirlingsProdigy.RH_IFF_STIRLINGS_PRODIGY_LOCAL
  ]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in declarations do
    let dependencies ← Lean.collectAxioms name
    logInfo m!"AXIOM_DEPENDENCIES {name}: {dependencies}"
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError m!"UNAPPROVED_DEPENDENCY {name}: {dependency}"
  logInfo m!"STIRLINGS_PRODIGY_AXIOM_AUDIT=PASS COUNT={declarations.size}"
