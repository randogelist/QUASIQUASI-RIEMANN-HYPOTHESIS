import MisterPremise
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/- The literal native endpoint is checked, without any extra hypothesis. -/
#check MisterPremise.MISTERPREMISE
#check MisterPremise.MISTERPREMISE_iff_expanded
#check MisterPremise.RiemannHypothesis_of_MISTERPREMISE
#check MisterPremise.MISTERPREMISE_of_RiemannHypothesis
#check MisterPremise.MISTERPREMISE_iff_RiemannHypothesis
#check MisterPremise.RiemannHypothesis_iff_MISTERPREMISE

example : MisterPremise.MISTERPREMISE ↔ _root_.RiemannHypothesis :=
  MisterPremise.MISTERPREMISE_iff_RiemannHypothesis

example : _root_.RiemannHypothesis ↔ MisterPremise.MISTERPREMISE :=
  MisterPremise.RiemannHypothesis_iff_MISTERPREMISE

#print axioms MisterPremise.MISTERPREMISE_iff_RiemannHypothesis
#print axioms MisterPremise.RiemannHypothesis_iff_MISTERPREMISE

/- Select by defining module, so private helpers and generated declarations
are included, while imported Mathlib and Lean declarations are not counted.
Their dependencies are still checked transitively for every project constant. -/
run_cmd do
  let sourcePaths ← IO.FS.lines "compile-order.txt"
  let projectModules : Array Name := sourcePaths.map fun sourcePath =>
    ((sourcePath.trimAscii.toString.replace ".lean" "").replace "/" ".").replace "\\" "." |>.toName
  unless projectModules.contains `MisterPremise do
    throwError "AUDIT_SOURCE_LIST_MISSING_MISTERPREMISE"
  let env ← getEnv
  let mut selectedModules := Array.replicate env.header.moduleNames.size false
  for moduleName in projectModules do
    let some moduleIdx := env.getModuleIdx? moduleName |
      throwError m!"AUDIT_SOURCE_MODULE_NOT_IMPORTED {moduleName}"
    selectedModules := selectedModules.set! moduleIdx.toNat true
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarationCount : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants.toList do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    unless selectedModules[moduleIdx.toNat]?.getD false do continue
    declarationCount := declarationCount + 1
    if let .thmInfo _ := info then theoremCount := theoremCount + 1
    let dependencies ← Lean.collectAxioms name
    logInfo m!"AXIOM_DEPENDENCIES {name}: {dependencies}"
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError m!"UNAPPROVED_DEPENDENCY {name}: {dependency}"
  if declarationCount == 0 then
    throwError "AUDIT_PROJECT_DECLARATIONS_EMPTY"
  logInfo m!"AUDITED_PROJECT_MODULES={projectModules.size}"
  logInfo m!"AUDITED_PROJECT_DECLARATIONS={declarationCount}"
  logInfo m!"AUDITED_PROJECT_THEOREM_CONSTANTS={theoremCount}"
  logInfo "MISTERPREMISE_AXIOM_AUDIT=PASS"
