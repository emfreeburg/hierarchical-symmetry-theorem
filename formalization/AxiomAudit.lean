/-
Axiom audit for the Freeburg library.

Walks the entire compiled environment and, for EVERY constant compiled
from a `Freeburg.*` module — theorems, definitions, instances, and all
auto-generated auxiliaries — collects the axioms its proof ultimately
depends on.  The audit FAILS (elaboration error, nonzero exit code) if
any constant depends on an axiom outside Lean's three standard ones:

  `propext`, `Classical.choice`, `Quot.sound`

In particular a pass rules out `sorryAx` (any `sorry`/`admit`),
`Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`), and every
custom axiom, across the whole library at once — strictly stronger than
running `#print axioms` on each named theorem.

Run from the repository root with:

  lake env lean AxiomAudit.lean
-/
import Freeburg

open Lean

#eval show Elab.TermElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.allImportedModuleNames
  let mut nChecked := 0
  let mut axiomsSeen : List Name := []
  let mut offenders : Array (Name × List Name) := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some modName := mods[idx]? then
        if modName.getRoot == `Freeburg then
          let axs ← collectAxioms name
          nChecked := nChecked + 1
          for a in axs do
            unless axiomsSeen.contains a do
              axiomsSeen := axiomsSeen.insert a
          let bad := axs.toList.filter (fun a => !allowed.contains a)
          unless bad.isEmpty do
            offenders := offenders.push (name, bad)
  IO.println s!"Freeburg axiom audit"
  IO.println s!"  constants checked (everything compiled from Freeburg.* modules): {nChecked}"
  IO.println s!"  distinct axioms encountered: {axiomsSeen}"
  if offenders.isEmpty then
    IO.println s!"  RESULT: PASS — every constant stays within {allowed}"
  else
    for (n, bad) in offenders do
      IO.println s!"  OFFENDER: {n} depends on {bad}"
    throwError "Freeburg axiom audit FAILED: {offenders.size} offending constant(s)"
