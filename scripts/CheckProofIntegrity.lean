/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import Lean

/-!
# Audit compiled declarations for incomplete proofs and custom axioms

Run through `python3 scripts/check-proof-integrity.py`. The arguments to this backend are a JSON
output path followed by the modules to audit. Modules are loaded with their private declarations.
Lean's own axiom collector follows types and proof bodies transitively; sharing its visited set
avoids repeatedly traversing common Mathlib dependencies. An unused axiom is itself a declaration,
so it is checked even when no theorem refers to it.
-/

open Lean

private def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def origin (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  env.header.moduleNames[idx]?

private def audit (reportPath : System.FilePath) (modules : Array Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun n ↦ { module := n }) {} (level := .private)
  for name in modules do
    unless (env.getModuleIdx? name).isSome do
      throw <| IO.userError s!"Module was not loaded: {name}"
  let declarations := (env.constants.fold (init := #[]) fun out name _ ↦
    if (origin env name).any modules.contains then out.push name else out).qsort Name.quickLt
  let mut state : CollectAxioms.State := {}
  let mut violations : Array Json := #[]
  for decl in declarations do
    let previousCount := state.axioms.size
    let (_, next) := ((CollectAxioms.collect decl).run env).run state
    state := next
    for axiomName in state.axioms[previousCount:] do
      unless allowedAxioms.contains axiomName do
        violations := violations.push <| Json.mkObj [
          ("declaration", toJson decl.toString),
          ("module", toJson ((origin env decl).map Name.toString)),
          ("axiom", toJson axiomName.toString),
          ("axiom_module", toJson ((origin env axiomName).map Name.toString))]
        IO.eprintln s!"{decl} depends on forbidden axiom {axiomName}"
  let report := Json.mkObj [
    ("status", toJson (if violations.isEmpty then "passed" else "failed")),
    ("modules", toJson (modules.map Name.toString)),
    ("declarations_checked", toJson declarations.size),
    ("dependencies_visited", toJson state.visited.size),
    ("axioms", toJson (state.axioms.map Name.toString)),
    ("allowed_axioms", toJson (allowedAxioms.map Name.toString)),
    ("violations", toJson violations)]
  IO.FS.writeFile reportPath (report.pretty ++ "\n")
  if violations.isEmpty then
    IO.println s!"Proof integrity check passed: {declarations.size} declarations in \
      {modules.size} modules."
    return 0
  IO.eprintln s!"Proof integrity check failed: {violations.size} forbidden axioms."
  return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | reportPath :: firstModule :: rest =>
    audit reportPath ((firstModule :: rest).toArray.map String.toName)
  | _ =>
    IO.eprintln "Usage: CheckProofIntegrity.lean REPORT.json MODULE [MODULE ...]"
    return 2
