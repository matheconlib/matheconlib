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
Lean's public axiom collector follows types and proof bodies transitively, using Lean 4.35's
precomputed imported-module axiom data. An unused axiom is itself a declaration, so it is checked
even when no theorem refers to it.
-/

open Lean

private def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

private def origin (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  return (← env.header.modules[idx]?).module

private unsafe def audit (reportPath : System.FilePath) (modules : Array Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  IO.println s!"Loading {modules.size} modules for the compiled axiom audit..."
  (← IO.getStdout).flush
  -- This standalone process loads one pinned module set on one thread. Initializer results
  -- may retain imported objects, so keep the environment alive until the process exits.
  -- Loading extensions supplies the public collector's precomputed axiom data.
  enableInitializersExecution
  let env ← importModules (modules.map fun n ↦ { module := n }) {}
    (leakEnv := true) (loadExts := true) (level := .private)
  for name in modules do
    unless (env.getModuleIdx? name).isSome do
      throw <| IO.userError s!"Module was not loaded: {name}"
  let moduleSet := modules.foldl (fun (out : NameSet) name ↦ out.insert name) {}
  let declarations := (env.constants.fold (init := #[]) fun out name _ ↦
    if (origin env name).any moduleSet.contains then out.push name else out).qsort Name.quickLt
  IO.println s!"Auditing {declarations.size} declarations..."
  (← IO.getStdout).flush
  let mut axioms : NameSet := {}
  let mut violations : Array Json := #[]
  for decl in declarations do
    let used := Id.run <| (collectAxioms decl : StateM Environment (Array Name)).run' env
    for axiomName in used do
      if axioms.contains axiomName then
        continue
      axioms := axioms.insert axiomName
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
    ("axiom_collector", toJson "Lean.collectAxioms"),
    ("axioms", toJson ((axioms.toArray.qsort Name.quickLt).map Name.toString)),
    ("allowed_axioms", toJson (allowedAxioms.map Name.toString)),
    ("violations", toJson violations)]
  IO.FS.writeFile reportPath (report.pretty ++ "\n")
  if violations.isEmpty then
    IO.println s!"Proof integrity check passed: {declarations.size} declarations in \
      {modules.size} modules."
    return 0
  IO.eprintln s!"Proof integrity check failed: {violations.size} forbidden axioms."
  return 1

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | reportPath :: firstModule :: rest =>
    audit reportPath ((firstModule :: rest).toArray.map String.toName)
  | _ =>
    IO.eprintln "Usage: CheckProofIntegrity.lean REPORT.json MODULE [MODULE ...]"
    return 2
