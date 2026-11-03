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

The `--source` mode also elaborates a source file and audits the anonymous-example environments
saved in its info trees. These retain examples and their auxiliaries before Lean discards them.
The audit covers holes inside interpolated strings or produced by macros. It does not depend on
warning settings or a second parser for Lean string syntax.
-/

open Lean

private def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

private def isExampleName : Name → Bool
  | .anonymous => false
  | .str parent part => part == "_example" || isExampleName parent
  | .num parent _ => isExampleName parent

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

private unsafe def auditSource (reportPath sourcePath : System.FilePath)
    (moduleName : Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile sourcePath) sourcePath.toString
  -- Retain full elaboration information, including the environments of discarded examples.
  let opts := ({} : Options).setBool `Elab.async false
    |>.setBool `internal.cmdlineSnapshots false
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header opts messages inputCtx
    (leakEnv := true) (mainModule := moduleName)
  let state ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages opts)
  if state.commandState.messages.hasErrors then
    for message in state.commandState.messages.toList do
      IO.eprintln (← message.toString)
    throw <| IO.userError s!"Source elaboration failed: {sourcePath}"
  let mut checked := 0
  let mut violations : Array Json := #[]
  -- Examples can reuse a generated name, even within one macro-expanded command. Deduplicate
  -- only identical types and bodies, so a later example with the same name is still audited.
  for tree in state.commandState.infoState.trees do
    let (_, count, found) ← tree.foldInfoM
      (init := (({} : NameMap (Expr × Option Expr)), 0, #[]))
      fun ctx _ (seen, count, found) => do
        let some decl := ctx.parentDecl? | return (seen, count, found)
        -- Persistent declarations are covered by the compiled audit. Here inspect only examples
        -- and their auxiliaries; compiler intermediates from commands such as `#eval` are not
        -- kernel proof declarations and may contain temporary compiler assumptions.
        unless isExampleName decl do return (seen, count, found)
        let some info := ctx.env.find? decl | return (seen, count, found)
        let signature := (info.type, info.value? (allowOpaque := true))
        if seen.find? decl == some signature then
          return (seen, count, found)
        let used := Id.run <| (collectAxioms decl : StateM Environment (Array Name)).run' ctx.env
        let mut found := found
        for axiomName in used do
          unless allowedAxioms.contains axiomName do
            found := found.push <| Json.mkObj [
              ("declaration", toJson decl.toString),
              ("module", toJson moduleName.toString),
              ("source", toJson sourcePath.toString),
              ("axiom", toJson axiomName.toString)]
        return (seen.insert decl signature, count + 1, found)
    checked := checked + count
    violations := violations ++ found
  let report := Json.mkObj [
    ("status", toJson (if violations.isEmpty then "passed" else "failed")),
    ("source", toJson sourcePath.toString),
    ("module", toJson moduleName.toString),
    ("declarations_checked", toJson checked),
    ("violations", toJson violations)]
  IO.FS.writeFile reportPath (report.pretty ++ "\n")
  if violations.isEmpty then return 0
  IO.eprintln s!"Source audit found forbidden axioms in {sourcePath}"
  return 1

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--source", reportPath, sourcePath, moduleName] =>
    auditSource reportPath sourcePath moduleName.toName
  | reportPath :: firstModule :: rest =>
    audit reportPath ((firstModule :: rest).toArray.map String.toName)
  | _ =>
    IO.eprintln "Usage: CheckProofIntegrity.lean REPORT.json MODULE [MODULE ...]"
    return 2
