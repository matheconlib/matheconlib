/-
Copyright (c) 2026 Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen
-/
import Lean

/-!
# Statement ledger

`lake exe statement_ledger` loads the built `MathEconLib` environment and writes the statement of
every library declaration to `StatementLedger.txt`, one entry per declaration, sorted by name. The
ledger is a "meaning diff": a pull request that changes what the library claims changes this file,
separately from any change to proofs.

Usage, from the repository root after `lake build MathEconLib`:

* `lake exe statement_ledger` regenerates `StatementLedger.txt`;
* `lake exe statement_ledger --output PATH` writes to `PATH` instead (`-` for standard output).

The filter, the entry format, and the printing options are described in `header` below, which is
also the header of the generated file.

## Stability

The output is deterministic for a fixed toolchain and Mathlib revision: entries are independent,
sorted by name, and printed with fixed options, and hygienic names are renamed before printing.
Across toolchain or Mathlib upgrades, expect the following to change without any change in the
library, so an upgrade pull request regenerates the ledger:

* the printed form, when delaborators, notation, or default instance paths change;
* the hashes, when elaboration produces different terms (for example a new instance path);
* the equation lemmas, when Lean's equation generator changes their shape;
* compiler-generated declarations and automatically generated instance names.

Independently of upgrades, an equation lemma such as `f.eq_def` appears in the ledger only if some
library proof caused it to be generated (for example by `rw [f]`), so a proof change can add or
remove such an entry.
-/

open Lean Meta PrettyPrinter Delaborator

namespace StatementLedger

/-- The module that is imported; the declarations of the modules under this prefix are listed. -/
def rootModule : Name := `MathEconLib

/-- The default output file, relative to the repository root. -/
def defaultOutput : System.FilePath := "StatementLedger.txt"

/-- The fixed header of the generated file. -/
def header : String := "\
-- Statement ledger for MathEconLib. Generated file: do not edit by hand.
-- Regenerate from the repository root with
--   lake build MathEconLib && lake exe statement_ledger
-- CI fails when this file is out of date (scripts/check-statement-ledger.sh).
--
-- Scope: the declarations of the `MathEconLib.*` modules selected by the filter of the Mathlib
-- pull-request declaration summaries (leanprover-community/mathlib-ci,
-- scripts/pr_summary/dumpReasonableDecls.lean): not private, not unsafe, and not
-- `Lean.Name.isInternalDetail` (no name component starting with `_` or numeric, and no last
-- component `eq_<n>`, `match_<n>`, `proof_<n>`, or `omega_<n>`). Compiler-generated declarations
-- that pass this filter (recursors, constructors, projections, `casesOn`, `noConfusion`,
-- `injEq`, ...) are listed too. Equation lemmas such as `f.eq_def` are listed only if the library
-- itself caused them to be generated.
--
-- One entry per declaration, sorted by full name:
--   * theorem, axiom, opaque, instance, constructor, recursor, projection: the signature;
--   * def, abbrev: the signature, then the equation lemmas Lean generates for it (`eq_<n>`, or
--     `eq_def` when there are none), not the compiled body;
--   * generated def (auxiliary recursors, `noConfusion`, `ctorIdx`, ...): the signature;
--   * structure, class: the signature, the constructor, the parent projections, and each field
--     (inherited fields included) with its type and default value;
--   * inductive: the signature and each constructor.
-- The last line of an entry is a 64-bit FNV-1a hash of its statement expressions (signature,
-- equations, fields, constructors), computed on the expressions themselves with metadata
-- dropped, proof subterms erased, and hygiene erased from binder names. It changes when a
-- statement changes even if the printed form does not.
--
-- Printing options are fixed: proofs elided as `⋯`, notation and coercions shown, universe
-- parameters listed after the declaration name (universe arguments inside terms are covered by
-- the hash), full names, no truncation, width 100. Hygienic and shadowing binder names are
-- renamed (`x✝` to `x`, a repeated `x` to `x_1`); anonymous instance binders print as `[C]`.
"

/-! ## Pretty-printing options -/

/-- Options fixed for every entry, so that the output does not depend on toolchain defaults. -/
def ppOptions : Options :=
  let o : Options := {}
  let o := o.set `pp.proofs false
  let o := o.set `pp.proofs.threshold (0 : Nat)
  let o := o.set `pp.universes false
  let o := o.set `pp.fullNames true
  let o := o.set `pp.privateNames false
  let o := o.set `pp.unicode.fun true
  let o := o.set `pp.notation true
  let o := o.set `pp.coercions true
  let o := o.set `pp.fieldNotation true
  let o := o.set `pp.explicit false
  let o := o.set `pp.funBinderTypes false
  let o := o.set `pp.piBinderTypes true
  let o := o.set `pp.letVarTypes false
  let o := o.set `pp.structureInstances true
  let o := o.set `pp.numericTypes false
  let o := o.set `pp.natLit false
  let o := o.set `pp.beta false
  let o := o.set `pp.mvars true
  let o := o.set `pp.deepTerms true
  let o := o.set `pp.maxSteps (100000000 : Nat)
  let o := o.set `pp.oneline false
  let o := o.set `pp.analyze false
  let o := o.set `pp.tagAppFns false
  let o := o.set `format.indent (2 : Nat)
  o.set `maxHeartbeats (0 : Nat)

/-! ## Selection -/

/-- The declaration filter of the Mathlib pull-request summaries
(`scripts/pr_summary/dumpReasonableDecls.lean` in `leanprover-community/mathlib-ci`): a
declaration is listed if it is not private, not unsafe, and not an internal detail in the sense of
`Lean.Name.isInternalDetail`. -/
def isReasonable (n : Name) (ci : ConstantInfo) : Bool :=
  !n.isInternalDetail && !isPrivateName n && !ci.isUnsafe

/-- The names of the declarations that receive a ledger entry: the reasonable declarations of the
modules under `rootModule`, sorted by their string form. -/
def selectNames (env : Environment) : Array Name :=
  let modules := env.allImportedModuleNames
  let inScope (n : Name) : Bool := Id.run do
    let some idx := env.getModuleIdxFor? n | return false
    let some mod := modules[idx.toNat]? | return false
    return rootModule.isPrefixOf mod
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    if isReasonable n ci && inScope n then acc.push n else acc
  names.qsort (toString · < toString ·)

/-- Last name components of compiler-generated definitions attached to an inductive type, besides
those tagged as auxiliary recursors or `noConfusion`. -/
def inductiveAuxSuffixes : List String :=
  ["noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "ofNat"]

/-- Whether a definition is generated by the compiler for an inductive type. Such definitions are
printed with their signature only. -/
def isGeneratedDef (env : Environment) (n : Name) : Bool := Id.run do
  if isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n then
    return true
  let .str p s := n | return false
  return inductiveAuxSuffixes.contains s && (env.find? p matches some (.inductInfo _))

/-! ## Normalization -/

/-- A binder name for `n` that is free of macro scopes and distinct from the names in `scope`. -/
partial def freshBinderName (scope : List Name) (n : Name) : Name :=
  let base := n.eraseMacroScopes
  let rec go (k : Nat) : Name :=
    let c := base.appendIndexAfter k
    if scope.contains c then go (k + 1) else c
  if scope.contains base then go 1 else base

/-- Renames binders so that the printer never needs hygiene marks such as `x✝`: a hygienic name
is replaced by its base name, and a name that shadows an enclosing binder gets a numeric suffix
(`x_1`). Hygienic instance binders keep their names: the signature printer shows them as `[C]`,
and instance arguments are not printed. -/
partial def sanitizeBinders (e : Expr) (scope : List Name := []) : Expr :=
  let rename (n : Name) (bi : BinderInfo) : Name :=
    if n.hasMacroScopes then
      if bi.isInstImplicit then n else freshBinderName scope n
    else if scope.contains n then freshBinderName scope n
    else n
  match e with
  | .forallE n d b bi =>
    let n' := rename n bi
    .forallE n' (sanitizeBinders d scope) (sanitizeBinders b (n' :: scope)) bi
  | .lam n d b bi =>
    let n' := rename n bi
    .lam n' (sanitizeBinders d scope) (sanitizeBinders b (n' :: scope)) bi
  | .letE n t v b nd =>
    let n' := rename n .default
    .letE n' (sanitizeBinders t scope) (sanitizeBinders v scope) (sanitizeBinders b (n' :: scope)) nd
  | .app f a => .app (sanitizeBinders f scope) (sanitizeBinders a scope)
  | .mdata d e => .mdata d (sanitizeBinders e scope)
  | .proj s i e => .proj s i (sanitizeBinders e scope)
  | e => e

/-- The placeholder that replaces proof subterms before hashing. -/
def erasedProof : Expr := .const `StatementLedger.erasedProof []

/-- Erases proof subterms, so that the hash depends on statements only. -/
def eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if e.isSort || e.isLit || e.isMVar || e.hasLooseBVars then return .continue
    if (← isProof e) then return .done erasedProof
    return .continue)

/-! ## Hashing -/

/-- FNV-1a, 64 bits, over bytes. The constants are fixed by the algorithm, so the result does not
depend on the toolchain. -/
structure Hasher where
  state : UInt64 := 0xcbf29ce484222325

namespace Hasher

def byte (h : Hasher) (b : UInt8) : Hasher := ⟨(h.state ^^^ b.toUInt64) * 0x100000001b3⟩

def str (h : Hasher) (s : String) : Hasher :=
  (s.toUTF8.foldl byte h).byte 0

def nat (h : Hasher) (n : Nat) : Hasher := h.str (toString n)

def name (h : Hasher) : Name → Hasher
  | .anonymous => h.byte 0x10
  | .str p s => (name h p).byte 0x11 |>.str s
  | .num p n => (name h p).byte 0x12 |>.nat n

def level (h : Hasher) : Level → Hasher
  | .zero => h.byte 0x20
  | .succ l => (h.byte 0x21).level l
  | .max a b => ((h.byte 0x22).level a).level b
  | .imax a b => ((h.byte 0x23).level a).level b
  | .param n => (h.byte 0x24).name n.eraseMacroScopes
  | .mvar _ => h.byte 0x25

def binderInfo (h : Hasher) : BinderInfo → Hasher
  | .default => h.byte 0x30
  | .implicit => h.byte 0x31
  | .strictImplicit => h.byte 0x32
  | .instImplicit => h.byte 0x33

/-- Hashes the structure of an expression. Metadata is skipped, and binder and universe parameter
names are hashed with their macro scopes erased. Free variables and metavariables are not expected. -/
partial def expr (h : Hasher) : Expr → Hasher
  | .bvar i => (h.byte 0x40).nat i
  | .fvar _ => h.byte 0x41
  | .mvar _ => h.byte 0x42
  | .sort l => (h.byte 0x43).level l
  | .const n ls => ls.foldl level ((h.byte 0x44).name n) |>.byte 0x45
  | .app f a => ((h.byte 0x46).expr f).expr a
  | .lam n d b bi =>
    ((((h.byte 0x47).name n.eraseMacroScopes).binderInfo bi).expr d).expr b
  | .forallE n d b bi =>
    ((((h.byte 0x48).name n.eraseMacroScopes).binderInfo bi).expr d).expr b
  | .letE n t v b _ => ((((h.byte 0x49).name n.eraseMacroScopes).expr t).expr v).expr b
  | .lit (.natVal n) => (h.byte 0x4a).nat n
  | .lit (.strVal s) => (h.byte 0x4b).str s
  | .mdata _ e => h.expr e
  | .proj s i e => (((h.byte 0x4c).name s).nat i).expr e

def hex (h : Hasher) : String :=
  let digits := String.ofList (Nat.toDigits 16 h.state.toNat)
  "".pushn '0' (16 - digits.length) ++ digits

end Hasher

/-! ## Rendering -/

/-- An entry under construction: printed lines and the expressions covered by the hash. -/
structure Entry where
  lines : Array String := #[]
  hashed : Array Expr := #[]

/-- Replaces hygienic universe parameter names by fresh base names. -/
def sanitizeLevels (us : List Name) (type : Expr) : List Name × Expr :=
  let us' := us.foldl (init := []) fun acc u =>
    acc ++ [if u.hasMacroScopes then freshBinderName (acc ++ us.filter (!·.hasMacroScopes)) u else u]
  (us', type.instantiateLevelParams us (us'.map Level.param))

/-- Pretty-prints `id.{us} binders : type` for the closed type `type`, in the style of `#print`'s
signatures: leading binders become parameters. The universe parameters are printed only if
`showLevels` holds. -/
def ppSig (id : Name) (us : List Name) (type : Expr) (showLevels := true) : MetaM Format := do
  let (us, type) := sanitizeLevels us type
  let us := if showLevels then us else []
  let type := sanitizeBinders type
  let idStx : Term ← if us.isEmpty then pure (mkIdent id) else do
    let us ← us.toArray.mapM fun u => `(level| $(mkIdent u):ident)
    `($(mkIdent id).{$us,*})
  let (stx, _) ← delabCore type (delab := delabForallParamsWithSignature fun groups type =>
    `(declSigWithId| $idStx $groups* : $type))
  ppTerm ⟨stx⟩

/-- Pretty-prints an expression that may mention local variables. -/
def ppE (e : Expr) : MetaM Format :=
  Meta.ppExpr (sanitizeBinders e)

/-- The maximal line width of the ledger. -/
def width : Nat := 100

/-- Lays out `f` indented by `n` spaces, within `width` columns. -/
def layout (n : Nat) (f : Format) : String :=
  let pad := "".pushn ' ' n
  "\n".intercalate ((f.pretty (width - n)).splitOn "\n" |>.map (pad ++ ·))

/-- `kw sig`, laid out at the margin. -/
def headLine (kw : String) (sig : Format) : String :=
  layout 0 (kw ++ " " ++ sig)

/-- `label : f`, breaking after the colon when `f` does not fit on the line. -/
def labelled (label : String) (f : Format) : Format :=
  .group (label ++ " :" ++ .nest 4 (.line ++ f))

/-- Pretty-prints the signature of a declaration under its own name. -/
def ppDeclSig (ci : ConstantInfo) : MetaM Format :=
  ppSig ci.name ci.levelParams ci.type

/-- A keyword describing a definition's reducibility, as written in source. -/
def defKeyword (n : Name) : MetaM String := do
  match (← getReducibilityStatus n) with
  | .reducible => return "abbrev"
  | .irreducible => return "@[irreducible] def"
  | _ => return "def"

/-- The equation lemmas of a definition: `eq_<n>` when Lean generates them, otherwise `eq_def`. -/
def equationsOf (n : Name) : MetaM (Array Name) := do
  if let some eqs ← getEqnsFor? n then
    if !eqs.isEmpty then return eqs
  if let some eq ← getUnfoldEqnFor? n (nonRec := true) then
    return #[eq]
  return #[]

def renderDef (ci : ConstantInfo) : MetaM Entry := do
  let mut e : Entry := { hashed := #[ci.type] }
  e := { e with lines := e.lines.push (headLine (← defKeyword ci.name) (← ppDeclSig ci)) }
  let eqs ← equationsOf ci.name
  if eqs.isEmpty then
    throwError "no equation lemmas for {ci.name}"
  for eq in eqs do
    let eqInfo ← getConstInfo eq
    let some suffix := eq.componentsRev.head? | unreachable!
    e := { e with
      lines := e.lines.push (layout 2 (← ppSig suffix eqInfo.levelParams eqInfo.type false))
      hashed := e.hashed.push eqInfo.type }
  return e

def renderSig (keyword : String) (ci : ConstantInfo) : MetaM Entry :=
  return { lines := #[headLine keyword (← ppDeclSig ci)], hashed := #[ci.type] }

def renderStructure (ci : ConstantInfo) : MetaM Entry := do
  let env ← getEnv
  let n := ci.name
  let keyword := if isClass env n then "class" else "structure"
  let mut e : Entry := { hashed := #[ci.type] }
  e := { e with lines := e.lines.push (headLine keyword (← ppDeclSig ci)) }
  let ctor := getStructureCtor env n
  e := { e with
    lines := e.lines.push s!"  constructor {ctor.name}"
    hashed := e.hashed.push ctor.type }
  let levels := ci.levelParams.map Level.param
  forallTelescope ci.type fun params _ => do
    withLocalDeclD `self (mkAppN (.const n levels) params) fun self => do
      let mut e := e
      let close (t : Expr) : MetaM Expr := mkForallFVars (params.push self) t
      for parent in getStructureParentInfo env n do
        let ptype ← inferType (mkApp (mkAppN (.const parent.projFn levels) params) self)
        e := { e with
          lines := e.lines.push (layout 2 (labelled s!"parent {parent.projFn}" (← ppE ptype)))
          hashed := e.hashed.push (← close ptype) }
      for field in getStructureFieldsFlattened env n (includeSubobjectFields := false) do
        let proj ← mkProjection self field
        let ftype ← inferType proj
        let mut fieldLine := labelled s!"field {field}" (← ppE ftype)
        e := { e with hashed := e.hashed.push (← close ftype) }
        if let some defFn := getEffectiveDefaultFnForField? env n field then
          let fieldVal? (f : Name) : MetaM (Option Expr) := some <$> mkProjection self f
          if let some (_, val) ← instantiateStructDefaultValueFn? defFn levels params fieldVal? then
            fieldLine := .group (fieldLine ++ " :=" ++ .nest 4 (.line ++ (← ppE val)))
            e := { e with hashed := e.hashed.push (← close val) }
        e := { e with lines := e.lines.push (layout 2 fieldLine) }
      return e

def renderInductive (ci : InductiveVal) : MetaM Entry := do
  let keyword := if isClass (← getEnv) ci.name then "class inductive" else "inductive"
  let mut e : Entry := { hashed := #[ci.type] }
  e := { e with lines := e.lines.push (headLine keyword (← ppDeclSig (.inductInfo ci))) }
  for ctor in ci.ctors do
    let ctorInfo ← getConstInfo ctor
    e := { e with
      lines := e.lines.push (layout 2 ("| " ++ (← ppSig ctor ctorInfo.levelParams ctorInfo.type false)))
      hashed := e.hashed.push ctorInfo.type }
  return e

/-- Renders one ledger entry. -/
def render (n : Name) : MetaM Entry := do
  let env ← getEnv
  let ci ← getConstInfo n
  let isInst := Meta.isInstanceCore env n
  match ci with
  | .thmInfo _ => renderSig (if isInst then "instance" else "theorem") ci
  | .defnInfo _ =>
    if isInst then renderSig "instance" ci
    else if env.isProjectionFn n then renderSig "projection" ci
    else if isGeneratedDef env n then renderSig "generated def" ci
    else renderDef ci
  | .axiomInfo _ => renderSig "axiom" ci
  | .opaqueInfo _ => renderSig (if isInst then "instance" else "opaque") ci
  | .quotInfo _ => renderSig "quot" ci
  | .inductInfo v => if isStructure env n then renderStructure ci else renderInductive v
  | .ctorInfo _ => renderSig "constructor" ci
  | .recInfo _ => renderSig "recursor" ci

/-- Renders and hashes one entry. Each entry starts from the imported environment, so lemmas
generated for one entry cannot affect another. -/
def entryText (env : Environment) (n : Name) : IO String := do
  let ctx : Core.Context := {
    fileName := "<statement_ledger>"
    fileMap := default
    options := ppOptions
    maxHeartbeats := 0 }
  let act : MetaM String := do
    let e ← render n
    let mut h : Hasher := {}
    for t in e.hashed do
      h := h.expr (← eraseProofs t)
    return "\n".intercalate (e.lines.push s!"  -- hash {h.hex}").toList
  let (text, _) ← act.run'.toIO ctx { env }
  return text

/-! ## Main -/

def usage : String :=
  "Usage: lake exe statement_ledger [--output PATH]\n\
  Writes the statement ledger to PATH (default: StatementLedger.txt; `-` for standard output)."

def parseArgs : List String → Except String System.FilePath
  | [] => .ok defaultOutput
  | ["--output", path] => .ok path
  | _ => .error usage

unsafe def run (output : System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := rootModule }] {} (loadExts := true)
  let names := selectNames env
  -- Entries are independent, so render them in parallel chunks and reassemble them in order.
  let chunkSize := max 1 ((names.size + 15) / 16)
  let chunks := (List.range ((names.size + chunkSize - 1) / chunkSize)).map fun i =>
    names.extract (i * chunkSize) ((i + 1) * chunkSize)
  let tasks ← chunks.mapM fun chunk => IO.asTask (prio := .dedicated) do
    chunk.mapM fun n => do
      try
        return Except.ok (← entryText env n)
      catch err =>
        return Except.error s!"{n}: {err}"
  let mut entries := #[]
  let mut failures := 0
  for task in tasks do
    for result in ← IO.ofExcept task.get do
      match result with
      | .ok text => entries := entries.push text
      | .error msg =>
        IO.eprintln s!"error: {msg}"
        failures := failures + 1
  if failures > 0 then
    IO.eprintln s!"{failures} declaration(s) could not be rendered"
    return 1
  let marked := entries.filter (·.contains '✝')
  unless marked.isEmpty do
    IO.eprintln s!"warning: {marked.size} entries contain hygiene marks (✝)"
  let text := header ++ "\n" ++ "\n\n".intercalate entries.toList ++ "\n"
  if output.toString == "-" then
    IO.print text
  else
    IO.FS.writeFile output text
    IO.println s!"Wrote {entries.size} entries to {output}"
  return 0

end StatementLedger

unsafe def main (args : List String) : IO UInt32 := do
  match StatementLedger.parseArgs args with
  | .ok output => StatementLedger.run output
  | .error msg => IO.eprintln msg; return 2
