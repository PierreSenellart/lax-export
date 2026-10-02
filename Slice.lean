/-
Copyright 2026 Pierre Senellart
SPDX-License-Identifier: Apache-2.0
-/
/-
The Lean half of the Lax export tool: what Lean knows and Python cannot
guess. Run with the library's toolchain on PATH and its built oleans on
LEAN_PATH, from the library's source root.

  lean --run lax/Slice.lean closure <prefix> <out.json> <target constant>...

reports the targets' proof-term closure: every constant reached, with its
module and source range (generated constants have none), the targets'
axioms, and the touched modules of the prefix.

  lean --run lax/Slice.lean commands <source file> <out.json>

elaborates one source file against its own imports and lists its commands:
syntax kind, byte range, line range. Elaboration rather than parsing, because
a file's own `local notation` and `open scoped` change how the rest of it
parses. One process per file: `importModules (loadExts := true)` is a
once-per-process affair.

Python decides what to keep and how to rename; this program never writes
Lean source.
-/
import Lean

open Lean

/-- The module a constant was declared in, by header index. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

/-- Run a `CoreM` computation on a bare environment. -/
def runCore (env : Environment) (x : CoreM α) : IO α :=
  Prod.fst <$> x.toIO { fileName := "<lax>", fileMap := FileMap.ofString "" } { env }

private def usedBy (ci : ConstantInfo) : Array Name :=
  let cs := ci.type.getUsedConstants
  let cs := match ci.value? (allowOpaque := true) with
    | some v => cs ++ v.getUsedConstants
    | none => cs
  match ci with
  | .inductInfo v => cs ++ v.ctors.toArray
  | _ => cs

partial def close (kenv : Kernel.Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n then close kenv rest acc
    else
      let acc := acc.insert n
      match kenv.find? n with
      | none => close kenv rest acc
      | some ci => close kenv ((usedBy ci).toList ++ rest) acc

unsafe def closureMode (prefix_ outPath : String) (targets : List String) : IO UInt32 := do
  let pfx := prefix_.toName
  let targetNames := targets.map String.toName
  let env ← importModules #[{ module := pfx }] {} (trustLevel := 0) (loadExts := true)
  let kenv := env.checked.get
  for t in targetNames do
    if (kenv.find? t).isNone then
      IO.eprintln s!"unknown target {t}"; return 1
  let cls := close kenv targetNames {}
  let mut consts : Array Json := #[]
  let mut mods : NameSet := {}
  for n in cls.toArray do
    let some _ := kenv.find? n | continue
    let some m := moduleOf env n | continue
    let own := pfx.isPrefixOf m
    if own then mods := mods.insert m
    let range ← runCore env (Lean.findDeclarationRanges? n)
    let r : Json := match range with
      | some dr => Json.mkObj [("line", dr.range.pos.line), ("endLine", dr.range.endPos.line),
                               ("col", dr.range.pos.column), ("endCol", dr.range.endPos.column)]
      | none => Json.null
    consts := consts.push (Json.mkObj [("name", toString n), ("module", toString m),
                                       ("own", own), ("range", r)])
  let mut axioms : Array Json := #[]
  for t in targetNames do
    let axs ← runCore env (collectAxioms t)
    axioms := axioms.push (Json.mkObj [("target", toString t),
      ("axioms", toJson (axs.toList.map toString))])
  let doc := Json.mkObj [("prefix", toString pfx), ("targets", toJson targets),
    ("constants", Json.arr consts), ("axioms", Json.arr axioms),
    ("modules", toJson (mods.toArray.map toString))]
  IO.FS.writeFile outPath doc.pretty
  IO.println s!"{cls.size} constants, {mods.size} own modules"
  return 0

/-- The syntax of a command's info tree root, and the syntaxes of the commands
elaborated directly beneath it (not of what those elaborate in turn). -/
partial def topAndNested (t : Elab.InfoTree) : Option (Syntax × Array Syntax) :=
  let rec nestedOf (t : Elab.InfoTree) : Array Syntax :=
    match t with
    | .context _ t => nestedOf t
    | .node (.ofCommandInfo ci) _ => #[ci.stx]
    | .node _ children => children.toArray.flatMap nestedOf
    | .hole _ => #[]
  match t with
  | .context _ t => topAndNested t
  | .node (.ofCommandInfo ci) children =>
    some (ci.stx, children.toArray.flatMap nestedOf)
  | _ => none

unsafe def commandsMode (file outPath : String) : IO UInt32 := do
  let path : System.FilePath := file
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let imports := Elab.headerToImports header
  let env ← importModules imports {} (trustLevel := 0) (loadExts := true)
  let cmdState := Elab.Command.mkState env messages {}
  let s ← Elab.IO.processCommands inputCtx parserState cmdState
  -- Commands a library-defined elaborator produced from a command of its
  -- own (`fo_language …`), as the info trees record them: for each top-level
  -- command, the commands elaborated directly beneath it, pretty-printed
  -- with macro scopes erased so that they read as ordinary source.
  let mut expansions : Std.HashMap Nat (Array String) := {}
  for tree in s.commandState.infoState.trees do
    let some (topStx, nested) := topAndNested tree | continue
    if nested.isEmpty then continue
    -- only library-defined commands: core ones (notations, declarations
    -- with `deriving`) also elaborate nested commands, which stay as written
    if (`Lean.Parser.Command).isPrefixOf topStx.getKind || topStx.getKind == `lemma then continue
    let some pos := topStx.getPos? | continue
    let mut texts : Array String := #[]
    for n in nested do
      let clean := n.rewriteBottomUp fun stx => match stx with
        | .ident info raw val pre => .ident info raw val.eraseMacroScopes pre
        | stx => stx
      try
        let fmt ← runCore s.commandState.env (PrettyPrinter.ppCommand ⟨clean⟩)
        texts := texts.push fmt.pretty
      catch e =>
        IO.eprintln s!"cannot print a command elaborated by {topStx.getKind}: {e}"
        texts := texts.push "<missing>"
    expansions := expansions.insert pos.byteIdx texts
  let mut out : Array Json := #[]
  if let some tail := header.raw.getTailPos? then
    out := out.push (Json.mkObj [("kind", "header"), ("start", 0), ("end", tail.byteIdx),
      ("line", 1), ("endLine", (inputCtx.fileMap.toPosition tail).line)])
  for cmd in s.commands do
    let some pos := cmd.getPos? | continue
    let some tail := cmd.getTailPos? | continue
    let p := inputCtx.fileMap.toPosition pos
    let q := inputCtx.fileMap.toPosition tail
    let exp : Json := match expansions.get? pos.byteIdx with
      | some ts => toJson ts
      | none => Json.null
    out := out.push (Json.mkObj [("kind", toString cmd.getKind),
      ("start", pos.byteIdx), ("end", tail.byteIdx), ("line", p.line), ("endLine", q.line),
      ("expansion", exp)])
  let mut errors : Array String := #[]
  for m in s.commandState.messages.toList do
    if m.severity == .error then
      errors := errors.push (← m.data.toString)
  IO.FS.writeFile outPath (Json.mkObj [("file", file), ("commands", Json.arr out),
    ("errors", toJson errors)]).pretty
  IO.println s!"{out.size} commands, {errors.size} errors"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  match args with
  | "closure" :: pfx :: out :: targets => closureMode pfx out targets
  | ["commands", file, out] => commandsMode file out
  | _ => IO.eprintln "usage: Slice.lean closure <prefix> <out> <target>... | commands <file> <out>"; return 1
