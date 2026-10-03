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

  lean --run lax/Slice.lean commands <source file> <out.json> [<syntax category>...]

elaborates one source file against its own imports and lists its commands:
syntax kind, byte range, line range, and, for each use of a notation
involving one of the given syntax categories (the ones the library declares,
which can never carry a package prefix), the term it expanded to.
Elaboration rather than parsing, because a file's own `local notation` and
`open scoped` change how the rest of it parses. One process per file:
`importModules (loadExts := true)` is a once-per-process affair.

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

/-- Whether a syntax tree has a node whose kind satisfies the predicate. -/
partial def containsKind (p : Name → Bool) (stx : Syntax) : Bool :=
  p stx.getKind || stx.getArgs.any (containsKind p)

/-- The uses of library notation recorded in an info tree: the source range
of every macro expansion whose syntax is itself of a kind satisfying the
predicate. -/
partial def usesOf (p : Name → Bool) (t : Elab.InfoTree) (acc : Array (String.Pos.Raw × String.Pos.Raw × Syntax)) :
    Array (String.Pos.Raw × String.Pos.Raw × Syntax) :=
  match t with
  | .context _ t => usesOf p t acc
  | .node (.ofMacroExpansionInfo mi) children =>
    let acc := match mi.stx.getPos?, mi.stx.getTailPos? with
      | some a, some b => if p mi.stx.getKind then acc.push (a, b, mi.stx) else acc
      | _, _ => acc
    children.foldl (fun acc c => usesOf p c acc) acc
  | .node _ children => children.foldl (fun acc c => usesOf p c acc) acc
  | .hole _ => acc

/-- Expand the macros of library kinds in a syntax tree, to a fixed point,
leaving every other node as it is: what the elaborator did in steps, done
at once so that the result can be printed in place of the use. -/
partial def expandLibrary (p : Name → Bool) (stx : Syntax) : Elab.Command.CommandElabM Syntax := do
  if p stx.getKind then
    match ← Elab.liftMacroM (Elab.expandMacroImpl? (← getEnv) stx) with
    | some (_, .ok stx') => expandLibrary p stx'
    | _ => expandArgs stx
  else
    expandArgs stx
where
  expandArgs (stx : Syntax) : Elab.Command.CommandElabM Syntax := do
    match stx with
    | .node info kind args => return .node info kind (← args.mapM (expandLibrary p))
    | _ => return stx

unsafe def commandsMode (file outPath : String) (categories : List String) : IO UInt32 := do
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
  -- the syntax kinds of the library's categories, and every macro expansion
  -- of a use of them, pretty-printed as the term it stands for
  -- `cat:<name>` tokens name the categories, `mod:<module>` the modules
  -- declaring them, whose every notation is expanded at its uses
  let cats := Lean.Parser.parserExtension.getState s.commandState.env |>.categories
  let mut kinds : Array Name := #[]
  let mut mods : Array Name := #[]
  for c in categories do
    if c.startsWith "cat:" then
      if let some cat := cats.find? (c.drop 4).toName then
        kinds := kinds ++ cat.kinds.toList.toArray.map Prod.fst
    else if c.startsWith "mod:" then
      mods := mods.push (c.drop 4).toName
  let env' := s.commandState.env
  let isLibraryKind (k : Name) : Bool :=
    kinds.contains k || (match moduleOf env' k with | some m => mods.contains m | none => false)
  let mut macros : Array (Nat × Nat × String) := #[]
  if !kinds.isEmpty || !mods.isEmpty then
    let ctx : Elab.Command.Context := { fileName := file, fileMap := inputCtx.fileMap,
                                        snap? := none, cancelTk? := none }
    let ref ← IO.mkRef s.commandState
    -- a `scoped notation` is active only inside its namespace, which the
    -- file's final `end` closed: reopen the root namespace of every module
    -- whose notations are to be expanded, so that their macros fire
    for m in mods do
      match Parser.runParserCategory s.commandState.env `command s!"open {m.getRoot}" with
      | .ok stx => discard <| ((Elab.Command.elabCommand stx) ctx ref).toBaseIO
      | .error e => IO.eprintln s!"cannot open {m.getRoot}: {e}"
    for tree in s.commandState.infoState.trees do
      for (p, q, use) in usesOf isLibraryKind tree #[] do
        match ← ((expandLibrary isLibraryKind use) ctx ref).toBaseIO with
        | .ok (output : Syntax) =>
          let clean := output.rewriteBottomUp fun stx => match stx with
            | .ident info raw val pre => .ident info raw val.eraseMacroScopes pre
            | stx => stx
          try
            let fmt ← runCore s.commandState.env (PrettyPrinter.ppTerm ⟨clean⟩)
            macros := macros.push (p.byteIdx, q.byteIdx, fmt.pretty)
          catch e =>
            IO.eprintln s!"cannot print the expansion at {p.byteIdx}: {e}"
        | .error e =>
          IO.eprintln s!"cannot expand the notation at {p.byteIdx}: {← e.toMessageData.toString}"
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
    let inside := macros.filter fun (a, b, _) => pos.byteIdx ≤ a && b ≤ tail.byteIdx
    out := out.push (Json.mkObj [("kind", toString cmd.getKind),
      ("start", pos.byteIdx), ("end", tail.byteIdx), ("line", p.line), ("endLine", q.line),
      ("expansion", exp),
      ("macros", Json.arr (inside.map fun (a, b, t) =>
        Json.mkObj [("start", a), ("end", b), ("text", t)]))])
  let mut errors : Array String := #[]
  for m in s.commandState.messages.toList do
    if m.severity == .error then
      errors := errors.push (← m.data.toString)
  IO.FS.writeFile outPath (Json.mkObj [("version", 2), ("file", file), ("commands", Json.arr out),
    ("errors", toJson errors)]).pretty
  IO.println s!"{out.size} commands, {errors.size} errors"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  match args with
  | "closure" :: pfx :: out :: targets => closureMode pfx out targets
  | "commands" :: file :: out :: categories => commandsMode file out categories
  | _ => IO.eprintln "usage: Slice.lean closure <prefix> <out> <target>... | commands <file> <out> [<category>...]"; return 1
