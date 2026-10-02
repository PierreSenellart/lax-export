/-
Copyright 2026 Pierre Senellart
SPDX-License-Identifier: Apache-2.0
-/
/-
Checks a built Lax proofs package the way the Lax archive will: every constant
the package declares carries its prefix, and the targets rest on the
background axioms only. Run with the toolchain on PATH and the package's
build plus its dependencies' on LEAN_PATH:

  lean --run Check.lean <package prefix, e.g., Lax261Proofs> <target constant>...
-/
import Lean

open Lean

def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let pkg :: targets := args
    | IO.eprintln "usage: Check.lean <package prefix> <target>..."; return 1
  let pfx := pkg.toName
  let env ← importModules #[{ module := pfx }] {} (trustLevel := 0) (loadExts := true)
  let mut n := 0
  let mut bad : Array Name := #[]
  for (c, _) in env.constants.map₁.toList do
    if let some m := moduleOf env c then
      if pfx.isPrefixOf m then
        n := n + 1
        -- reserved names (`f.eq_1`, `f.congr_simp`) are realized on demand in
        -- whichever package first needs them, and the archive exempts them
        if !pfx.isPrefixOf c && !c.isInternal && !isReservedName env c then bad := bad.push c
  IO.println s!"constants in package: {n}; outside prefix: {bad.size}"
  for c in bad.qsort (fun a b => a.toString < b.toString) do IO.println s!"  {c}"
  let background : List Name := [`propext, `Classical.choice, `Quot.sound]
  -- the statements of the submission's own concept package (`LaxN` for
  -- `LaxNProofs`) are admissible assumptions, as for the archive
  let concepts := (if pkg.endsWith "Proofs" then pkg.dropRight 6 else pkg).toName
  let mut failures := 0
  for t in targets do
    let (axs, _) ← (collectAxioms t.toName : CoreM (Array Name)).toIO
      { fileName := "<check>", fileMap := FileMap.ofString "" } { env }
    let extra := axs.toList.filter fun a => !background.contains a && !concepts.isPrefixOf a
    IO.println s!"{t}: {axs.toList}"
    if !extra.isEmpty then failures := failures + 1
  return if failures == 0 then 0 else 2
