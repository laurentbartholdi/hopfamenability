/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Lean

/-! Local kernel comparison of the independent statement and its dependencies.
This is a development check, not Comparator's sandboxed export/replay protocol. -/
open Lean

private def normalized (info : ConstantInfo) (e : Expr) : Expr :=
  e.instantiateLevelParams info.levelParams
    ((List.range info.levelParams.length).map fun i => Level.param (.num `level i))

/-- Elaborator-generated proof names depend on declaration order. Inline their
proofs before comparing; the kernel still checks the resulting expressions. -/
private partial def expandAuxProofs (env : Environment) (e : Expr) : Expr :=
  e.replace fun e => do
    let .const name levels := e | none
    unless (name.toString.splitOn "_proof_").length > 1 do none
    let info ← env.find? name
    let value ← info.value? (allowOpaque := true)
    return expandAuxProofs env (value.instantiateLevelParams info.levelParams levels)

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let config ← IO.FS.readFile "comparator.json"
  let json ← IO.ofExcept (Json.parse config)
  let roots ← IO.ofExcept (json.getObjValAs? (Array String) "theorem_names")
  let challenge ← importModules #[{ module := `Challenge }] {} 0
  let solution ← importModules #[{ module := `Solution }] {} 0
  let challengeIdx := challenge.getModuleIdx? `Challenge
  let mut pending := roots.map String.toName
  let mut visited : NameSet := {}
  let mut count := 0
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    unless challenge.getModuleIdxFor? name == challengeIdx do continue
    let some c := challenge.find? name | throw (IO.userError s!"Missing Challenge declaration: {name}")
    let some s := solution.find? name | throw (IO.userError s!"Missing Solution declaration: {name}")
    unless c.levelParams.length == s.levelParams.length do
      throw (IO.userError s!"Universe parameter mismatch: {name}")
    unless Lean.Kernel.isDefEqGuarded solution {} (normalized c (expandAuxProofs challenge c.type))
        (normalized s (expandAuxProofs solution s.type)) do
      throw (IO.userError s!"Independent type mismatch: {name}")
    pending := pending ++ (expandAuxProofs challenge c.type).getUsedConstants
    match c with
    | .defnInfo _ =>
      let some cv := c.value? | throw (IO.userError s!"Missing Challenge value: {name}")
      let some sv := s.value? | throw (IO.userError s!"Missing Solution value: {name}")
      unless Lean.Kernel.isDefEqGuarded solution {} (normalized c (expandAuxProofs challenge cv))
          (normalized s (expandAuxProofs solution sv)) do
        throw (IO.userError s!"Independent definition mismatch: {name}")
      pending := pending ++ (expandAuxProofs challenge cv).getUsedConstants
    | .inductInfo ci =>
      let .inductInfo si := s | throw (IO.userError s!"Inductive kind mismatch: {name}")
      unless ci.ctors == si.ctors do throw (IO.userError s!"Constructor mismatch: {name}")
      pending := pending ++ ci.ctors.toArray
    | .axiomInfo _ => throw (IO.userError s!"Unexpected statement axiom: {name}")
    | _ => pure ()
    count := count + 1
  IO.println s!"Independent kernel comparison passed for {roots.size} claims and {count} statement declarations."
