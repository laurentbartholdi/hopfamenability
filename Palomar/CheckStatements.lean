/-
Copyright (c) 2026 Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bartholdi, based on code by ChatGPT 5.6 Sol
-/

import Lean

/-! Strict structural comparison of the independent statements and their dependencies.
Match Comparator's declaration equality: do not unfold definitions, rename universe
parameters, or inline generated proofs. Kernel definitional equality is weaker and
can accept packages rejected by Comparator. This development check does not replace
Comparator's sandboxed export/replay protocol. -/
open Lean

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let config ← IO.FS.readFile "comparator.json"
  let json ← IO.ofExcept (Json.parse config)
  let roots ← IO.ofExcept (json.getObjValAs? (Array String) "theorem_names")
  let challengeModule := args.headD "Challenge" |>.toName
  let challenge ← importModules #[{ module := challengeModule }] {} 0
  let solution ← importModules #[{ module := `Solution }] {} 0
  let challengeIdx := challenge.getModuleIdx? challengeModule
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
    if roots.contains name.toString then
      unless c.toConstantVal == s.toConstantVal do
        throw (IO.userError s!"Independent theorem statement mismatch: {name}")
    else
      unless c == s do
        throw (IO.userError s!"Independent declaration mismatch: {name}")
      if let some value := c.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
      match c with
      | .inductInfo ci => pending := pending ++ ci.ctors.toArray ++ ci.all.toArray
      | .ctorInfo ci => pending := pending.push ci.induct
      | .recInfo ri =>
        for rule in ri.rules do
          pending := pending.push rule.ctor ++ rule.rhs.getUsedConstants
      | _ => pure ()
    pending := pending ++ c.type.getUsedConstants
    count := count + 1
  IO.println s!"Strict declaration comparison passed for {roots.size} claims and {count} statement declarations."
