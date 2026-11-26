/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrailHeavy
import Lean.Util.CollectAxioms

/-!
# Audit every declaration defined by a project module, heavy checks included

The defining module identifies project declarations even when their names live
in the root namespace. Every axiom is collected transitively through imports.

This audits `WideTrailHeavy`: all of `WideTrail` and the three memory-heavy check
modules. Build them first, one at a time (see `WideTrailHeavy.lean`).
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if (`WideTrail).isPrefixOf modName then
        let axioms ← Lean.collectAxioms name
        let unexpected := axioms.filter (fun ax => !allowed.contains ax)
        unless unexpected.isEmpty do
          throwError "{name}: unexpected axioms {unexpected}"
        checked := checked + 1
  if checked = 0 then
    throwError "Axiom audit selected no project declarations"
  logInfo m!"Audited {checked} project declarations: only propext, Classical.choice, Quot.sound."
