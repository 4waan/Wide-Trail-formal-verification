/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Masked
import WideTrail.Hades.Schedule
import WideTrail.Hades.Bounds
import WideTrail.Hades.Counting
import WideTrail.Hades.Probability
import WideTrail.Hades.Subspace
import WideTrail.Hades.Hull
import WideTrail.Hades.Krylov
import WideTrail.Hades.Dimension
import WideTrail.Hades.MiddleBound
import WideTrail.Hades.RelationCheck
import WideTrail.Hades.WindowRelation
import WideTrail.Hades.Checks.Toy
import WideTrail.Hades.Checks.Counting
import WideTrail.Hades.Checks.Krylov
import WideTrail.Hades.Checks.Dimension
import WideTrail.Hades.Checks.MiddleBound
import WideTrail.Hades.Checks.WindowRelation
import WideTrail.Hades.Checks.Axioms

/-! Scheduled masked rounds, activity bounds for full outer blocks, inactive
propagation through partial rounds, lower bounds on the partial rounds taken as a
hypothesis (`MiddleBound.lean`) and proved from window-relation certificates
(`WindowRelation.lean`, with the Boolean checker `RelationCheck.lean`), and a bound on the
key-averaged differential over two full rounds in the additional-independent-key model
(`Hull.lean`). -/
