/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BN254
import WideTrail.Poseidon2.BN254Middle
import WideTrail.Poseidon2.BN254Execution
import WideTrail.Poseidon2.BN254Checks
import WideTrail.Poseidon2.Checks.BN254SP1
import WideTrail.Poseidon2.Plonky3
import WideTrail.Poseidon2.KoalaBear
import WideTrail.Poseidon2.BabyBear
import WideTrail.Poseidon2.PicoKoalaBear
import WideTrail.Poseidon2.OpenVMBabyBear
import WideTrail.Poseidon2.Plonky3Execution
import WideTrail.Poseidon2.Checks.Plonky3KAT
import WideTrail.Poseidon2.Checks.PicoKoalaBear
import WideTrail.Poseidon2.Checks.OpenVMBabyBear
import WideTrail.Poseidon2.Checks.Axioms

/-! Pinned concrete Poseidon2 parameter certificates.

The checks `Checks.Plonky3`, `Checks.KoalaBear` and `Checks.BabyBear` evaluate whole
width-16 permutations in the kernel and need about 7 to 12 GB of memory each. They are
not imported here, so that the default `lake build` fits on a laptop; the separate
library `WideTrailHeavy` imports them. -/
