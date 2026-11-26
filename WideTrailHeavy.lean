/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail
import WideTrail.Poseidon2.Checks.Plonky3
import WideTrail.Poseidon2.Checks.KoalaBear
import WideTrail.Poseidon2.Checks.BabyBear

/-!
# The memory-heavy checks

Everything in `WideTrail`, plus the three check modules that evaluate whole width-16
Poseidon2 permutations in the kernel. Elaborating them peaks at about 7 GB
(`WideTrail.Poseidon2.Checks.Plonky3`, `WideTrail.Poseidon2.Checks.BabyBear`) and 12 GB
(`WideTrail.Poseidon2.Checks.KoalaBear`). Lake builds independent modules in parallel, so
build them one at a time:

```
lake build WideTrail.Poseidon2.Checks.KoalaBear
lake build WideTrail.Poseidon2.Checks.BabyBear
lake build WideTrail.Poseidon2.Checks.Plonky3
lake build WideTrailHeavy
```

`scripts/AuditAxiomsHeavy.lean` audits every declaration of this library, which includes
all of `WideTrail`.
-/
