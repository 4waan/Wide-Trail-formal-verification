/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Rijndael.MixColumns
import WideTrail.Rijndael.Checks.MixColumns
import WideTrail.Rijndael.Checks.Axioms

/-!
# Rijndael at block widths 192 and 256

* `MixColumns`: Rijndael's `MixColumns` on a `4 × cols` state for every `cols`, the AES matrix
  applied to each column (`mixColumns`; at `cols = 4` it is `aesMixColumns`). Every column
  active on either side carries at least `5` active bytes across input and output
  (`mixColumns_isColBranchBound`), and the whole-state layer `MixColumns ∘ ShiftRows` has branch
  number at least `5` for every offset vector (`lin_isBranchBound`). With this map, every
  differential trail (`IsTrail`) with a nonzero input pattern has at least `25` active S-boxes in
  any four consecutive rounds, at least `80` in `14` rounds of Rijndael-256 (`Nb = 8`, offsets
  `0, 1, 3, 4`) and at least `75` in `12` rounds of Rijndael-192 (`Nb = 6`), with no hypothesis
  on `MixColumns`; the functional-trail statements of `Propagation/Rijndael.lean` follow;
* `Checks.MixColumns`: `MixColumns` at width `8` reproduces the `MixColumns` steps of rounds 1
  and 2 of FIPS 197-upd1 Appendix B, and the transposed matrix does not; an invertible matrix
  with one entry changed from `01` to `00` fails the branch hypotheses on `GridIdx 4 8` and is
  not MDS; the branch bound `5` cannot be raised to `6`; the hypothesis `T 0 ≠ 0` is needed;
* `Checks.Axioms`: pinned axiom footprints.

## What is not claimed

This file only imports the modules above and proves nothing itself. The bounds are lower bounds
on active S-boxes in the trail model of `WideTrailSpec`, in which every round includes
`MixColumns`; they are not claimed to be attained, and nothing here is about probabilities, the
S-box, the key schedule, a fixed key, linear trails, differentials, the final round without
`MixColumns`, or any attack. The claims are those of the individual modules.
-/

set_option autoImplicit false

namespace Rijndael

end Rijndael
