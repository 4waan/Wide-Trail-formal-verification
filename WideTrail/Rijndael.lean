/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Rijndael.MixColumns
import WideTrail.Rijndael.Probability
import WideTrail.Rijndael.Checks.MixColumns
import WideTrail.Rijndael.Checks.Probability
import WideTrail.Rijndael.Checks.Axioms
import WideTrail.Rijndael.Checks.ProbabilityAxioms

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
* `Probability`: in the independent-key model (an independent uniform key added before each
  round, every probability averaged over all key vectors), for S-boxes that are injective with
  differential uniformity at most `4` (the AES S-box is one), every differential trail of
  Rijndael-256 with a nonzero input difference has probability at most `2⁻¹⁵⁰` over `4` rounds,
  `2⁻³⁰⁰` over `8` and `2⁻⁴⁸⁰` over `14` (`rijndael256_{four,eight,fourteen}_round_prob`). The
  `14`-round bound also holds with `ShiftRows` alone in the last round
  (`rijndael256_fourteen_round_prob_final`), and so do the AES bounds `2⁻³³⁰`, `2⁻⁴⁵⁰` and
  `2⁻⁴⁸⁰` for AES-128, AES-192 and AES-256 (`aes128_ten_round_prob_final`,
  `aes192_twelve_round_prob_final`, `aes256_fourteen_round_prob_final`). With the AES S-box,
  every two-round differential with a nonzero input difference has probability at most `2⁻²⁴`,
  for Rijndael-256 and for AES-128 (`rijndael256_two_round_differential`,
  `aes128_two_round_differential`); this bound is coarse, and for AES the exact maximum
  two-round value, averaged over independent round keys, is `53 / 2³⁴` (Keliher and Sui);
* `Checks.MixColumns`: `MixColumns` at width `8` reproduces the `MixColumns` steps of rounds 1
  and 2 of FIPS 197-upd1 Appendix B, and the transposed matrix does not; an invertible matrix
  with one entry changed from `01` to `00` fails the branch hypotheses on `GridIdx 4 8` and is
  not MDS; the branch bound `5` cannot be raised to `6`; the hypothesis `T 0 ≠ 0` is needed;
* `Checks.Probability`: no differential uniformity bound of the AES S-box clears `2⁷` per active
  S-box (`4 · 2⁷ > 256`); eight is the first round count at which the trail exponent exceeds
  `256`; the hypotheses `T 0 ≠ 0` and `a ≠ 0` are needed; the last round of the final-round
  schedule is not the full linear layer;
* `Checks.Axioms`, `Checks.ProbabilityAxioms`: pinned axiom footprints.

## What is not claimed

This file only imports the modules above and proves nothing itself. The activity bounds are lower
bounds on active S-boxes in the trail model of `WideTrailSpec`, in which every round includes
`MixColumns`. The real last round, with `ShiftRows` alone, enters only probability statements: the
`_final` trail bounds, and `rijndael256_differential` and `aes128_differential`, which allow any
linear maps after round `0`. The probability bounds are in the independent-key model. No bound is
claimed to be attained. A trail bound bounds one summand of a differential, and no bound here is
about the key schedule, a fixed key, related keys, differentials over more than two charged rounds,
linear trails, or any attack. The claims are those of the individual modules.
-/

set_option autoImplicit false

namespace Rijndael

end Rijndael
