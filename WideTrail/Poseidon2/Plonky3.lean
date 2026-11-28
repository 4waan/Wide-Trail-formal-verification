/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.BlockCirculant
import WideTrail.Algebra.MDS4
import WideTrail.Algebra.Transpose
import WideTrail.Hades.Krylov
import WideTrail.Hades.Dimension
import WideTrail.Hades.Hull
import Mathlib.Tactic.FinCases

/-!
# The Plonky3 Poseidon2 permutation of width sixteen, for every internal diagonal

SP1 hashes with Plonky3's `Poseidon2<F, Poseidon2ExternalMatrixGeneral, DiffusionMatrix…, 16, D>`:
KoalaBear with `D = 3` in `sp1-primitives` `6.10.0` (`src/lib.rs:1145`), BabyBear with `D = 7`
in `sp1-primitives` `5.2.4` (`src/lib.rs:1106-1124`). Both run the same skeleton, from the
byte-identical sources of `p3-poseidon2` `0.4.3-succinct` and `0.2.3-succinct`. This file models
that skeleton over an arbitrary field `K` and for an arbitrary internal diagonal
`d : Fin 16 → K` (the namespace `Diag`), and then specialises it to SP1's diagonal `sp1Diag`.
Every condition on `K` and `d` is an explicit hypothesis that a concrete prime field and a
literal diagonal discharge by `decide`; the generic layer fixes no field, diagonal, S-box, scale
or constant table. If a width-sixteen instance runs this skeleton with another internal
diagonal, the `Diag` results apply to it, each under its stated hypotheses: `Diag.Conditions`
for the schedule, plus the `m4Primes` hypothesis for the activity, trail and differential bounds,
and an inactive-space hypothesis for the `_with_middle` forms.

## The model

A state is `Fin 16 → K`, and coordinate `i` is the Rust `state[i]`. Block `b`, position `c` is
coordinate `4 b + c` (`blockIndex`, Mathlib's `finProdFinEquiv`; `blockIndex_val`).

* `external h35`: the external layer `circ(2 M4, M4, M4, M4)`, where `M4 = m4 = circ(2, 3, 1, 1)`
  is Plonky3's `MDSMat4`. It is `BlockCirculant.blockMixEquiv` with `N = m4Equiv`, conjugated to
  the flat state, and needs only `35 ≠ 0`. The code (`mds_light_permutation`, `p3-poseidon2`
  `src/matrix.rs:110-139`, called at `:156`) applies `M4` to each block and then adds position
  sums; `external_apply_blockIndex` states
  `out[4 b + c] = (M4 x_b)[c] + ∑_{b'} (M4 x_{b'})[c]`, and `external_eq_mdsLight` identifies the
  layer with `mdsLight`, a transcription of those lines. It does not depend on the diagonal.
* `Diag.internal d c hc hd hs`: `x_i ↦ c (d_i x_i + ∑_j x_j)` for a diagonal `d` and a scale
  `c`, the linear equivalence `diagPlusOnesEquiv` of `WideTrail.Algebra.DiagPlusOnes`. It takes
  as hypotheses `c ≠ 0`, `d i ≠ 0` for every `i` and the Sherman–Morrison condition
  `1 + ∑_i 1/d_i ≠ 0`; under the first two, the Sherman–Morrison condition is exact
  (`Poseidon2.diagPlusOnes_injective_iff`).
* `Diag.Conditions d c` bundles `35 ≠ 0`, `d i ≠ 0`, `1 + ∑ 1/d_i ≠ 0` and `c ≠ 0`, under which
  both layers are invertible. `Diag.Conditions.of_mul_eq_one` derives it from a table `e` with
  `d i * e i = 1` and from `1 + ∑ e_i ≠ 0`, which `decide` checks in `ZMod p` without computing an
  inverse.
* `Diag.rounds hD rP sbox values = Hades.hadesSchedule 4 rP 4 {0} (fun _ _ => sbox)
  (Diag.linear hD rP) values`: four full rounds, `rP` partial rounds with the S-box on
  coordinate `0`, four full rounds, the same S-box `sbox` everywhere (intended: `x ↦ x^D`), the
  external layer in full rounds and the internal layer in partial rounds. The code runs
  `rounds_f_half = rounds_f / 2` full rounds on each side (`p3-poseidon2` `src/lib.rs:182`), and
  SP1 sets `ROUNDS_F = 8` (`slop-koala-bear` `6.10.0` `src/koala_bear_poseidon2.rs:49`;
  `sp1-primitives` `5.2.4` `src/lib.rs:1108`), hence four. SP1 sets `ROUNDS_P = 20` for
  KoalaBear (`slop-koala-bear` `6.10.0` `src/koala_bear_poseidon2.rs:50`) and `ROUNDS_P = 13`
  for BabyBear (`sp1-primitives` `5.2.4` `src/lib.rs:1109`).
* `Diag.permutation hD rP sbox values x = Hades.execute (Diag.rounds hD rP sbox values)
  (external x) (8 + rP)`: the initial external layer (`p3-poseidon2` `src/lib.rs:179`), then the
  three loops of `src/lib.rs:182-201`.

**The SP1 diagonal.** `sp1Diag = (-2, 1, 2, 4, …, 2^13, 2^15)` (`p3-koala-bear` `0.4.3-succinct`
`src/poseidon2.rs:37-58`; the same vector in `p3-baby-bear` `0.2.3-succinct`
`src/poseidon2.rs:29-49`). The code works on Montgomery representatives and returns
`R^{-1} (d_i x_i + ∑_j x_j)` with `R = 2^32` (`MONTY_BITS = 32`, `p3-koala-bear`
`src/koala_bear.rs:21`, `p3-baby-bear` `src/baby_bear.rs:17`; the layer at `p3-koala-bear`
`src/poseidon2.rs:95-113`, `p3-baby-bear` `src/poseidon2.rs:85-103`). The scale `c` is a
parameter whose intended value is `R^{-1}`, i.e. `c * 2^32 = 1`; only `c ≠ 0` is used.
`internal c hc h2 hs` is `Diag.internal (sp1Diag K) c` (`internal_eq_diag`): for this diagonal
`d i ≠ 0` follows from `2 ≠ 0` (`sp1Diag_ne_zero`) and `1 + ∑ 1/d_i ≠ 0` is `81917 ≠ 0`, where
`81917 = 11^2 * 677 = 2^15 (1 + ∑ 1/d_i)` (`one_add_sum_inv_ne_zero_iff`);
`internal_injective_iff` shows the second condition is exact. `Conditions c` bundles `35 ≠ 0`,
`2 ≠ 0`, `81917 ≠ 0` and `c ≠ 0`, and `Conditions.toDiag` turns it into
`Diag.Conditions (sp1Diag K) c`. `linear hK`, `rounds hK` and `permutation hK` are
`Diag.linear`, `Diag.rounds` and `Diag.permutation` at `hK.toDiag`, by `rfl`
(`linear_eq_diag`, `rounds_eq_diag`, `permutation_eq_diag`). `Conditions.of_primes` derives
`Conditions c` from the `m4Primes` hypothesis, `677 ≠ 0` and `c ≠ 0`. So `Conditions c` and the
`m4Primes` hypothesis of the branch bound both hold over every field whose characteristic is none
of `2, 3, 5, 7, 11, 17, 677`, for every nonzero `c`.

**Partial-round constants.** A HADES round adds a whole row `values n`, but the code adds a
partial-round constant to `state[0]` only (`p3-poseidon2` `src/lib.rs:191`). Tables whose partial
rows vanish off coordinate `0` (`PartialRowsAtZero`) model exactly that: `Diag.rounds_apply_middle`
shows such a round is the code's round `internal (update x 0 (sbox (x 0 + v)))`, for every
diagonal. `roundValues` builds such a table from the eight external rows the full-round loops read
and the `rP` internal scalars. `Diag.rounds_apply_prefix` and `Diag.rounds_apply_suffix` give the
full rounds. A raw constant table need not have this form: SP1 `5.2.4`'s BabyBear table
`RC_16_30` is not `PartialRowsAtZero`, and the code's table is `roundValues 13 ext int` built from
parts of it (see `roundValues`).

## Results, for every diagonal and every round-constant table

Each `Diag` result below holds for every field `K`, every diagonal `d` and scale `c` meeting its
hypotheses, every S-box, every number `rP` of partial rounds and every constant table. Results
about the schedule take `hD : Diag.Conditions d c`; results about the internal layer alone take
`c ≠ 0`, `d i ≠ 0` and `1 + ∑ 1/d_i ≠ 0` separately, or no hypothesis for the unscaled
`diag d + J`. The activity, trail and differential bounds also take the `m4Primes` hypothesis of
the branch bound.

* `Diag.permutation_bijective`.
* `external_isBranchBound`: under the `m4Primes` hypothesis the external layer has branch number
  at least `8`.
* `Diag.activity`: two distinct inputs incur at least `32` charged S-box applications, all
  counted in the full rounds. `Diag.activity_with_middle` adds `rP / w` when no nonzero
  difference stays inactive through `w` consecutive partial rounds with the unscaled layer
  `diag d + J`; by `Diag.inactiveSpace_internal` the scale does not matter, so a Krylov
  certificate (`Hades.inactiveSpace_diagPlusOnes_eq_bot`) need not mention `c`.
* `Diag.independent_key_probability`, `Diag.independent_key_probability_with_middle`: if `sbox`
  has differential uniformity at most `u` and `u * 2^dd ≤ |K|`, then for every nonzero trail `T`,
  `keyCount * 2^(dd * 32) ≤ |K^16|^(8 + rP)`, and with exponent `dd * (32 + rP / w)` under the
  inactive-space hypothesis.
* `Diag.independent_key_probability_exact`, `Diag.independent_key_probability_with_middle_exact`:
  the same bounds with the ratio `|K| / u` kept exact and no relation between `u` and `|K|`
  assumed: `keyCount * |K|^32 ≤ u^32 * |K^16|^(8 + rP)`, and with `32 + rP / w` in place of `32`
  under the inactive-space hypothesis.
* `Diag.independent_key_probability_sharp`, `Diag.independent_key_probability_with_middle_sharp`:
  the exact-ratio bounds with a power of two, `keyCount * 2^e ≤ |K^16|^(8 + rP)`, for every `e`
  with `2^e u^n ≤ |K|^n`, where `n` is the number of charged S-boxes and `0 < u`. An instance
  takes the largest `e` this arithmetic gives.
* `Diag.finrank_inactiveSpace_internal`: at least `16 - r` dimensions of differences stay
  inactive through `r` consecutive partial rounds. A difference entering the partial rounds in
  that space crosses them with no charged S-box (`Hades.IsTrail.free_window`), and
  `Diag.middle_term_eq_zero` shows that for `rP < 16` the middle term `rP / w` is `0`.
* `Diag.inactiveSpace_sixteen_eq_bot_iff`: no nonzero difference stays inactive through sixteen
  consecutive partial rounds with `diag d + J` exactly when the diagonal entries `d i`, `i ≠ 0`,
  are pairwise distinct in `K`, i.e. `Set.InjOn d {i | i ≠ 0}`
  (`Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff`). Under that condition
  `Diag.inactiveSpace_internal_sixteen_eq_bot` states the same for the scaled layer, and
  `Diag.finrank_inactiveSpace_internal_eq` makes `Diag.finrank_inactiveSpace_internal` exact:
  `16 - r` dimensions for `r ≤ 16`. This is a second route to the inactive-space hypothesis of
  `Diag.activity_with_middle` with `w = 16`, with no Krylov table. When two of those entries
  coincide, some nonzero difference stays inactive through any number of consecutive partial
  rounds (`Diag.inactiveSpace_ne_bot_of_not_injOn`), so no window meets that hypothesis.
* `Diag.independent_key_differential_exact`, `Diag.independent_key_differential_sharp`: under the
  `m4Primes` hypothesis, if `sbox` has differential uniformity at most `u`, then in the same
  model, for every nonzero input difference `a`, every output difference `b` and every input `x`,
  the key count of the differential `(a, b)` over the `8 + rP` rounds that follow the initial
  external layer satisfies `diffKeyCount * |K|^7 ≤ u^7 * |K^16|^(8 + rP)`, and
  `diffKeyCount * 2^e ≤ |K^16|^(8 + rP)` when `2^e u^7 ≤ |K|^7` and `0 < u`. Only `7` S-boxes of
  the first two full rounds are charged, one fewer than the branch number `8`
  (`Hades.hades_differential_bound`).

## Results for the SP1 diagonal

The SP1 forms carry the same names without `Diag.`. `permutation_bijective`, `activity`,
`activity_with_middle`, `independent_key_probability`, `independent_key_probability_with_middle`,
the two `_exact` forms, `independent_key_differential_exact` and the round lemmas take
`hK : Conditions c`; `inactiveSpace_internal`, `finrank_inactiveSpace_internal`,
`inactiveSpace_internal_ne_bot`, `inactiveSpace_internal_sixteen_eq_bot`,
`finrank_inactiveSpace_internal_eq` and `internal_dotProduct` take the scalars `c hc h2 hs`;
`middle_term_eq_zero` and `inactiveSpace_sixteen_eq_bot_iff` take neither. Each is the `Diag`
result at `d = sp1Diag K`: `Conditions.toDiag`, or `sp1Diag_ne_zero` and
`one_add_sum_inv_ne_zero_iff` directly, discharge `d i ≠ 0` from `2 ≠ 0` and the
Sherman–Morrison condition from `81917 ≠ 0`, and the inactive-space hypotheses are stated for
`diag (sp1Diag K) + J`. In particular at least `3` dimensions of differences stay inactive
through thirteen consecutive partial rounds (`three_le_finrank_inactiveSpace_thirteen`), and with
`w = 16` the middle term is `20 / 16 = 1` for `rP = 20` and `0` for `rP = 13`. The sharp forms
for SP1's two fields are in `WideTrail.Poseidon2.KoalaBear` and `WideTrail.Poseidon2.BabyBear`.

## Structure of the linear layers

* `blockSumZeroFlat`: the states whose four blocks of four coordinates sum to zero, a subspace
  of dimension `12` (`finrank_blockSumZeroFlat`). Under `35 ≠ 0`, `external h35 x = mat4Blocks x`
  (`M4` on each block, with no mixing between blocks) exactly when `x` lies in it
  (`external_eq_mat4Blocks_iff`), and `external h35 x` lies in it exactly when `x` does
  (`external_mem_blockSumZeroFlat_iff`). Over every commutative ring the position sums of
  `mdsLight x` are `5` times `M4` applied to those of `x` (`positionSums_mdsLight`). These
  concern the external layer and hold whatever the diagonal.
* `external_dotProduct`: the transpose of the external layer is `circ(2 m4ᵀ, m4ᵀ, m4ᵀ, m4ᵀ)`, and
  under the `m4Primes` hypothesis it has branch number at least `8`
  (`external_transpose_isBranchBound`). `Diag.internal_dotProduct`: the internal layer is its own
  transpose, for every diagonal (`internal_dotProduct` for SP1's).

## What is not claimed

The activity counts are lower bounds on charged S-boxes for actual input pairs; they are not claimed
to be attained. The trail-probability statements concern one trail in the model with an additional
independent uniform key per round. The differential statements
(`Diag.independent_key_differential_exact`, `Diag.independent_key_differential_sharp`) bound the
key-averaged differential of the rounds after the initial external layer, in the same model, and
charge only `B - 1 = 7` S-boxes of the first two full rounds. None of these is a statement about
the permutation with its fixed constants, or about any one key. The `Diag` results hold for every
diagonal that meets their hypotheses; the only diagonal this file identifies with source code is
`sp1Diag`. Nothing is said about subspace-trail resistance beyond the inactive-space statements
here, about algebraic attacks, about sponge or duplex constructions built on the permutation, or
about equivalence with the Rust code or the AIR beyond the transcriptions stated here
(`external_eq_mdsLight` and the round lemmas). The inactive-space hypothesis can fail for some
fields (`Checks/Plonky3.lean`, `ZMod 23`). The block-sum and transpose statements concern the two
linear layers alone: they say nothing about the S-box or whole rounds, and no correlation, linear
trail, linear hull or linear-attack bound is proved.
-/

set_option autoImplicit false

namespace Poseidon2.Plonky3

open BlockCirculant

/-! ### Coordinates -/

/-- Block `b`, position `c` is coordinate `4 b + c` (`blockIndex_val`): the block
`state[4b..4b+4]` of `mds_light_permutation` (`p3-poseidon2` `0.4.3-succinct`
`src/matrix.rs:113-123`). This is Mathlib's `finProdFinEquiv`, which sends `(b, c)` to `c + 4 b`. -/
abbrev blockIndex : Fin 4 × Fin 4 ≃ Fin 16 := finProdFinEquiv

theorem blockIndex_val (b c : Fin 4) : (blockIndex (b, c) : ℕ) = 4 * b + c := by
  rw [finProdFinEquiv_apply_val]
  dsimp only
  omega

theorem blockIndex_symm_fst (i : Fin 16) : ((blockIndex.symm i).1 : ℕ) = i / 4 :=
  Fin.coe_divNat (m := 4) (n := 4) i

theorem blockIndex_symm_snd (i : Fin 16) : ((blockIndex.symm i).2 : ℕ) = i % 4 :=
  Fin.coe_modNat (m := 4) (n := 4) i

/-- Block `b` of a flat state: coordinates `4 b, …, 4 b + 3`. -/
def blockOf {α : Type*} (x : Fin 16 → α) (b : Fin 4) : Fin 4 → α :=
  fun c => x (blockIndex (b, c))

/-! ### The external layer -/

section Code

variable {R : Type*} [CommRing R]

/-- The first step of Plonky3's `mds_light_permutation` at width sixteen (`p3-poseidon2`
`0.4.3-succinct` `src/matrix.rs:113-123`): `M4` applied in place to each block
`state[i..i+4]`, `i = 0, 4, 8, 12`. Coordinate `i` of the result is coordinate `i % 4` of `M4`
applied to the block starting at `4 (i / 4)`. -/
def mat4Blocks (x : Fin 16 → R) : Fin 16 → R := fun i =>
  (m4 R).mulVec (fun c : Fin 4 => x ⟨4 * (i.val / 4) + c.val, by omega⟩) ⟨i.val % 4, by omega⟩

/-- `sums[k]`, the sum of the coordinates `j + k`, `j = 0, 4, 8, 12` (`src/matrix.rs:127-132`). -/
def positionSums (y : Fin 16 → R) (k : Fin 4) : R :=
  ∑ j : Fin 4, y ⟨4 * j.val + k.val, by omega⟩

/-- Plonky3's `mds_light_permutation::<_, MDSMat4, 16>` (`p3-poseidon2` `0.4.3-succinct`
`src/matrix.rs:110-139`), transcribed over any commutative ring: `M4` on each block of four
(`mat4Blocks`), then `state[i] += sums[i % 4]` (lines 136-138). -/
def mdsLight (x : Fin 16 → R) : Fin 16 → R := fun i =>
  mat4Blocks x i + positionSums (mat4Blocks x) ⟨i.val % 4, by omega⟩

theorem mat4Blocks_apply (x : Fin 16 → R) (i : Fin 16) :
    mat4Blocks x i = (m4 R).mulVec (blockOf x (blockIndex.symm i).1) (blockIndex.symm i).2 := by
  have h1 : (fun c' : Fin 4 => x ⟨4 * (i.val / 4) + c'.val, by omega⟩) =
      blockOf x (blockIndex.symm i).1 := by
    funext c'
    simp only [blockOf]
    congr 1
    apply Fin.ext
    rw [blockIndex_val, blockIndex_symm_fst]
  have h2 : (⟨i.val % 4, by omega⟩ : Fin 4) = (blockIndex.symm i).2 :=
    Fin.ext (blockIndex_symm_snd i).symm
  rw [mat4Blocks, h1, h2]

theorem positionSums_apply (y : Fin 16 → R) (k : Fin 4) :
    positionSums y k = ∑ j : Fin 4, y (blockIndex (j, k)) := by
  rw [positionSums]
  congr 1
  funext j
  congr 1
  exact Fin.ext (blockIndex_val j k).symm

/-- **The code's formula.** Coordinate `4 b + c` of `mdsLight x` is `(M4 x_b)[c]` plus the sum
over all blocks `b'` of `(M4 x_{b'})[c]`. -/
theorem mdsLight_apply (x : Fin 16 → R) (b c : Fin 4) :
    mdsLight x (blockIndex (b, c)) =
      (m4 R).mulVec (blockOf x b) c + ∑ b' : Fin 4, (m4 R).mulVec (blockOf x b') c := by
  have hc : (⟨(blockIndex (b, c)).val % 4, by omega⟩ : Fin 4) = c := by
    apply Fin.ext
    change (blockIndex (b, c)).val % 4 = c.val
    rw [blockIndex_val]
    omega
  rw [mdsLight, hc, positionSums_apply, mat4Blocks_apply, Equiv.symm_apply_apply]
  simp only [mat4Blocks_apply, Equiv.symm_apply_apply]

end Code

variable {K : Type*} [Field K]

/-- `35 ≠ 0` gives `5 ≠ 0`, the hypothesis `t + 1 ≠ 0` of `blockMixEquiv` for four blocks. -/
theorem five_ne_zero_of_thirtyFive (h35 : (35 : K) ≠ 0) :
    ((Fintype.card (Fin 4) + 1 : ℕ) : K) ≠ 0 := by
  rw [Fintype.card_fin]
  intro h5
  apply h35
  have h : ((4 + 1 : ℕ) : K) = 5 := by norm_num
  rw [h] at h5
  rw [show (35 : K) = 5 * 7 by norm_num, h5, zero_mul]

/-- **The external layer** `circ(2 M4, M4, M4, M4)` on the flat state, as a linear equivalence:
`BlockCirculant.blockMixEquiv` with `N = m4Equiv`, conjugated by `blockIndex`. Invertibility
needs only `35 ≠ 0` (`det M4 = -35`, and `5 ≠ 0` follows). -/
def external (h35 : (35 : K) ≠ 0) : (Fin 16 → K) ≃ₗ[K] (Fin 16 → K) :=
  (LinearEquiv.funCongrLeft K K blockIndex).trans
    ((blockMixEquiv (m4Equiv K h35) (five_ne_zero_of_thirtyFive h35)).trans
      (LinearEquiv.funCongrLeft K K blockIndex.symm))

theorem external_apply (h35 : (35 : K) ≠ 0) (x : Fin 16 → K) :
    external h35 x =
      blockMix (B := Fin 4) (m4Equiv K h35).toLinearMap (x ∘ blockIndex) ∘ blockIndex.symm :=
  rfl

/-- **The explicit Plonky3 formula.** `out[4 b + c] = (M4 x_b)[c] + ∑_{b'} (M4 x_{b'})[c]`:
`M4` is applied to every block, then the position sums of the images are added
(`p3-poseidon2` `0.4.3-succinct` `src/matrix.rs:110-139`). -/
theorem external_apply_blockIndex (h35 : (35 : K) ≠ 0) (x : Fin 16 → K) (b c : Fin 4) :
    external h35 x (blockIndex (b, c)) =
      (m4 K).mulVec (blockOf x b) c + ∑ b' : Fin 4, (m4 K).mulVec (blockOf x b') c := by
  rw [external_apply, Function.comp_apply, Equiv.symm_apply_apply, blockMix_apply_eq_add_sum]
  rfl

/-- **The external layer is the code's `mds_light_permutation`.** -/
theorem external_eq_mdsLight (h35 : (35 : K) ≠ 0) (x : Fin 16 → K) :
    external h35 x = mdsLight x := by
  funext i
  obtain ⟨⟨b, c⟩, rfl⟩ := blockIndex.surjective i
  rw [external_apply_blockIndex, mdsLight_apply]

section Branch

variable [DecidableEq K]

/-- **Branch number `8` for the external layer.** `m4` has branch number `5` under the
`m4Primes` hypothesis (`m4Equiv_isBranchBound`), and that hypothesis also makes `1, …, 5` nonzero
(`m4_natCast_ne_zero_of_le_five`), so `BlockCirculant.isBranchBound_blockMix_sixteen` applies. -/
theorem external_isBranchBound (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (h35 : (35 : K) ≠ 0) :
    isBranchBound id (external h35) 8 :=
  isBranchBound_blockMix_sixteen (N := (m4Equiv K h35).toLinearMap)
    (m4Equiv_isBranchBound hprimes h35) (m4_natCast_ne_zero_of_le_five hprimes)

end Branch

/-! ### Partial-round constants

These do not depend on the internal layer. -/

/-- The partial rows of a round-constant table vanish off the S-box coordinate. Plonky3 adds a
partial-round constant to `state[0]` only (`p3-poseidon2` `src/lib.rs:190-191`), and a HADES round
adds the whole row, so tables with this property are the ones the code can realise. A raw
constant table from a source need not have it; see `roundValues`. -/
def PartialRowsAtZero (rP : ℕ) (values : ℕ → Fin 16 → K) : Prop :=
  ∀ j < rP, ∀ i : Fin 16, i ≠ 0 → values (4 + j) i = 0

/-- The round-constant table the code reads: `ext` holds the eight external rows (the first
eight entries of the code's `external_constants`, read in order by the two full-round loops,
`p3-poseidon2` `src/lib.rs:183-184`, `:197-198`), and `int` the `rP` internal scalars
(`internal_constants`, line 191). Partial rows carry their scalar at coordinate `0` and zero
elsewhere.

SP1 `5.2.4`'s BabyBear table `RC_16_30` cannot be used directly as `values`: columns `1-15` of
its rows `4-16` are nonzero, so it is not `PartialRowsAtZero`, and the eight external rows that
the code reads are rows `0-3` and `17-20`, not a contiguous block. The code's table is
`roundValues 13 ext int` with `ext` rows `0-3` and `17-20` of `RC_16_30` and `int` column `0` of
rows `4-16` (`sp1-primitives` `5.2.4` `src/lib.rs:1110-1115`); `BabyBear.values_eq_roundValues`
states this for the pinned table. -/
def roundValues (rP : ℕ) (ext : Fin 8 → Fin 16 → K) (int : Fin rP → K) (n : ℕ) : Fin 16 → K :=
  if h : n < 4 then ext ⟨n, by omega⟩
  else if h' : n < 4 + rP then Pi.single 0 (int ⟨n - 4, by omega⟩)
  else if h'' : n < 8 + rP then ext ⟨n - rP, by omega⟩
  else 0

theorem roundValues_prefix (rP : ℕ) (ext : Fin 8 → Fin 16 → K) (int : Fin rP → K) {j : ℕ}
    (hj : j < 4) : roundValues rP ext int j = ext ⟨j, by omega⟩ := by
  simp [roundValues, hj]

theorem roundValues_middle (rP : ℕ) (ext : Fin 8 → Fin 16 → K) (int : Fin rP → K) {j : ℕ}
    (hj : j < rP) : roundValues rP ext int (4 + j) = Pi.single 0 (int ⟨j, hj⟩) := by
  simp [roundValues, show ¬(4 + j < 4) by omega, show 4 + j < 4 + rP by omega]

theorem roundValues_suffix (rP : ℕ) (ext : Fin 8 → Fin 16 → K) (int : Fin rP → K) {j : ℕ}
    (hj : j < 4) : roundValues rP ext int (4 + rP + j) = ext ⟨4 + j, by omega⟩ := by
  simp only [roundValues, show ¬(4 + rP + j < 4) by omega, show ¬(4 + rP + j < 4 + rP) by omega,
    show 4 + rP + j < 8 + rP by omega, dite_true, dite_false]
  congr 1
  apply Fin.ext
  simp only
  omega

theorem roundValues_partialRowsAtZero (rP : ℕ) (ext : Fin 8 → Fin 16 → K)
    (int : Fin rP → K) : PartialRowsAtZero rP (roundValues rP ext int) := by
  intro j hj i hi
  rw [roundValues_middle rP ext int hj, Pi.single_apply, if_neg hi]

/-! ### The internal layer for every diagonal -/

namespace Diag

/-- **The internal layer for a diagonal `d`**: `x ↦ c (diag d + J) x`, so coordinate `i` of the
image is `c (d_i x_i + ∑_j x_j)` (`Diag.internal_apply`). It is `diagPlusOnesEquiv` of
`WideTrail.Algebra.DiagPlusOnes`, and takes as hypotheses `c ≠ 0`, `d i ≠ 0` for every `i` and
`1 + ∑ 1/d_i ≠ 0`; under the first two, the last is exact
(`Poseidon2.diagPlusOnes_injective_iff`). -/
def internal (d : Fin 16 → K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) : (Fin 16 → K) ≃ₗ[K] (Fin 16 → K) :=
  diagPlusOnesEquiv c d hc hd hs

theorem internal_apply (d : Fin 16 → K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (x : Fin 16 → K) (i : Fin 16) :
    internal d c hc hd hs x i = c * (d i * x i + ∑ j, x j) :=
  rfl

theorem internal_toLinearMap (d : Fin 16 → K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) :
    (internal d c hc hd hs).toLinearMap = diagPlusOnes c d :=
  rfl

/-- **The scale is invisible to inactive differences**, for every diagonal: the inactive space of
the internal layer is that of `diag d + J`, whatever the nonzero scale `c`. -/
theorem inactiveSpace_internal (d : Fin 16 → K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (mask : Finset (Fin 16)) (r : ℕ) :
    Hades.inactiveSpace (internal d c hc hd hs).toLinearMap mask r =
      Hades.inactiveSpace (diagPlusOnes (1 : K) d) mask r :=
  Hades.inactiveSpace_diagPlusOnes hc _ mask r

/-- **At least `16 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds**, for every diagonal (rank–nullity, `Hades.card_sub_le_finrank_inactiveSpace`). It is a
lower bound only. -/
theorem finrank_inactiveSpace_internal (d : Fin 16 → K) (c : K) (hc : c ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (r : ℕ) :
    16 - r ≤ Module.finrank K
      (Hades.inactiveSpace (internal d c hc hd hs).toLinearMap ({0} : Finset (Fin 16)) r) := by
  have h := Hades.card_sub_le_finrank_inactiveSpace (internal d c hc hd hs).toLinearMap
    ({0} : Finset (Fin 16)) r
  rwa [Fintype.card_fin, Finset.card_singleton, mul_one] at h

/-- For `r < 16`, some nonzero difference stays inactive through `r` consecutive partial rounds,
for every diagonal. -/
theorem inactiveSpace_internal_ne_bot (d : Fin 16 → K) (c : K) (hc : c ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) {r : ℕ} (hr : r < 16) :
    Hades.inactiveSpace (internal d c hc hd hs).toLinearMap ({0} : Finset (Fin 16)) r ≠ ⊥ :=
  Hades.inactiveSpace_ne_bot _ _ r (by simpa using hr)

/-- **For fewer than sixteen partial rounds the middle term is zero**, for every diagonal. A
window `w` meeting the hypothesis of `Diag.activity_with_middle` has `w ≥ 16`, since shorter
windows leave a nonzero inactive difference (`Hades.inactiveSpace_ne_bot`); so `rP / w = 0` when
`rP < 16`. -/
theorem middle_term_eq_zero {d : Fin 16 → K} {rP w : ℕ} (hr : rP < 16)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) w = ⊥) :
    rP / w = 0 := by
  have hw : 16 ≤ w := by
    by_contra h
    refine Hades.inactiveSpace_ne_bot _ _ w ?_ htriv
    rw [Finset.card_singleton, mul_one, Fintype.card_fin]
    omega
  exact Nat.div_eq_of_lt (by omega)

/-! #### Field conditions -/

/-- The four field conditions under which both linear layers are invertible, for a diagonal `d`
and a scale `c`: `35 ≠ 0` for the external layer, and `d i ≠ 0` for every `i`, the
Sherman–Morrison condition `1 + ∑ 1/d_i ≠ 0` and `c ≠ 0` for the internal one. -/
structure Conditions (d : Fin 16 → K) (c : K) : Prop where
  thirtyFive : (35 : K) ≠ 0
  diag : ∀ i, d i ≠ 0
  shermanMorrison : 1 + ∑ i, (d i)⁻¹ ≠ 0
  scale : c ≠ 0

/-- **The conditions from a table of inverses.** If `d i * e i = 1` for every `i`, then every
`d i` is nonzero and `∑ 1/d_i = ∑ e_i` (`Poseidon2.sum_inv_eq_of_mul_eq_one`), so
`1 + ∑ e_i ≠ 0` is the Sherman–Morrison condition. Over `ZMod p` with literal tables and a literal
scale, every hypothesis is closed by `decide`, which does not have to compute an inverse. -/
theorem Conditions.of_mul_eq_one {d e : Fin 16 → K} {c : K} (h35 : (35 : K) ≠ 0)
    (he : ∀ i, d i * e i = 1) (hs : 1 + ∑ i, e i ≠ 0) (hc : c ≠ 0) : Conditions d c where
  thirtyFive := h35
  diag := ne_zero_of_mul_eq_one he
  shermanMorrison := by
    rw [sum_inv_eq_of_mul_eq_one he]
    exact hs
  scale := hc

/-! #### The schedule -/

variable {d : Fin 16 → K} {c : K}

/-- The linear layer of round `n`: external in the four full rounds on each side, internal with
the diagonal `d` in the `rP` partial rounds in between. -/
def linear (hD : Conditions d c) (rP n : ℕ) : (Fin 16 → K) ≃ₗ[K] (Fin 16 → K) :=
  if n < 4 ∨ 4 + rP ≤ n then external hD.thirtyFive
  else internal d c hD.scale hD.diag hD.shermanMorrison

/-- The rounds for the diagonal `d`: four full, `rP` partial with the S-box on coordinate `0`,
four full, with the same S-box everywhere and an arbitrary table of round constants. -/
def rounds (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) :
    ℕ → Hades.RoundSpec (Fin 16) K :=
  Hades.hadesSchedule 4 rP 4 {0} (fun _ _ => sbox) (linear hD rP) values

/-- **The permutation for the diagonal `d`.** The initial external layer (`p3-poseidon2`
`src/lib.rs:179`), then the `8 + rP` rounds of `Diag.rounds` (`src/lib.rs:182-201`). -/
def permutation (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    (x : Fin 16 → K) : Fin 16 → K :=
  Hades.execute (rounds hD rP sbox values) (external hD.thirtyFive x) (8 + rP)

/-- The permutation is a bijection, for every diagonal, S-box and table. -/
theorem permutation_bijective (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) : Function.Bijective (permutation hD rP sbox values) :=
  (Hades.execute_bijective (rounds hD rP sbox values) (8 + rP)).comp
    (external hD.thirtyFive).bijective

theorem linear_prefix (hD : Conditions d c) (rP : ℕ) {j : ℕ} (hj : j < 4) :
    linear hD rP j = external hD.thirtyFive := by
  simp [linear, hj]

theorem linear_middle (hD : Conditions d c) (rP : ℕ) {j : ℕ} (hj : j < rP) :
    linear hD rP (4 + j) = internal d c hD.scale hD.diag hD.shermanMorrison := by
  simp [linear, show ¬(4 + j < 4) by omega, show ¬(4 + rP ≤ 4 + j) by omega]

theorem linear_suffix (hD : Conditions d c) (rP j : ℕ) :
    linear hD rP (4 + rP + j) = external hD.thirtyFive := by
  simp [linear]

/-- A first-half full round is the code's round (`p3-poseidon2` `src/lib.rs:183-187`): add the
row, apply the S-box to every coordinate, then the external layer. -/
theorem rounds_apply_prefix (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {j : ℕ} (hj : j < 4) (x : Fin 16 → K) :
    (rounds hD rP sbox values j).apply x =
      external hD.thirtyFive (fun i => sbox (x i + values j i)) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, linear_prefix hD rP hj,
    Hades.hadesMask_prefix 4 rP 4 _ hj]
  congr 1
  funext i
  simp

/-- A second-half full round is the code's round (`p3-poseidon2` `src/lib.rs:197-201`). -/
theorem rounds_apply_suffix (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {j : ℕ} (hj : j < 4) (x : Fin 16 → K) :
    (rounds hD rP sbox values (4 + rP + j)).apply x =
      external hD.thirtyFive (fun i => sbox (x i + values (4 + rP + j) i)) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, linear_suffix hD rP j,
    Hades.hadesMask_suffix 4 rP 4 _ hj]
  congr 1
  funext i
  simp

/-- **A partial round is the code's round** (`p3-poseidon2` `src/lib.rs:190-194`), for every
diagonal: add the constant to `x 0`, apply the S-box to `x 0` alone, then the internal layer. -/
theorem rounds_apply_middle (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (hv : PartialRowsAtZero rP values) {j : ℕ} (hj : j < rP)
    (x : Fin 16 → K) :
    (rounds hD rP sbox values (4 + j)).apply x =
      internal d c hD.scale hD.diag hD.shermanMorrison
        (Function.update x 0 (sbox (x 0 + values (4 + j) 0))) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, linear_middle hD rP hj,
    Hades.hadesMask_middle 4 rP 4 _ hj]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hi, hv j hj i hi]

/-- With a table built by `roundValues`, partial round `j` adds `int j` to `x 0`, applies the
S-box there, then the internal layer (`p3-poseidon2` `src/lib.rs:190-194`). -/
theorem rounds_roundValues_apply_middle (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K)
    (ext : Fin 8 → Fin 16 → K) (int : Fin rP → K) {j : ℕ} (hj : j < rP) (x : Fin 16 → K) :
    (rounds hD rP sbox (roundValues rP ext int) (4 + j)).apply x =
      internal d c hD.scale hD.diag hD.shermanMorrison
        (Function.update x 0 (sbox (x 0 + int ⟨j, hj⟩))) := by
  rw [rounds_apply_middle hD rP sbox _ (roundValues_partialRowsAtZero rP ext int) hj,
    roundValues_middle rP ext int hj, Pi.single_eq_same]

/-! #### Activity and the independent-key bounds -/

section Activity

variable [DecidableEq K]

/-- The branch hypothesis of the first full block, in the form `Hades.hades_bound` takes. -/
theorem full_prefix (hD : Conditions d c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP j : ℕ)
    (hj : j + 1 < 4) : isBranchBound id (linear hD rP j) 8 := by
  rw [linear_prefix hD rP (by omega)]
  exact external_isBranchBound hprimes hD.thirtyFive

/-- The branch hypothesis of the second full block. -/
theorem full_suffix (hD : Conditions d c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP j : ℕ)
    (_hj : j + 1 < 4) : isBranchBound id (linear hD rP (4 + rP + j)) 8 := by
  rw [linear_suffix hD rP j]
  exact external_isBranchBound hprimes hD.thirtyFive

/-- **Thirty-two active S-boxes in the full rounds, for every diagonal.** For every S-box, scale
and constant table, two distinct inputs incur at least `32` charged S-box applications over the
`8 + rP` rounds: `8` for each of the two pairs of full rounds on each side. The partial rounds are
charged nothing here. A lower bound; it is not claimed to be attained. -/
theorem activity (hD : Conditions d c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ)
    (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {x y : Fin 16 → K} (hxy : x ≠ y) :
    32 ≤ Hades.scheduledWeight (rounds hD rP sbox values)
      (Hades.differenceTrace (rounds hD rP sbox values)
        (external hD.thirtyFive x) (external hD.thirtyFive y)) 0 (8 + rP) := by
  have h := Hades.hades_bound 4 rP 4 8 {0} (fun _ _ => sbox) (linear hD rP) values
    (fun h => hxy ((external hD.thirtyFive).injective h)) (full_prefix hD hprimes rP)
    (full_suffix hD hprimes rP)
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact le_trans (le_of_eq (by norm_num)) h

/-- **The partial rounds charged, for every diagonal.** If no nonzero difference stays inactive
through `w` consecutive partial rounds with the unscaled layer `diag d + J` (`htriv`), then each
of the `rP / w` disjoint windows of `w` partial rounds charges at least one S-box. The hypothesis
does not mention the scale `c` (`Diag.inactiveSpace_internal`); for a concrete field it is a
Krylov certificate (`Hades.inactiveSpace_diagPlusOnes_eq_bot`) or, with `w = 16`, the diagonal
criterion `Diag.inactiveSpace_sixteen_eq_bot_iff`. -/
theorem activity_with_middle (hD : Conditions d c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0)
    (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {w : ℕ}
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) w = ⊥)
    {x y : Fin 16 → K} (hxy : x ≠ y) :
    32 + rP / w ≤ Hades.scheduledWeight (rounds hD rP sbox values)
      (Hades.differenceTrace (rounds hD rP sbox values)
        (external hD.thirtyFive x) (external hD.thirtyFive y)) 0 (8 + rP) := by
  have htriv' : Hades.inactiveSpace
      (internal d c hD.scale hD.diag hD.shermanMorrison).toLinearMap ({0} : Finset (Fin 16)) w =
        ⊥ := by
    rw [inactiveSpace_internal]
    exact htriv
  have h := Hades.outer_middle_bound (rounds hD rP sbox values)
    (fun h => hxy ((external hD.thirtyFive).injective h)) 4 rP 4 8 w
    (fun j hj => Hades.hadesMask_prefix 4 rP 4 _ hj)
    (fun j hj => Hades.hadesMask_suffix 4 rP 4 _ hj)
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP)
    (internal d c hD.scale hD.diag hD.shermanMorrison) {0}
    (fun j hj => linear_middle hD rP hj)
    (fun j hj => Hades.hadesMask_middle 4 rP 4 _ hj) htriv'
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact le_trans (le_of_eq (by norm_num)) h

variable [Fintype K]

/-- **Trail bound from the full rounds, for every diagonal.** If `sbox` has differential
uniformity at most `u` and `u * 2^dd ≤ |K|`, the number of keys realising any fixed nonzero trail
`T`, in the model with an additional independent uniform key per round, times `2^(32 dd)`, is at
most the number of all key sequences. This concerns one trail in that model only: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u dd : ℕ} (hu : IsDiffUniform sbox u) (hd : u * 2 ^ dd ≤ Fintype.card K)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * 2 ^ (dd * 32)
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have h := Hades.hades_probability (Idx := Fin 16) (K := K) (u := u) (d := dd)
    4 rP 4 8 {0} (fun _ _ => sbox) (linear hD rP) values (fun _ _ _ => hu) hd
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP) h0 x
  rw [show dd * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) = dd * 32 by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

/-- **Trail bound with the partial rounds charged, for every diagonal.** As
`Diag.independent_key_probability`, with exponent `dd * (32 + rP / w)` under the inactive-space
hypothesis of `Diag.activity_with_middle`. The sample space is the same: one trail, an additional
independent uniform key per round. -/
theorem independent_key_probability_with_middle (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u dd w : ℕ} (hu : IsDiffUniform sbox u) (hd : u * 2 ^ dd ≤ Fintype.card K)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) w = ⊥)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * 2 ^ (dd * (32 + rP / w))
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have htriv' : Hades.inactiveSpace
      (internal d c hD.scale hD.diag hD.shermanMorrison).toLinearMap ({0} : Finset (Fin 16)) w =
        ⊥ := by
    rw [inactiveSpace_internal]
    exact htriv
  have h := Hades.hades_probability_with_middle (Idx := Fin 16) (K := K) (u := u) (d := dd)
    4 rP 4 8 w {0} (fun _ _ => sbox) (linear hD rP) values (fun _ _ _ => hu) hd
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP)
    (internal d c hD.scale hD.diag hD.shermanMorrison) (fun j hj => linear_middle hD rP hj)
    htriv' h0 x
  rw [show dd * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 + rP / w) = dd * (32 + rP / w) by
    norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

/-- **Trail bound from the full rounds, as an exact ratio, for every diagonal.** If `sbox` has
differential uniformity at most `u`, then for every nonzero trail `T`, the number of key sequences
realising `T` in the model with an additional independent uniform key per round, times `|K|^32`,
is at most `u^32` times the number of all key sequences. No relation between `u` and `|K|` is
assumed. This concerns one trail in that model only: not the permutation with its fixed
constants, and not a differential. -/
theorem independent_key_probability_exact (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u : ℕ} (hu : IsDiffUniform sbox u) {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * Fintype.card K ^ 32
      ≤ u ^ 32 * Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have h := Hades.hades_probability_exact (Idx := Fin 16) (K := K) (u := u)
    4 rP 4 8 {0} (fun _ _ => sbox) (linear hD rP) values (fun _ _ _ => hu)
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP) h0 x
  rw [show (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 = 32 by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

/-- **Trail bound with the partial rounds charged, as an exact ratio, for every diagonal.** As
`Diag.independent_key_probability_exact`, with `32 + rP / w` charged S-boxes under the
inactive-space hypothesis of `Diag.activity_with_middle`:
`keyCount * |K|^(32 + rP / w) ≤ u^(32 + rP / w) * |K^16|^(8 + rP)`. The sample space is the
same: one trail, an additional independent uniform key per round. -/
theorem independent_key_probability_with_middle_exact (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u w : ℕ} (hu : IsDiffUniform sbox u)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) w = ⊥)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * Fintype.card K ^ (32 + rP / w)
      ≤ u ^ (32 + rP / w) * Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have htriv' : Hades.inactiveSpace
      (internal d c hD.scale hD.diag hD.shermanMorrison).toLinearMap ({0} : Finset (Fin 16)) w =
        ⊥ := by
    rw [inactiveSpace_internal]
    exact htriv
  have h := Hades.hades_probability_with_middle_exact (Idx := Fin 16) (K := K) (u := u)
    4 rP 4 8 w {0} (fun _ _ => sbox) (linear hD rP) values (fun _ _ _ => hu)
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP)
    (internal d c hD.scale hD.diag hD.shermanMorrison) (fun j hj => linear_middle hD rP hj)
    htriv' h0 x
  rw [show (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 + rP / w = 32 + rP / w by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

/-- **Trail bound from the full rounds with a power of two, for every diagonal.** If `sbox` has
differential uniformity at most `u`, `0 < u`, and `2^e u^32 ≤ |K|^32`, then for every nonzero
trail `T` the number of key sequences realising `T`, times `2^e`, is at most the number of all
key sequences. It follows from `Diag.independent_key_probability_exact` by
`Hades.mul_le_of_ratio`; for a concrete field the hypothesis on `e` is closed by `decide`. The
sample space is the same: one trail, an additional independent uniform key per round. -/
theorem independent_key_probability_sharp (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u e : ℕ} (hu : IsDiffUniform sbox u) (hu0 : 0 < u)
    (he : 2 ^ e * u ^ 32 ≤ Fintype.card K ^ 32) {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0)
    (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * 2 ^ e
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Hades.mul_le_of_ratio (independent_key_probability_exact hD hprimes rP sbox values hu h0 x) he
    (pow_pos hu0 _)

/-- **Trail bound with the partial rounds charged and a power of two, for every diagonal.** As
`Diag.independent_key_probability_sharp`, with `32 + rP / w` charged S-boxes under the
inactive-space hypothesis of `Diag.activity_with_middle`: if `2^e u^(32 + rP / w) ≤
|K|^(32 + rP / w)` and `0 < u`, then `keyCount * 2^e ≤ |K^16|^(8 + rP)`. The sample space is the
same: one trail, an additional independent uniform key per round. -/
theorem independent_key_probability_with_middle_sharp (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u w e : ℕ} (hu : IsDiffUniform sbox u) (hu0 : 0 < u)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) w = ⊥)
    (he : 2 ^ e * u ^ (32 + rP / w) ≤ Fintype.card K ^ (32 + rP / w)) {T : ℕ → Fin 16 → K}
    (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * 2 ^ e
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Hades.mul_le_of_ratio
    (independent_key_probability_with_middle_exact hD hprimes rP sbox values hu htriv h0 x) he
    (pow_pos hu0 _)

/-- **Differential bound, as an exact ratio, for every diagonal.** If `sbox` has differential
uniformity at most `u`, then for every nonzero input difference `a`, every output difference `b`
and every input `x`, the number of key sequences under which `(x, x + a)` has output difference
`b` after the `8 + rP` rounds, in the model with an additional independent uniform key per round,
times `|K|^7`, is at most `u^7` times the number of all key sequences. No relation between `u` and
`|K|` is assumed. This concerns the key-averaged differential only: not the permutation with its
fixed constants, and not any one key. -/
theorem independent_key_differential_exact (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u : ℕ} (hu : IsDiffUniform sbox u) {a : Fin 16 → K} (ha : a ≠ 0) (b x : Fin 16 → K) :
    Hades.diffKeyCount (rounds hD rP sbox values) (8 + rP) a b x * Fintype.card K ^ 7
      ≤ u ^ 7 * Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have h := Hades.hades_differential_bound 4 rP 4 8 (by norm_num) {0} (fun _ _ => sbox)
    (linear hD rP) values (fun _ _ _ => hu) (full_prefix hD hprimes rP 0 (by norm_num)) ha b x
  rw [show 4 + rP + 4 = 8 + rP by omega] at h
  exact h

/-- **Differential bound with a power of two, for every diagonal.** If `sbox` has differential
uniformity at most `u`, `0 < u`, and `2^e u^7 ≤ |K|^7`, then for every nonzero input difference
`a`, the key count of the differential `(a, b)`, times `2^e`, is at most the number of all key
sequences. It follows from `Diag.independent_key_differential_exact` by `Hades.mul_le_of_ratio`.
This concerns the key-averaged differential only: not the permutation with its fixed constants,
and not any one key. -/
theorem independent_key_differential_sharp (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u e : ℕ} (hu : IsDiffUniform sbox u) (hu0 : 0 < u) (he : 2 ^ e * u ^ 7 ≤ Fintype.card K ^ 7)
    {a : Fin 16 → K} (ha : a ≠ 0) (b x : Fin 16 → K) :
    Hades.diffKeyCount (rounds hD rP sbox values) (8 + rP) a b x * 2 ^ e
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Hades.mul_le_of_ratio (independent_key_differential_exact hD hprimes rP sbox values hu ha b x) he
    (pow_pos hu0 _)

end Activity

/-! #### The diagonal criterion -/

omit [Field K] in
/-- Derives the injectivity hypothesis below from a `∀ i j : Fin 16` statement that `decide` can
check for a concrete field and a literal diagonal. -/
theorem injOn_of_forall (h : ∀ i j : Fin 16, i ≠ 0 → j ≠ 0 → d i = d j → i = j) :
    Set.InjOn d {i | i ≠ 0} :=
  fun i hi j hj hij => h i j hi hj hij

/-- **Criterion for sixteen partial rounds, for every diagonal.** No nonzero difference stays
inactive through sixteen consecutive partial rounds with `diag d + J` exactly when the diagonal
entries `d i`, `i ≠ 0`, are pairwise distinct in `K`. No hypothesis on `K` or `d` is needed. -/
theorem inactiveSpace_sixteen_eq_bot_iff :
    Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) 16 = ⊥ ↔
      Set.InjOn d {i | i ≠ 0} := by
  have h := Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff (one_ne_zero : (1 : K) ≠ 0)
    d (0 : Fin 16)
  rwa [Fintype.card_fin] at h

/-- **Sixteen partial rounds leave no inactive difference**, for the scaled internal layer with
any diagonal whose entries off coordinate `0` are pairwise distinct in `K`. -/
theorem inactiveSpace_internal_sixteen_eq_bot (d : Fin 16 → K) (c : K) (hc : c ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (hinj : Set.InjOn d {i | i ≠ 0}) :
    Hades.inactiveSpace (internal d c hc hd hs).toLinearMap ({0} : Finset (Fin 16)) 16 = ⊥ := by
  rw [inactiveSpace_internal]
  exact inactiveSpace_sixteen_eq_bot_iff.mpr hinj

/-- **Exactly `16 - r` dimensions stay inactive through `r` consecutive partial rounds**, for
`r ≤ 16` and any diagonal whose entries off coordinate `0` are pairwise distinct in `K`. This
makes `Diag.finrank_inactiveSpace_internal` exact under that hypothesis. -/
theorem finrank_inactiveSpace_internal_eq (d : Fin 16 → K) (c : K) (hc : c ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (hinj : Set.InjOn d {i | i ≠ 0}) {r : ℕ}
    (hr : r ≤ 16) :
    Module.finrank K
      (Hades.inactiveSpace (internal d c hc hd hs).toLinearMap ({0} : Finset (Fin 16)) r) =
        16 - r := by
  have h := Hades.finrank_inactiveSpace_diagPlusOnes hc d (0 : Fin 16) hinj (r := r)
    (by rw [Fintype.card_fin]; exact hr)
  rw [Fintype.card_fin] at h
  rw [internal_toLinearMap]
  exact h

/-- **A repeated diagonal entry defeats every window.** If `d i = d j` for two distinct indices
`i, j ≠ 0`, then `e_i - e_j` is an eigenvector of `diag d + J` whose coordinate `0` is zero. So
for every `w` some nonzero difference stays inactive through `w` consecutive partial rounds, and
the hypothesis of `Diag.activity_with_middle` holds for no window. This does not show that the
conclusion of `Diag.activity_with_middle` fails; it shows only that this route charges the
partial rounds nothing. -/
theorem inactiveSpace_ne_bot_of_not_injOn (h : ¬ Set.InjOn d {i | i ≠ 0}) (w : ℕ) :
    Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) w ≠ ⊥ := by
  simp only [Set.InjOn, not_forall] at h
  obtain ⟨i, hi, j, hj, hdij, hij⟩ := h
  replace hi : i ≠ 0 := hi
  replace hj : j ≠ 0 := hj
  let v : Fin 16 → K := Pi.single i 1 - Pi.single j 1
  have hsum : ∑ m, v m = 0 := by simp [v, Finset.sum_sub_distrib]
  have hLv : diagPlusOnes (1 : K) d v = d i • v := by
    funext k
    rw [diagPlusOnes_apply, hsum, add_zero, one_mul, Pi.smul_apply, smul_eq_mul]
    by_cases hkj : k = j
    · rw [hkj, hdij]
    · by_cases hki : k = i
      · rw [hki]
      · simp [v, hkj, hki]
  have hpow : ∀ m : ℕ, (diagPlusOnes (1 : K) d ^ m) v = d i ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hLv, smul_smul, pow_succ]
  intro hbot
  have hmem : v ∈ Hades.inactiveSpace (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) w := by
    intro m _ k hk
    rw [Finset.mem_singleton.mp hk, hpow, Pi.smul_apply, smul_eq_mul]
    simp [v, Ne.symm hi, Ne.symm hj]
  rw [hbot, Submodule.mem_bot] at hmem
  have hvi := congrFun hmem i
  simp [v, hij] at hvi

/-! #### The transpose -/

open scoped Matrix in
/-- **The internal layer is its own transpose, for every diagonal.** For all states `x, y`,
`Diag.internal d c hc hd hs x ⬝ᵥ y = x ⬝ᵥ Diag.internal d c hc hd hs y`
(`Poseidon2.diagPlusOnes_dotProduct`). -/
theorem internal_dotProduct (d : Fin 16 → K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (x y : Fin 16 → K) :
    internal d c hc hd hs x ⬝ᵥ y = x ⬝ᵥ internal d c hc hd hs y :=
  diagPlusOnes_dotProduct c d x y

end Diag

/-! ### The SP1 internal diagonal -/

variable (K) in
/-- The SP1 internal diagonal `d = (-2, 1, 2, 4, …, 2^13, 2^15)`: `d 0 = -2`,
`d i = 2^(i - 1)` for `1 ≤ i ≤ 14`, `d 15 = 2^15` (`sp1Diag_zero`, `sp1Diag_eq_pow`,
`sp1Diag_fifteen`). It is `POSEIDON2_INTERNAL_MATRIX_DIAG_16_KOALABEAR_MONTY`
(`p3-koala-bear` `0.4.3-succinct` `src/poseidon2.rs:37-55`, with shifts at lines 57-58), and the
BabyBear vector of `p3-baby-bear` `0.2.3-succinct` `src/poseidon2.rs:29-46` (shifts at lines
48-49) is the same. The entries are written as numerals so that `decide` evaluates them in
`ZMod p`. -/
def sp1Diag : Fin 16 → K :=
  ![-2, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 32768]

theorem sp1Diag_zero : sp1Diag K 0 = -2 := rfl

theorem sp1Diag_fifteen : sp1Diag K 15 = 2 ^ 15 := by
  simp [sp1Diag]
  norm_num

theorem sp1Diag_eq_pow (i : Fin 16) (h1 : 1 ≤ i.val) (h14 : i.val ≤ 14) :
    sp1Diag K i = 2 ^ (i.val - 1) := by
  fin_cases i <;> simp_all [sp1Diag] <;> norm_num

/-- Every diagonal entry is `± 2^k`, so all are nonzero once `2` is. -/
theorem sp1Diag_ne_zero (h2 : (2 : K) ≠ 0) (i : Fin 16) : sp1Diag K i ≠ 0 := by
  by_cases h0 : i = 0
  · rw [h0, sp1Diag_zero]
    exact neg_ne_zero.mpr h2
  by_cases h15 : i = 15
  · rw [h15, sp1Diag_fifteen]
    exact pow_ne_zero _ h2
  have h0' : i.val ≠ 0 := fun h => h0 (Fin.ext h)
  have h15' : i.val ≠ 15 := fun h => h15 (Fin.ext h)
  have hi := i.isLt
  rw [sp1Diag_eq_pow i (by omega) (by omega)]
  exact pow_ne_zero _ h2

/-- **The Sherman–Morrison quantity.** `1 + ∑ 1/d_i = 81917 / 2^15`; over `ℚ`,
`81917 = 11^2 * 677`. -/
theorem one_add_sum_inv_sp1Diag (h2 : (2 : K) ≠ 0) :
    (1 + ∑ i, (sp1Diag K i)⁻¹) * 32768 = 81917 := by
  have hd : sp1Diag K = ![-2, 1, 2, 2 ^ 2, 2 ^ 3, 2 ^ 4, 2 ^ 5, 2 ^ 6, 2 ^ 7, 2 ^ 8, 2 ^ 9,
      2 ^ 10, 2 ^ 11, 2 ^ 12, 2 ^ 13, 2 ^ 15] := by
    funext i
    fin_cases i <;> simp [sp1Diag] <;> norm_num
  rw [hd]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  field_simp
  ring

/-- With `2 ≠ 0`, the Sherman–Morrison hypothesis of `diagPlusOnesEquiv` is `81917 ≠ 0`. -/
theorem one_add_sum_inv_ne_zero_iff (h2 : (2 : K) ≠ 0) :
    1 + ∑ i, (sp1Diag K i)⁻¹ ≠ 0 ↔ (81917 : K) ≠ 0 := by
  rw [← one_add_sum_inv_sp1Diag h2]
  have h32 : (32768 : K) ≠ 0 := by
    rw [show (32768 : K) = 2 ^ 15 by norm_num]
    exact pow_ne_zero _ h2
  constructor
  · intro h
    exact mul_ne_zero h h32
  · intro h h0
    apply h
    rw [h0, zero_mul]

/-- **The internal layer** `x ↦ c (diag d + J) x` with the SP1 diagonal: coordinate `i` of the
image is `c (d_i x_i + ∑_j x_j)` (`internal_apply`). It is `Diag.internal (sp1Diag K) c`
(`internal_eq_diag`), with `d i ≠ 0` from `2 ≠ 0` and the Sherman–Morrison condition from
`81917 ≠ 0`. The code's value of `c` is `R^{-1}` for `R = 2^32` (`MONTY_BITS = 32`,
`p3-koala-bear` `0.4.3-succinct` `src/koala_bear.rs:21`, `p3-baby-bear` `0.2.3-succinct`
`src/baby_bear.rs:17`); here `c` is any nonzero scalar. -/
def internal (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) (hs : (81917 : K) ≠ 0) :
    (Fin 16 → K) ≃ₗ[K] (Fin 16 → K) :=
  diagPlusOnesEquiv c (sp1Diag K) hc (sp1Diag_ne_zero h2)
    ((one_add_sum_inv_ne_zero_iff h2).mpr hs)

/-- **The SP1 internal layer is the generic layer at `d = sp1Diag K`**, by definition. -/
theorem internal_eq_diag (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) (hs : (81917 : K) ≠ 0) :
    internal c hc h2 hs =
      Diag.internal (sp1Diag K) c hc (sp1Diag_ne_zero h2)
        ((one_add_sum_inv_ne_zero_iff h2).mpr hs) :=
  rfl

theorem internal_apply (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) (hs : (81917 : K) ≠ 0)
    (x : Fin 16 → K) (i : Fin 16) :
    internal c hc h2 hs x i = c * (sp1Diag K i * x i + ∑ j, x j) :=
  rfl

theorem internal_toLinearMap (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) (hs : (81917 : K) ≠ 0) :
    (internal c hc h2 hs).toLinearMap = diagPlusOnes c (sp1Diag K) :=
  rfl

/-- **The condition `81917 ≠ 0` is exact.** With `c ≠ 0` and `2 ≠ 0`, the internal map is
injective if and only if `81917 ≠ 0` in `K`. -/
theorem internal_injective_iff {c : K} (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) :
    Function.Injective (diagPlusOnes c (sp1Diag K)) ↔ (81917 : K) ≠ 0 :=
  (diagPlusOnes_injective_iff hc (sp1Diag_ne_zero h2)).trans (one_add_sum_inv_ne_zero_iff h2)

/-- The intended scale `c = R^{-1}`, `R = 2^32`, is nonzero. -/
theorem ne_zero_of_mul_two_pow_eq_one {c : K} (h : c * 2 ^ 32 = 1) : c ≠ 0 :=
  left_ne_zero_of_mul_eq_one h

/-- **The scale is invisible to inactive differences.** The inactive space of the internal
layer is that of `diag d + J`, whatever the nonzero scale `c` (`Diag.inactiveSpace_internal`). -/
theorem inactiveSpace_internal (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) (mask : Finset (Fin 16)) (r : ℕ) :
    Hades.inactiveSpace (internal c hc h2 hs).toLinearMap mask r =
      Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) mask r :=
  Diag.inactiveSpace_internal _ c hc _ _ mask r

/-- **At least `16 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds** (`Diag.finrank_inactiveSpace_internal`). For `r = 13` this is at least `3`. It is a
lower bound only. -/
theorem finrank_inactiveSpace_internal (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) (r : ℕ) :
    16 - r ≤ Module.finrank K
      (Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) r) :=
  Diag.finrank_inactiveSpace_internal _ c hc _ _ r

/-- For `r < 16`, some nonzero difference stays inactive through `r` consecutive partial
rounds. -/
theorem inactiveSpace_internal_ne_bot (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) {r : ℕ} (hr : r < 16) :
    Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) r ≠ ⊥ :=
  Diag.inactiveSpace_internal_ne_bot _ c hc _ _ hr

/-- At least three dimensions of differences stay inactive through thirteen consecutive partial
rounds, the number of partial rounds in SP1's BabyBear instance. -/
theorem three_le_finrank_inactiveSpace_thirteen (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) :
    3 ≤ Module.finrank K
      (Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) 13) :=
  finrank_inactiveSpace_internal c hc h2 hs 13

/-- **For fewer than sixteen partial rounds the middle term is zero** (`Diag.middle_term_eq_zero`
at `d = sp1Diag K`). For BabyBear's thirteen partial rounds, `activity_with_middle` therefore
gives nothing beyond `activity`. -/
theorem middle_term_eq_zero {rP w : ℕ} (hr : rP < 16)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) w = ⊥) :
    rP / w = 0 :=
  Diag.middle_term_eq_zero hr htriv

/-! ### Field conditions -/

/-- The four field conditions under which both linear layers are invertible, for a scale
`c`: `35 ≠ 0` for the external layer, and `2 ≠ 0`, `81917 ≠ 0`, `c ≠ 0` for the internal one.
For a prime field `ZMod p` with a literal `c`, each field is closed by `decide`. -/
structure Conditions (c : K) : Prop where
  thirtyFive : (35 : K) ≠ 0
  two : (2 : K) ≠ 0
  shermanMorrison : (81917 : K) ≠ 0
  scale : c ≠ 0

/-- The conditions follow from the `m4Primes` hypothesis of the branch bound, `677 ≠ 0` and
`c ≠ 0`, since `35 = 5 * 7` and `81917 = 11 * 11 * 677`. -/
theorem Conditions.of_primes {c : K} (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) (h677 : (677 : K) ≠ 0)
    (hc : c ≠ 0) : Conditions c where
  thirtyFive := thirtyFive_ne_zero_of_primes h
  two := by exact_mod_cast h 2 (by decide)
  shermanMorrison := by
    have h11 : (11 : K) ≠ 0 := by exact_mod_cast h 11 (by decide)
    rw [show (81917 : K) = 11 * 11 * 677 by norm_num]
    exact mul_ne_zero (mul_ne_zero h11 h11) h677
  scale := hc

/-- **The SP1 conditions are the generic conditions at `d = sp1Diag K`**: `d i ≠ 0` from `2 ≠ 0`
(`sp1Diag_ne_zero`) and `1 + ∑ 1/d_i ≠ 0` from `81917 ≠ 0` (`one_add_sum_inv_ne_zero_iff`). -/
theorem Conditions.toDiag {c : K} (hK : Conditions c) : Diag.Conditions (sp1Diag K) c where
  thirtyFive := hK.thirtyFive
  diag := sp1Diag_ne_zero hK.two
  shermanMorrison := (one_add_sum_inv_ne_zero_iff hK.two).mpr hK.shermanMorrison
  scale := hK.scale

/-! ### The schedule -/

variable {c : K}

/-- The linear layer of round `n`: external in the four full rounds on each side, internal in
the `rP` partial rounds in between. It is `Diag.linear hK.toDiag rP` (`linear_eq_diag`). -/
def linear (hK : Conditions c) (rP n : ℕ) : (Fin 16 → K) ≃ₗ[K] (Fin 16 → K) :=
  if n < 4 ∨ 4 + rP ≤ n then external hK.thirtyFive
  else internal c hK.scale hK.two hK.shermanMorrison

/-- The rounds: four full, `rP` partial with the S-box on coordinate `0`, four full, with the
same S-box everywhere and an arbitrary table of round constants. Four is the code's
`rounds_f_half = rounds_f / 2` (`p3-poseidon2` `src/lib.rs:182`) for SP1's `ROUNDS_F = 8`
(`slop-koala-bear` `6.10.0` `src/koala_bear_poseidon2.rs:49`; `sp1-primitives` `5.2.4`
`src/lib.rs:1108`). SP1's `rP` is `ROUNDS_P`: `20` for KoalaBear (`slop-koala-bear` `6.10.0`
`src/koala_bear_poseidon2.rs:50`) and `13` for BabyBear (`sp1-primitives` `5.2.4`
`src/lib.rs:1109`). It is `Diag.rounds hK.toDiag` (`rounds_eq_diag`). -/
def rounds (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) :
    ℕ → Hades.RoundSpec (Fin 16) K :=
  Hades.hadesSchedule 4 rP 4 {0} (fun _ _ => sbox) (linear hK rP) values

/-- **The permutation.** The initial external layer (`p3-poseidon2` `src/lib.rs:179`), then the
`8 + rP` rounds of `rounds` (`src/lib.rs:182-201`). It is `Diag.permutation hK.toDiag`
(`permutation_eq_diag`). -/
def permutation (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    (x : Fin 16 → K) : Fin 16 → K :=
  Hades.execute (rounds hK rP sbox values) (external hK.thirtyFive x) (8 + rP)

/-- The SP1 linear layers are the generic ones at `d = sp1Diag K`, by definition. -/
theorem linear_eq_diag (hK : Conditions c) (rP : ℕ) : linear hK rP = Diag.linear hK.toDiag rP :=
  rfl

/-- The SP1 rounds are the generic rounds at `d = sp1Diag K`, by definition. -/
theorem rounds_eq_diag (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) :
    rounds hK rP sbox values = Diag.rounds hK.toDiag rP sbox values :=
  rfl

/-- The SP1 permutation is the generic permutation at `d = sp1Diag K`, by definition. -/
theorem permutation_eq_diag (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) :
    permutation hK rP sbox values = Diag.permutation hK.toDiag rP sbox values :=
  rfl

theorem permutation_bijective (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) : Function.Bijective (permutation hK rP sbox values) :=
  Diag.permutation_bijective hK.toDiag rP sbox values

theorem linear_prefix (hK : Conditions c) (rP : ℕ) {j : ℕ} (hj : j < 4) :
    linear hK rP j = external hK.thirtyFive :=
  Diag.linear_prefix hK.toDiag rP hj

theorem linear_middle (hK : Conditions c) (rP : ℕ) {j : ℕ} (hj : j < rP) :
    linear hK rP (4 + j) = internal c hK.scale hK.two hK.shermanMorrison :=
  Diag.linear_middle hK.toDiag rP hj

theorem linear_suffix (hK : Conditions c) (rP j : ℕ) :
    linear hK rP (4 + rP + j) = external hK.thirtyFive :=
  Diag.linear_suffix hK.toDiag rP j

/-! ### The rounds against the code -/

/-- A first-half full round is the code's round (`p3-poseidon2` `src/lib.rs:183-187`): add the
row, apply the S-box to every coordinate, then the external layer. -/
theorem rounds_apply_prefix (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {j : ℕ} (hj : j < 4) (x : Fin 16 → K) :
    (rounds hK rP sbox values j).apply x =
      external hK.thirtyFive (fun i => sbox (x i + values j i)) :=
  Diag.rounds_apply_prefix hK.toDiag rP sbox values hj x

/-- A second-half full round is the code's round (`p3-poseidon2` `src/lib.rs:197-201`). -/
theorem rounds_apply_suffix (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {j : ℕ} (hj : j < 4) (x : Fin 16 → K) :
    (rounds hK rP sbox values (4 + rP + j)).apply x =
      external hK.thirtyFive (fun i => sbox (x i + values (4 + rP + j) i)) :=
  Diag.rounds_apply_suffix hK.toDiag rP sbox values hj x

/-- **A partial round is the code's round** (`p3-poseidon2` `src/lib.rs:190-194`): add the
constant to `x 0`, apply the S-box to `x 0` alone, then the internal layer. -/
theorem rounds_apply_middle (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (hv : PartialRowsAtZero rP values) {j : ℕ} (hj : j < rP)
    (x : Fin 16 → K) :
    (rounds hK rP sbox values (4 + j)).apply x =
      internal c hK.scale hK.two hK.shermanMorrison
        (Function.update x 0 (sbox (x 0 + values (4 + j) 0))) :=
  Diag.rounds_apply_middle hK.toDiag rP sbox values hv hj x

/-- With a table built by `roundValues`, partial round `j` adds `int j` to `x 0`, applies
the S-box there, then the internal layer (`p3-poseidon2` `src/lib.rs:190-194`). -/
theorem rounds_roundValues_apply_middle (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (ext : Fin 8 → Fin 16 → K) (int : Fin rP → K) {j : ℕ} (hj : j < rP) (x : Fin 16 → K) :
    (rounds hK rP sbox (roundValues rP ext int) (4 + j)).apply x =
      internal c hK.scale hK.two hK.shermanMorrison
        (Function.update x 0 (sbox (x 0 + int ⟨j, hj⟩))) :=
  Diag.rounds_roundValues_apply_middle hK.toDiag rP sbox ext int hj x

/-! ### Activity -/

section Activity

variable [DecidableEq K]

/-- The branch hypothesis of the first full block, in the form `Hades.hades_bound` takes. -/
theorem full_prefix (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP j : ℕ)
    (hj : j + 1 < 4) : isBranchBound id (linear hK rP j) 8 :=
  Diag.full_prefix hK.toDiag hprimes rP j hj

/-- The branch hypothesis of the second full block. -/
theorem full_suffix (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP j : ℕ)
    (_hj : j + 1 < 4) : isBranchBound id (linear hK rP (4 + rP + j)) 8 :=
  Diag.full_suffix hK.toDiag hprimes rP j _hj

/-- **Thirty-two active S-boxes in the full rounds.** For every S-box, scale and constant table,
two distinct inputs incur at least `32` charged S-box applications over the `8 + rP` rounds:
`8` for each of the two pairs of full rounds on each side (`Diag.activity` at `d = sp1Diag K`).
The partial rounds are charged nothing here. A lower bound; it is not claimed to be attained. -/
theorem activity (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ)
    (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {x y : Fin 16 → K} (hxy : x ≠ y) :
    32 ≤ Hades.scheduledWeight (rounds hK rP sbox values)
      (Hades.differenceTrace (rounds hK rP sbox values)
        (external hK.thirtyFive x) (external hK.thirtyFive y)) 0 (8 + rP) :=
  Diag.activity hK.toDiag hprimes rP sbox values hxy

/-- **The partial rounds charged.** If no nonzero difference stays inactive through `w`
consecutive partial rounds with the unscaled layer `diag d + J` (`htriv`), then each of the
`rP / w` disjoint windows of `w` partial rounds charges at least one S-box
(`Diag.activity_with_middle` at `d = sp1Diag K`). The hypothesis does not mention the scale `c`
(`inactiveSpace_internal`); for a concrete field it is a Krylov certificate
(`Hades.inactiveSpace_diagPlusOnes_eq_bot`). With `w = 16`: `33` for `rP = 20`, and `32` for
`rP = 13`, where the middle term vanishes. -/
theorem activity_with_middle (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0)
    (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {w : ℕ}
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) w = ⊥)
    {x y : Fin 16 → K} (hxy : x ≠ y) :
    32 + rP / w ≤ Hades.scheduledWeight (rounds hK rP sbox values)
      (Hades.differenceTrace (rounds hK rP sbox values)
        (external hK.thirtyFive x) (external hK.thirtyFive y)) 0 (8 + rP) :=
  Diag.activity_with_middle hK.toDiag hprimes rP sbox values htriv hxy

/-! ### The independent-key trail bound -/

variable [Fintype K]

/-- **Trail bound from the full rounds.** If `sbox` has differential uniformity at most `u` and
`u * 2^dd ≤ |K|`, the number of keys realising any fixed nonzero trail `T`, in the model with an
additional independent uniform key per round, times `2^(32 dd)`, is at most the number of all
key sequences (`Diag.independent_key_probability` at `d = sp1Diag K`). This concerns one trail in
that model only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0)
    (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {u dd : ℕ} (hu : IsDiffUniform sbox u)
    (hd : u * 2 ^ dd ≤ Fintype.card K) {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hK rP sbox values) (8 + rP) T x * 2 ^ (dd * 32)
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Diag.independent_key_probability hK.toDiag hprimes rP sbox values hu hd h0 x

/-- **Trail bound with the partial rounds charged.** As `independent_key_probability`, with
exponent `dd * (32 + rP / w)` under the inactive-space hypothesis of `activity_with_middle`. The
sample space is the same: one trail, an additional independent uniform key per round. -/
theorem independent_key_probability_with_middle (hK : Conditions c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u dd w : ℕ} (hu : IsDiffUniform sbox u) (hd : u * 2 ^ dd ≤ Fintype.card K)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) w = ⊥)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hK rP sbox values) (8 + rP) T x * 2 ^ (dd * (32 + rP / w))
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Diag.independent_key_probability_with_middle hK.toDiag hprimes rP sbox values hu hd htriv h0 x

end Activity

end Poseidon2.Plonky3

/-! ### The independent-key trail bound as an exact ratio

`independent_key_probability` and `independent_key_probability_with_middle` charge a whole
number `dd` of bits per charged S-box, where `u * 2^dd ≤ |K|`. The two results below keep the
ratio `|K| / u` per charged S-box exact; they are `Diag.independent_key_probability_exact` and
`Diag.independent_key_probability_with_middle_exact` at `d = sp1Diag K`. The sample space is the
same: one trail, an additional independent uniform key per round. -/

namespace Poseidon2.Plonky3

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K] {c : K}

/-- **Trail bound from the full rounds, as an exact ratio.** If `sbox` has differential
uniformity at most `u`, then for every nonzero trail `T`, the number of key sequences realising
`T` in the model with an additional independent uniform key per round, times `|K|^32`, is at
most `u^32` times the number of all key sequences. No relation between `u` and `|K|` is
assumed. This concerns one trail in that model only: not the permutation with its fixed
constants, and not a differential. -/
theorem independent_key_probability_exact (hK : Conditions c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u : ℕ} (hu : IsDiffUniform sbox u) {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hK rP sbox values) (8 + rP) T x * Fintype.card K ^ 32
      ≤ u ^ 32 * Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Diag.independent_key_probability_exact hK.toDiag hprimes rP sbox values hu h0 x

/-- **Trail bound with the partial rounds charged, as an exact ratio.** As
`independent_key_probability_exact`, with `32 + rP / w` charged S-boxes under the inactive-space
hypothesis of `activity_with_middle`:
`keyCount * |K|^(32 + rP / w) ≤ u^(32 + rP / w) * |K^16|^(8 + rP)`. The sample space is the
same: one trail, an additional independent uniform key per round. -/
theorem independent_key_probability_with_middle_exact (hK : Conditions c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u w : ℕ} (hu : IsDiffUniform sbox u)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) w = ⊥)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hK rP sbox values) (8 + rP) T x * Fintype.card K ^ (32 + rP / w)
      ≤ u ^ (32 + rP / w) * Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Diag.independent_key_probability_with_middle_exact hK.toDiag hprimes rP sbox values hu htriv h0 x

end Poseidon2.Plonky3

/-! ### Exact inactive dimensions through the diagonal criterion

`finrank_inactiveSpace_internal` is a lower bound: at least `16 - r` dimensions of differences
stay inactive through `r` consecutive partial rounds. The results below make it exact when the
fifteen diagonal entries off coordinate `0`, namely `1, 2, 4, …, 2^13, 2^15`, are pairwise
distinct in `K`, by the general criterion `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff`;
they are `Diag.inactiveSpace_sixteen_eq_bot_iff`, `Diag.inactiveSpace_internal_sixteen_eq_bot` and
`Diag.finrank_inactiveSpace_internal_eq` at `d = sp1Diag K`. Under that condition the hypothesis
of `activity_with_middle` holds with `w = 16`, with no Krylov table. This is a second route to
that hypothesis; the first, a Krylov certificate (`Hades.inactiveSpace_diagPlusOnes_eq_bot`),
checks literal tables for one concrete field.

These are statements about inactive differences of the partial rounds only: they are the
linear-algebra fact behind "at most `15` consecutive partial rounds can be linearized", not a
proof of resistance to subspace trails in general, and they say nothing about the full
rounds. -/

namespace Poseidon2.Plonky3

variable {K : Type*} [Field K]

/-- Derives the injectivity hypothesis below from a `∀ i j : Fin 16` statement that `decide` can
check for a concrete field. -/
theorem injOn_sp1Diag_of_forall
    (h : ∀ i j : Fin 16, i ≠ 0 → j ≠ 0 → sp1Diag K i = sp1Diag K j → i = j) :
    Set.InjOn (sp1Diag K) {i | i ≠ 0} :=
  Diag.injOn_of_forall h

/-- **Criterion for sixteen partial rounds.** No nonzero difference stays inactive through
sixteen consecutive partial rounds with `diag d + J` exactly when the diagonal entries `d i`,
`i ≠ 0`, are pairwise distinct in `K`. No hypothesis on `K` is needed. -/
theorem inactiveSpace_sixteen_eq_bot_iff :
    Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) 16 = ⊥ ↔
      Set.InjOn (sp1Diag K) {i | i ≠ 0} :=
  Diag.inactiveSpace_sixteen_eq_bot_iff

/-- **Sixteen partial rounds leave no inactive difference**, for the scaled internal layer,
when the diagonal entries off coordinate `0` are pairwise distinct in `K`. -/
theorem inactiveSpace_internal_sixteen_eq_bot (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) (hinj : Set.InjOn (sp1Diag K) {i | i ≠ 0}) :
    Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Diag.inactiveSpace_internal_sixteen_eq_bot _ c hc _ _ hinj

/-- **Exactly `16 - r` dimensions stay inactive through `r` consecutive partial rounds**, for
`r ≤ 16`, when the diagonal entries off coordinate `0` are pairwise distinct in `K`. This makes
`finrank_inactiveSpace_internal` exact under that hypothesis. -/
theorem finrank_inactiveSpace_internal_eq (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) (hinj : Set.InjOn (sp1Diag K) {i | i ≠ 0}) {r : ℕ} (hr : r ≤ 16) :
    Module.finrank K
      (Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) r) =
        16 - r :=
  Diag.finrank_inactiveSpace_internal_eq _ c hc _ _ hinj hr

end Poseidon2.Plonky3

/-! ### The independent-key differential bound

The trail bounds above concern one trail. The result below bounds a differential: the sum over
all trails from a nonzero input difference `a` to an output difference `b`, in the same model with
an additional independent uniform key per round (`Hades.hades_differential_bound`). It charges the
first two full rounds only: the external layer of round `0` has branch number at least `8`
(`external_isBranchBound`), so the ratio is `(u / |K|)^7`. The partial rounds and the other full
rounds are not charged. It is `Diag.independent_key_differential_exact` at `d = sp1Diag K`. -/

namespace Poseidon2.Plonky3

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K] {c : K}

/-- **Differential bound, as an exact ratio.** If `sbox` has differential uniformity at most `u`,
then for every nonzero input difference `a`, every output difference `b` and every input `x`, the
number of key sequences under which `(x, x + a)` has output difference `b` after the `8 + rP`
rounds, in the model with an additional independent uniform key per round, times `|K|^7`, is at
most `u^7` times the number of all key sequences. No relation between `u` and `|K|` is assumed.
This concerns the key-averaged differential only: not the permutation with its fixed constants,
and not any one key. -/
theorem independent_key_differential_exact (hK : Conditions c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u : ℕ} (hu : IsDiffUniform sbox u) {a : Fin 16 → K} (ha : a ≠ 0) (b x : Fin 16 → K) :
    Hades.diffKeyCount (rounds hK rP sbox values) (8 + rP) a b x * Fintype.card K ^ 7
      ≤ u ^ 7 * Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Diag.independent_key_differential_exact hK.toDiag hprimes rP sbox values hu ha b x

end Poseidon2.Plonky3

/-! ### States whose four blocks sum to zero

A flat state `x` lies in `blockSumZeroFlat` when its four blocks `x_0, …, x_3` (`blockOf`) sum
to zero, that is, when the position sums of the input, `positionSums x`
(`x[k] + x[4 + k] + x[8 + k] + x[12 + k]`), all vanish (`mem_blockSumZeroFlat`). The code computes
its `sums` from the state after the `M4` step, which is `M4` applied to these
(`positionSums_mat4Blocks`), so under `35 ≠ 0` the two vanish together
(`positionSums_mat4Blocks_eq_zero_iff`). This is `BlockCirculant.blockSumZero` on the flat state,
and the results below specialise `BlockCirculant.blockMix_of_blockSum_eq_zero` and its companions
to the external layer:

* `blockOf_external_of_mem`, `external_eq_mat4Blocks_of_mem`: on such a state the external layer
  is `M4` applied to each block separately, with no mixing between blocks;
* `external_eq_mat4Blocks_iff`: under `35 ≠ 0`, the states on which the external layer equals
  `mat4Blocks` are exactly the states of `blockSumZeroFlat`;
* `external_mem_blockSumZeroFlat_iff`: a state lies in the subspace exactly when its image under
  the external layer does, so the layer maps the subspace onto itself and every state outside it
  to a state outside it;
* `finrank_blockSumZeroFlat`: the subspace has dimension `12`.

At the level of the code, over every commutative ring: the position sums after the first step of
`mds_light_permutation` are `M4` applied to the position sums of the input
(`positionSums_mat4Blocks`), so when the latter vanish the second step adds zero and the layer is
`M4` on each block (`mdsLight_eq_mat4Blocks`); in general the output position sums are `5` times
`M4` applied to the input position sums (`positionSums_mdsLight`).

Why this subspace is singled out: recent round-skipping work on Poseidon2 (IACR ePrint 2026/306)
exploits the structure of the linear-layer matrices; the zero-block-sum subspace is one
structural property of the external matrix, and no claim is made here about which properties
that work uses. Its authors state that their attacks do not mean that the primitive falls short of
its claimed security level. No source cited here shows that SP1's parameter sets are affected,
and nothing here is a statement about any attack. These are facts about the external layer
alone: the S-box layer of a full round acts on every coordinate and need not keep a state in the
subspace, and nothing is said about the internal layer, about whole rounds or about the
permutation. -/

namespace Poseidon2.Plonky3

open BlockCirculant

section Code

variable {R : Type*} [CommRing R]

/-- The position sums of a state are the sum of its four blocks. -/
theorem positionSums_eq_sum_blockOf (x : Fin 16 → R) :
    positionSums x = ∑ b : Fin 4, blockOf x b := by
  funext k
  rw [positionSums_apply, Finset.sum_apply]
  rfl

/-- **The position sums after the first step.** `sums[k]` computed from `M4` applied to each
block (`mat4Blocks`) is coordinate `k` of `M4` applied to the position sums of the input. -/
theorem positionSums_mat4Blocks (x : Fin 16 → R) :
    positionSums (mat4Blocks x) = (m4 R).mulVec (positionSums x) := by
  funext k
  rw [positionSums_apply, positionSums_eq_sum_blockOf, Matrix.mulVec_sum, Finset.sum_apply]
  simp only [mat4Blocks_apply, Equiv.symm_apply_apply]

/-- **The code adds nothing on states with zero position sums.** If every position sum of `x`
vanishes, `mds_light_permutation` returns `M4` applied to each block: `mdsLight x = mat4Blocks x`.
This holds over every commutative ring. -/
theorem mdsLight_eq_mat4Blocks {x : Fin 16 → R} (hx : positionSums x = 0) :
    mdsLight x = mat4Blocks x := by
  funext i
  rw [mdsLight, positionSums_mat4Blocks, hx, Matrix.mulVec_zero, Pi.zero_apply, add_zero]

/-- **The position sums of the output.** `sums` of `mdsLight x` is `5` times `M4` applied to the
position sums of `x`: each of the four blocks contributes `M4 s` once more. -/
theorem positionSums_mdsLight (x : Fin 16 → R) :
    positionSums (mdsLight x) = (5 : R) • (m4 R).mulVec (positionSums x) := by
  funext k
  have h := congrFun (positionSums_mat4Blocks x) k
  rw [positionSums_apply] at h
  simp only [mat4Blocks_apply, Equiv.symm_apply_apply] at h
  rw [positionSums_apply]
  simp only [mdsLight_apply]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, h,
    Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

end Code

variable {K : Type*} [Field K]

/-- The position sums of a flat state are the block sum of the state indexed by `blockIndex`. -/
theorem positionSums_eq_blockSum (x : Fin 16 → K) :
    positionSums x = blockSum (x ∘ blockIndex) := by
  funext k
  rw [positionSums_apply]
  rfl

/-- The flat states whose four blocks sum to zero: `BlockCirculant.blockSumZero`, pulled back to
`Fin 16 → K` along `blockIndex`. -/
def blockSumZeroFlat : Submodule K (Fin 16 → K) :=
  blockSumZero.comap (LinearEquiv.funCongrLeft K K blockIndex).toLinearMap

/-- **Membership is the vanishing of the position sums `positionSums x` of the input.** -/
theorem mem_blockSumZeroFlat {x : Fin 16 → K} : x ∈ blockSumZeroFlat ↔ positionSums x = 0 := by
  rw [positionSums_eq_blockSum, ← mem_blockSumZero]
  rfl

/-- **The code's `sums` vanish exactly when the position sums of the input do**, under `35 ≠ 0`.
The code computes `sums` from the state after the `M4` step, `positionSums (mat4Blocks x)`, which
is `M4` applied to `positionSums x` (`positionSums_mat4Blocks`), and `M4` is injective. -/
theorem positionSums_mat4Blocks_eq_zero_iff (h35 : (35 : K) ≠ 0) (x : Fin 16 → K) :
    positionSums (mat4Blocks x) = 0 ↔ positionSums x = 0 := by
  rw [positionSums_mat4Blocks, ← m4Equiv_apply h35]
  exact map_eq_zero_iff _ (m4Equiv K h35).injective

/-- **The subspace has dimension `12`**: `(4 - 1) * 4` (`BlockCirculant.finrank_blockSumZero`),
unchanged by relabelling coordinates. -/
theorem finrank_blockSumZeroFlat : Module.finrank K (blockSumZeroFlat (K := K)) = 12 := by
  rw [blockSumZeroFlat, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    finrank_blockSumZero, Fintype.card_fin]

/-- **On `blockSumZeroFlat` the external layer is `M4` on each block.** It equals the first step
of the code alone, `mat4Blocks`. -/
theorem external_eq_mat4Blocks_of_mem (h35 : (35 : K) ≠ 0) {x : Fin 16 → K}
    (hx : x ∈ blockSumZeroFlat) : external h35 x = mat4Blocks x := by
  rw [external_eq_mdsLight, mdsLight_eq_mat4Blocks (mem_blockSumZeroFlat.mp hx)]

/-- **No mixing between blocks on `blockSumZeroFlat`.** Block `b` of the output is `M4` applied to
block `b` of the input. -/
theorem blockOf_external_of_mem (h35 : (35 : K) ≠ 0) {x : Fin 16 → K}
    (hx : x ∈ blockSumZeroFlat) (b : Fin 4) :
    blockOf (external h35 x) b = (m4 K).mulVec (blockOf x b) := by
  funext c
  rw [blockOf, external_eq_mat4Blocks_of_mem h35 hx, mat4Blocks_apply, Equiv.symm_apply_apply]

/-- **The blockwise form holds exactly on `blockSumZeroFlat`.** Under `35 ≠ 0`,
`external h35 x = mat4Blocks x` if and only if `x ∈ blockSumZeroFlat`. The external layer is the
code's `mdsLight`, which adds the code's `sums[i % 4]`, `positionSums (mat4Blocks x)`, to
coordinate `i` of `mat4Blocks x`; those vanish exactly when `x` lies in the subspace
(`positionSums_mat4Blocks_eq_zero_iff`). -/
theorem external_eq_mat4Blocks_iff (h35 : (35 : K) ≠ 0) (x : Fin 16 → K) :
    external h35 x = mat4Blocks x ↔ x ∈ blockSumZeroFlat := by
  refine ⟨fun h => ?_, external_eq_mat4Blocks_of_mem h35⟩
  rw [mem_blockSumZeroFlat, ← positionSums_mat4Blocks_eq_zero_iff h35]
  funext k
  have hk := congrFun h ⟨k.val, by omega⟩
  have hmod : (⟨k.val % 4, by omega⟩ : Fin 4) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  rw [external_eq_mdsLight, mdsLight, hmod, add_eq_left] at hk
  exact hk

/-- `external h35 x` written through `BlockCirculant.blockMix` on the state indexed by
`blockIndex`. -/
theorem external_comp_blockIndex (h35 : (35 : K) ≠ 0) (x : Fin 16 → K) :
    external h35 x ∘ blockIndex = blockMix (m4Equiv K h35).toLinearMap (x ∘ blockIndex) := by
  rw [external_apply]
  funext ic
  simp

/-- **The external layer preserves `blockSumZeroFlat` in both directions.** `external h35 x`
lies in the subspace exactly when `x` does, by `BlockCirculant.blockMix_mem_blockSumZero_iff`:
`M4` is injective and `5 ≠ 0` under `35 ≠ 0`. Since the layer is bijective, it maps the subspace
onto itself. -/
theorem external_mem_blockSumZeroFlat_iff (h35 : (35 : K) ≠ 0) (x : Fin 16 → K) :
    external h35 x ∈ blockSumZeroFlat ↔ x ∈ blockSumZeroFlat := by
  rw [mem_blockSumZeroFlat, mem_blockSumZeroFlat, positionSums_eq_blockSum,
    positionSums_eq_blockSum, external_comp_blockIndex, ← mem_blockSumZero, ← mem_blockSumZero]
  exact blockMix_mem_blockSumZero_iff (m4Equiv K h35).injective (five_ne_zero_of_thirtyFive h35) _

end Poseidon2.Plonky3

/-! ### Transposes of the two layers

In linear (correlation) cryptanalysis a mask is carried through a linear map by its transpose.
`WideTrail.Algebra.Transpose` takes the linear branch number of a layer, as a definition, to be
the differential branch number of its transpose. The results below identify the transposes of the
two layers of this file:

* `external_dotProduct`: `external h35 x ⬝ᵥ y = x ⬝ᵥ T y` for all states `x, y`, where `T` is
  `circ(2 m4ᵀ, m4ᵀ, m4ᵀ, m4ᵀ)` on the flat state and `m4ᵀ = circ(2, 1, 1, 3)`
  (`Poseidon2.m4_transpose`);
* `external_transpose_isBranchBound`: under the `m4Primes` hypothesis `T` has branch number at
  least `8`, the bound `external_isBranchBound` gives for the external layer itself;
* `Diag.internal_dotProduct`: the internal layer is its own transpose for every diagonal,
  `Diag.internal d c hc hd hs x ⬝ᵥ y = x ⬝ᵥ Diag.internal d c hc hd hs y`
  (`Poseidon2.diagPlusOnes_dotProduct`); `internal_dotProduct` is the case `d = sp1Diag K`.

These are facts about the two linear layers alone. No correlation, linear trail, linear hull or
linear-attack bound is proved, and nothing is said about the S-box or about whole rounds. -/

namespace Poseidon2.Plonky3

open BlockCirculant
open scoped Matrix

variable {K : Type*} [Field K]

/-- **The transpose of the external layer.** For all states `x, y`,
`external h35 x ⬝ᵥ y = x ⬝ᵥ T y`, where `T` is `circ(2 m4ᵀ, m4ᵀ, m4ᵀ, m4ᵀ)` on the flat state:
`Poseidon2.blockMix_m4_sixteen_dotProduct` applied to `external_apply`. -/
theorem external_dotProduct (h35 : (35 : K) ≠ 0) (x y : Fin 16 → K) :
    external h35 x ⬝ᵥ y =
      x ⬝ᵥ (blockMix (B := Fin 4) (Matrix.mulVecLin (m4 K)ᵀ) (y ∘ blockIndex) ∘
        blockIndex.symm) := by
  rw [external_apply, m4Equiv_toLinearMap]
  exact blockMix_m4_sixteen_dotProduct x y

/-- **Branch number `8` for the transpose of the external layer.** Under the `m4Primes`
hypothesis, the map `T` of `external_dotProduct` has branch number at least `8`
(`Poseidon2.isBranchBound_blockMix_m4_transpose_sixteen`). -/
theorem external_transpose_isBranchBound [DecidableEq K]
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) :
    isBranchBound id
      (fun y : Fin 16 → K =>
        blockMix (B := Fin 4) (Matrix.mulVecLin (m4 K)ᵀ) (y ∘ blockIndex) ∘ blockIndex.symm) 8 :=
  isBranchBound_blockMix_m4_transpose_sixteen hprimes

/-- **The internal layer is its own transpose.** For all states `x, y`,
`internal c hc h2 hs x ⬝ᵥ y = x ⬝ᵥ internal c hc h2 hs y` (`Diag.internal_dotProduct` at
`d = sp1Diag K`). -/
theorem internal_dotProduct (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) (hs : (81917 : K) ≠ 0)
    (x y : Fin 16 → K) :
    internal c hc h2 hs x ⬝ᵥ y = x ⬝ᵥ internal c hc h2 hs y :=
  Diag.internal_dotProduct _ c hc _ _ x y

end Poseidon2.Plonky3
