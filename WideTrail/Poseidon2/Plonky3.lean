/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.BlockCirculant
import WideTrail.Algebra.MDS4
import WideTrail.Hades.Krylov
import Mathlib.Tactic.FinCases

/-!
# The Plonky3 Poseidon2 permutation of width sixteen, as SP1 uses it

SP1 hashes with Plonky3's `Poseidon2<F, Poseidon2ExternalMatrixGeneral, DiffusionMatrix…, 16, D>`:
KoalaBear with `D = 3` in `sp1-primitives` `6.10.0` (`src/lib.rs:1145`), BabyBear with `D = 7`
in `sp1-primitives` `5.2.4` (`src/lib.rs:1106-1124`). Both run the same skeleton, from the
byte-identical sources of `p3-poseidon2` `0.4.3-succinct` and `0.2.3-succinct`. This file models
that skeleton over an arbitrary field `K`. Every condition on `K` is an explicit hypothesis that a
concrete prime field discharges by `decide`; no field, S-box, scale or constant table is fixed.

## The model

A state is `Fin 16 → K`, and coordinate `i` is the Rust `state[i]`. Block `b`, position `c` is
coordinate `4 b + c` (`blockIndex`, Mathlib's `finProdFinEquiv`; `blockIndex_val`).

* `external h35`: the external layer `circ(2 M4, M4, M4, M4)`, where `M4 = m4 = circ(2, 3, 1, 1)`
  is Plonky3's `MDSMat4`. It is `BlockCirculant.blockMixEquiv` with `N = m4Equiv`, conjugated to
  the flat state, and needs only `35 ≠ 0`. The code (`mds_light_permutation`, `p3-poseidon2`
  `src/matrix.rs:110-139`, called at `:156`) applies `M4` to each block and then adds position
  sums; `external_apply_blockIndex` states
  `out[4 b + c] = (M4 x_b)[c] + ∑_{b'} (M4 x_{b'})[c]`, and `external_eq_mdsLight` identifies the
  layer with `mdsLight`, a transcription of those lines.
* `internal c hc h2 hs`: `x_i ↦ c (d_i x_i + ∑_j x_j)` with `d = sp1Diag = (-2, 1, 2, 4, …, 2^13,
  2^15)` (`p3-koala-bear` `0.4.3-succinct` `src/poseidon2.rs:37-58`; the same vector in
  `p3-baby-bear` `0.2.3-succinct` `src/poseidon2.rs:29-49`). The code works on Montgomery
  representatives and returns `R^{-1} (d_i x_i + ∑_j x_j)` with `R = 2^32` (`MONTY_BITS = 32`,
  `p3-koala-bear` `src/koala_bear.rs:21`, `p3-baby-bear` `src/baby_bear.rs:17`; the layer at
  `p3-koala-bear` `src/poseidon2.rs:95-113`, `p3-baby-bear` `src/poseidon2.rs:85-103`). The
  scale `c` is a parameter whose intended value is `R^{-1}`, i.e. `c * 2^32 = 1`; only `c ≠ 0`
  is used. The layer is invertible under `2 ≠ 0` and `81917 ≠ 0`, where `81917 = 11^2 * 677 =
  2^15 (1 + ∑ 1/d_i)`, and `internal_injective_iff` shows the second condition is exact.
* `rounds hK rP sbox values = Hades.hadesSchedule 4 rP 4 {0} (fun _ _ => sbox) (linear hK rP)
  values`: four full rounds, `rP` partial rounds with the S-box on coordinate `0`, four full
  rounds, the same S-box `sbox` everywhere (intended: `x ↦ x^D`), the external layer in full
  rounds and the internal layer in partial rounds. The code runs `rounds_f_half = rounds_f / 2`
  full rounds on each side (`p3-poseidon2` `src/lib.rs:182`), and SP1 sets `ROUNDS_F = 8`
  (`slop-koala-bear` `6.10.0` `src/koala_bear_poseidon2.rs:49`; `sp1-primitives` `5.2.4`
  `src/lib.rs:1108`), hence four. SP1 sets `ROUNDS_P = 20` for KoalaBear
  (`slop-koala-bear` `6.10.0` `src/koala_bear_poseidon2.rs:50`) and `ROUNDS_P = 13` for BabyBear
  (`sp1-primitives` `5.2.4` `src/lib.rs:1109`).
* `permutation hK rP sbox values x = Hades.execute (rounds hK rP sbox values) (external x)
  (8 + rP)`: the initial external layer (`p3-poseidon2` `src/lib.rs:179`), then the three loops
  of `src/lib.rs:182-201`.

`Conditions c` bundles `35 ≠ 0`, `2 ≠ 0`, `81917 ≠ 0` and `c ≠ 0`, under which both layers are
invertible. `Conditions.of_primes` derives it from the `m4Primes` hypothesis, `677 ≠ 0` and
`c ≠ 0`. So `Conditions c` and the `m4Primes` hypothesis of the branch bound both hold over every
field whose characteristic is none of `2, 3, 5, 7, 11, 17, 677`, for every nonzero `c`.

**Partial-round constants.** A HADES round adds a whole row `values n`, but the code adds a
partial-round constant to `state[0]` only (`p3-poseidon2` `src/lib.rs:191`). Tables whose partial
rows vanish off coordinate `0` (`PartialRowsAtZero`) model exactly that: `rounds_apply_middle`
shows such a round is the code's round `internal (update x 0 (sbox (x 0 + v)))`. `roundValues`
builds such a table from the eight external rows the full-round loops read and the `rP`
internal scalars. `rounds_apply_prefix` and `rounds_apply_suffix` give the full rounds. A raw
constant table need not have this form: SP1 `5.2.4`'s BabyBear table `RC_16_30` is not
`PartialRowsAtZero`, and the code's table is `roundValues 13 ext int` built from parts of it
(see `roundValues`).

## Results, for every round-constant table

* `permutation_bijective`.
* `external_isBranchBound`: under the `m4Primes` hypothesis the external layer has branch number
  at least `8`.
* `activity`: two distinct inputs incur at least `32` charged S-box applications, all counted in
  the full rounds. `activity_with_middle` adds `rP / w` when no nonzero difference stays
  inactive through `w` consecutive partial rounds with the unscaled layer `diag d + J`; by
  `inactiveSpace_internal` the scale does not matter, so a Krylov certificate
  (`Hades.inactiveSpace_diagPlusOnes_eq_bot`) need not mention `c`.
* `independent_key_probability`, `independent_key_probability_with_middle`: if `sbox` has
  differential uniformity at most `u` and `u * 2^dd ≤ |K|`, then for every nonzero trail `T`,
  `keyCount * 2^(dd * 32) ≤ |K^16|^(8 + rP)`, and with exponent `dd * (32 + rP / w)` under the
  inactive-space hypothesis.
* `finrank_inactiveSpace_internal`: at least `16 - r` dimensions of differences stay inactive
  through `r` consecutive partial rounds (at least `3` for `r = 13`). A difference entering the
  partial rounds in that space crosses them with no charged S-box (`Hades.IsTrail.free_window`),
  and `middle_term_eq_zero` shows that for `rP < 16` the middle term `rP / w` is `0`.

## What is not claimed

The activity counts are lower bounds on charged S-boxes for actual input pairs; they are not
claimed to be attained. The probability statements concern one trail in the model with an
additional independent uniform key per round; they are not statements about the permutation with
its fixed constants, and not about a differential. Nothing is said about subspace-trail
resistance beyond the inactive-space statements here, about algebraic attacks, about sponge or
duplex constructions built on the permutation, or about equivalence with the Rust code or the AIR
beyond the transcriptions stated here (`external_eq_mdsLight` and the round lemmas). The
inactive-space hypothesis can fail for some fields (`Checks/Plonky3.lean`, `ZMod 23`).
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

/-! ### The internal layer -/

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
image is `c (d_i x_i + ∑_j x_j)` (`internal_apply`). The code's value of `c` is
`R^{-1}` for `R = 2^32` (`MONTY_BITS = 32`, `p3-koala-bear` `0.4.3-succinct`
`src/koala_bear.rs:21`, `p3-baby-bear` `0.2.3-succinct` `src/baby_bear.rs:17`); here `c` is any
nonzero scalar. -/
def internal (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) (hs : (81917 : K) ≠ 0) :
    (Fin 16 → K) ≃ₗ[K] (Fin 16 → K) :=
  diagPlusOnesEquiv c (sp1Diag K) hc (sp1Diag_ne_zero h2)
    ((one_add_sum_inv_ne_zero_iff h2).mpr hs)

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
layer is that of `diag d + J`, whatever the nonzero scale `c`. -/
theorem inactiveSpace_internal (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) (mask : Finset (Fin 16)) (r : ℕ) :
    Hades.inactiveSpace (internal c hc h2 hs).toLinearMap mask r =
      Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) mask r :=
  Hades.inactiveSpace_diagPlusOnes hc _ mask r

/-- **At least `16 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds** (rank–nullity, `Hades.card_sub_le_finrank_inactiveSpace`). For `r = 13` this is at
least `3`. It is a lower bound only. -/
theorem finrank_inactiveSpace_internal (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) (r : ℕ) :
    16 - r ≤ Module.finrank K
      (Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) r) := by
  have h := Hades.card_sub_le_finrank_inactiveSpace (internal c hc h2 hs).toLinearMap
    ({0} : Finset (Fin 16)) r
  rwa [Fintype.card_fin, Finset.card_singleton, mul_one] at h

/-- For `r < 16`, some nonzero difference stays inactive through `r` consecutive partial
rounds. -/
theorem inactiveSpace_internal_ne_bot (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) {r : ℕ} (hr : r < 16) :
    Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) r ≠ ⊥ :=
  Hades.inactiveSpace_ne_bot _ _ r (by simpa using hr)

/-- At least three dimensions of differences stay inactive through thirteen consecutive partial
rounds, the number of partial rounds in SP1's BabyBear instance. -/
theorem three_le_finrank_inactiveSpace_thirteen (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : (81917 : K) ≠ 0) :
    3 ≤ Module.finrank K
      (Hades.inactiveSpace (internal c hc h2 hs).toLinearMap ({0} : Finset (Fin 16)) 13) :=
  finrank_inactiveSpace_internal c hc h2 hs 13

/-- **For fewer than sixteen partial rounds the middle term is zero.** A window `w` meeting the
hypothesis of `activity_with_middle` has `w ≥ 16`, since shorter windows leave a nonzero inactive
difference (`Hades.inactiveSpace_ne_bot`); so `rP / w = 0` when `rP < 16`. For BabyBear's
thirteen partial rounds, `activity_with_middle` therefore gives nothing beyond `activity`. -/
theorem middle_term_eq_zero {rP w : ℕ} (hr : rP < 16)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) w = ⊥) :
    rP / w = 0 := by
  have hw : 16 ≤ w := by
    by_contra h
    refine Hades.inactiveSpace_ne_bot _ _ w ?_ htriv
    rw [Finset.card_singleton, mul_one, Fintype.card_fin]
    omega
  exact Nat.div_eq_of_lt (by omega)

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

/-! ### The schedule -/

variable {c : K}

/-- The linear layer of round `n`: external in the four full rounds on each side, internal in
the `rP` partial rounds in between. -/
def linear (hK : Conditions c) (rP n : ℕ) : (Fin 16 → K) ≃ₗ[K] (Fin 16 → K) :=
  if n < 4 ∨ 4 + rP ≤ n then external hK.thirtyFive
  else internal c hK.scale hK.two hK.shermanMorrison

/-- The rounds: four full, `rP` partial with the S-box on coordinate `0`, four full, with the
same S-box everywhere and an arbitrary table of round constants. Four is the code's
`rounds_f_half = rounds_f / 2` (`p3-poseidon2` `src/lib.rs:182`) for SP1's `ROUNDS_F = 8`
(`slop-koala-bear` `6.10.0` `src/koala_bear_poseidon2.rs:49`; `sp1-primitives` `5.2.4`
`src/lib.rs:1108`). SP1's `rP` is `ROUNDS_P`: `20` for KoalaBear (`slop-koala-bear` `6.10.0`
`src/koala_bear_poseidon2.rs:50`) and `13` for BabyBear (`sp1-primitives` `5.2.4`
`src/lib.rs:1109`). -/
def rounds (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) :
    ℕ → Hades.RoundSpec (Fin 16) K :=
  Hades.hadesSchedule 4 rP 4 {0} (fun _ _ => sbox) (linear hK rP) values

/-- **The permutation.** The initial external layer (`p3-poseidon2` `src/lib.rs:179`), then the
`8 + rP` rounds of `rounds` (`src/lib.rs:182-201`). -/
def permutation (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    (x : Fin 16 → K) : Fin 16 → K :=
  Hades.execute (rounds hK rP sbox values) (external hK.thirtyFive x) (8 + rP)

theorem permutation_bijective (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) : Function.Bijective (permutation hK rP sbox values) :=
  (Hades.execute_bijective (rounds hK rP sbox values) (8 + rP)).comp
    (external hK.thirtyFive).bijective

theorem linear_prefix (hK : Conditions c) (rP : ℕ) {j : ℕ} (hj : j < 4) :
    linear hK rP j = external hK.thirtyFive := by
  simp [linear, hj]

theorem linear_middle (hK : Conditions c) (rP : ℕ) {j : ℕ} (hj : j < rP) :
    linear hK rP (4 + j) = internal c hK.scale hK.two hK.shermanMorrison := by
  simp [linear, show ¬(4 + j < 4) by omega, show ¬(4 + rP ≤ 4 + j) by omega]

theorem linear_suffix (hK : Conditions c) (rP j : ℕ) :
    linear hK rP (4 + rP + j) = external hK.thirtyFive := by
  simp [linear]

/-! ### The rounds against the code -/

/-- A first-half full round is the code's round (`p3-poseidon2` `src/lib.rs:183-187`): add the
row, apply the S-box to every coordinate, then the external layer. -/
theorem rounds_apply_prefix (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {j : ℕ} (hj : j < 4) (x : Fin 16 → K) :
    (rounds hK rP sbox values j).apply x =
      external hK.thirtyFive (fun i => sbox (x i + values j i)) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, linear_prefix hK rP hj,
    Hades.hadesMask_prefix 4 rP 4 _ hj]
  congr 1
  funext i
  simp

/-- A second-half full round is the code's round (`p3-poseidon2` `src/lib.rs:197-201`). -/
theorem rounds_apply_suffix (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {j : ℕ} (hj : j < 4) (x : Fin 16 → K) :
    (rounds hK rP sbox values (4 + rP + j)).apply x =
      external hK.thirtyFive (fun i => sbox (x i + values (4 + rP + j) i)) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, linear_suffix hK rP j,
    Hades.hadesMask_suffix 4 rP 4 _ hj]
  congr 1
  funext i
  simp

/-- The partial rows of a round-constant table vanish off the S-box coordinate. Plonky3 adds a
partial-round constant to `state[0]` only (`p3-poseidon2` `src/lib.rs:190-191`), and a HADES round
adds the whole row, so tables with this property are the ones the code can realise. A raw
constant table from a source need not have it; see `roundValues`. -/
def PartialRowsAtZero (rP : ℕ) (values : ℕ → Fin 16 → K) : Prop :=
  ∀ j < rP, ∀ i : Fin 16, i ≠ 0 → values (4 + j) i = 0

/-- **A partial round is the code's round** (`p3-poseidon2` `src/lib.rs:190-194`): add the
constant to `x 0`, apply the S-box to `x 0` alone, then the internal layer. -/
theorem rounds_apply_middle (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (hv : PartialRowsAtZero rP values) {j : ℕ} (hj : j < rP)
    (x : Fin 16 → K) :
    (rounds hK rP sbox values (4 + j)).apply x =
      internal c hK.scale hK.two hK.shermanMorrison
        (Function.update x 0 (sbox (x 0 + values (4 + j) 0))) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, linear_middle hK rP hj,
    Hades.hadesMask_middle 4 rP 4 _ hj]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hi, hv j hj i hi]

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

/-- With a table built by `roundValues`, partial round `j` adds `int j` to `x 0`, applies
the S-box there, then the internal layer (`p3-poseidon2` `src/lib.rs:190-194`). -/
theorem rounds_roundValues_apply_middle (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (ext : Fin 8 → Fin 16 → K) (int : Fin rP → K) {j : ℕ} (hj : j < rP) (x : Fin 16 → K) :
    (rounds hK rP sbox (roundValues rP ext int) (4 + j)).apply x =
      internal c hK.scale hK.two hK.shermanMorrison
        (Function.update x 0 (sbox (x 0 + int ⟨j, hj⟩))) := by
  rw [rounds_apply_middle hK rP sbox _ (roundValues_partialRowsAtZero rP ext int) hj,
    roundValues_middle rP ext int hj, Pi.single_eq_same]

/-! ### Activity -/

section Activity

variable [DecidableEq K]

/-- **Branch number `8` for the external layer.** `m4` has branch number `5` under the
`m4Primes` hypothesis (`m4Equiv_isBranchBound`), and that hypothesis also makes `1, …, 5` nonzero
(`m4_natCast_ne_zero_of_le_five`), so `BlockCirculant.isBranchBound_blockMix_sixteen` applies. -/
theorem external_isBranchBound (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (h35 : (35 : K) ≠ 0) :
    isBranchBound id (external h35) 8 :=
  isBranchBound_blockMix_sixteen (N := (m4Equiv K h35).toLinearMap)
    (m4Equiv_isBranchBound hprimes h35) (m4_natCast_ne_zero_of_le_five hprimes)

/-- The branch hypothesis of the first full block, in the form `Hades.hades_bound` takes. -/
theorem full_prefix (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP j : ℕ)
    (hj : j + 1 < 4) : isBranchBound id (linear hK rP j) 8 := by
  rw [linear_prefix hK rP (by omega)]
  exact external_isBranchBound hprimes hK.thirtyFive

/-- The branch hypothesis of the second full block. -/
theorem full_suffix (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP j : ℕ)
    (_hj : j + 1 < 4) : isBranchBound id (linear hK rP (4 + rP + j)) 8 := by
  rw [linear_suffix hK rP j]
  exact external_isBranchBound hprimes hK.thirtyFive

/-- **Thirty-two active S-boxes in the full rounds.** For every S-box, scale and constant table,
two distinct inputs incur at least `32` charged S-box applications over the `8 + rP` rounds:
`8` for each of the two pairs of full rounds on each side. The partial rounds are charged
nothing here. A lower bound; it is not claimed to be attained. -/
theorem activity (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ)
    (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {x y : Fin 16 → K} (hxy : x ≠ y) :
    32 ≤ Hades.scheduledWeight (rounds hK rP sbox values)
      (Hades.differenceTrace (rounds hK rP sbox values)
        (external hK.thirtyFive x) (external hK.thirtyFive y)) 0 (8 + rP) := by
  have h := Hades.hades_bound 4 rP 4 8 {0} (fun _ _ => sbox) (linear hK rP) values
    (fun h => hxy ((external hK.thirtyFive).injective h)) (full_prefix hK hprimes rP)
    (full_suffix hK hprimes rP)
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact le_trans (le_of_eq (by norm_num)) h

/-- **The partial rounds charged.** If no nonzero difference stays inactive through `w`
consecutive partial rounds with the unscaled layer `diag d + J` (`htriv`), then each of the
`rP / w` disjoint windows of `w` partial rounds charges at least one S-box. The hypothesis does
not mention the scale `c` (`inactiveSpace_internal`); for a concrete field it is a Krylov
certificate (`Hades.inactiveSpace_diagPlusOnes_eq_bot`). With `w = 16`: `33` for `rP = 20`, and
`32` for `rP = 13`, where the middle term vanishes. -/
theorem activity_with_middle (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0)
    (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {w : ℕ}
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) w = ⊥)
    {x y : Fin 16 → K} (hxy : x ≠ y) :
    32 + rP / w ≤ Hades.scheduledWeight (rounds hK rP sbox values)
      (Hades.differenceTrace (rounds hK rP sbox values)
        (external hK.thirtyFive x) (external hK.thirtyFive y)) 0 (8 + rP) := by
  have htriv' : Hades.inactiveSpace
      (internal c hK.scale hK.two hK.shermanMorrison).toLinearMap ({0} : Finset (Fin 16)) w =
        ⊥ := by
    rw [inactiveSpace_internal]
    exact htriv
  have h := Hades.outer_middle_bound (rounds hK rP sbox values)
    (fun h => hxy ((external hK.thirtyFive).injective h)) 4 rP 4 8 w
    (fun j hj => Hades.hadesMask_prefix 4 rP 4 _ hj)
    (fun j hj => Hades.hadesMask_suffix 4 rP 4 _ hj)
    (full_prefix hK hprimes rP) (full_suffix hK hprimes rP)
    (internal c hK.scale hK.two hK.shermanMorrison) {0}
    (fun j hj => linear_middle hK rP hj)
    (fun j hj => Hades.hadesMask_middle 4 rP 4 _ hj) htriv'
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact le_trans (le_of_eq (by norm_num)) h

/-! ### The independent-key trail bound -/

variable [Fintype K]

/-- **Trail bound from the full rounds.** If `sbox` has differential uniformity at most `u` and
`u * 2^dd ≤ |K|`, the number of keys realising any fixed nonzero trail `T`, in the model with an
additional independent uniform key per round, times `2^(32 dd)`, is at most the number of all
key sequences. This concerns one trail in that model only: not the permutation with its fixed
constants, and not a differential. -/
theorem independent_key_probability (hK : Conditions c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0)
    (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K) {u dd : ℕ} (hu : IsDiffUniform sbox u)
    (hd : u * 2 ^ dd ≤ Fintype.card K) {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hK rP sbox values) (8 + rP) T x * 2 ^ (dd * 32)
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have h := Hades.hades_probability (Idx := Fin 16) (K := K) (u := u) (d := dd)
    4 rP 4 8 {0} (fun _ _ => sbox) (linear hK rP) values (fun _ _ _ => hu) hd
    (full_prefix hK hprimes rP) (full_suffix hK hprimes rP) h0 x
  rw [show dd * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) = dd * 32 by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

/-- **Trail bound with the partial rounds charged.** As `independent_key_probability`, with
exponent `dd * (32 + rP / w)` under the inactive-space hypothesis of `activity_with_middle`. The
sample space is the same: one trail, an additional independent uniform key per round. -/
theorem independent_key_probability_with_middle (hK : Conditions c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u dd w : ℕ} (hu : IsDiffUniform sbox u) (hd : u * 2 ^ dd ≤ Fintype.card K)
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : K) (sp1Diag K)) ({0} : Finset (Fin 16)) w = ⊥)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hK rP sbox values) (8 + rP) T x * 2 ^ (dd * (32 + rP / w))
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have htriv' : Hades.inactiveSpace
      (internal c hK.scale hK.two hK.shermanMorrison).toLinearMap ({0} : Finset (Fin 16)) w =
        ⊥ := by
    rw [inactiveSpace_internal]
    exact htriv
  have h := Hades.hades_probability_with_middle (Idx := Fin 16) (K := K) (u := u) (d := dd)
    4 rP 4 8 w {0} (fun _ _ => sbox) (linear hK rP) values (fun _ _ _ => hu) hd
    (full_prefix hK hprimes rP) (full_suffix hK hprimes rP)
    (internal c hK.scale hK.two hK.shermanMorrison) (fun j hj => linear_middle hK rP hj)
    htriv' h0 x
  rw [show dd * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 + rP / w) = dd * (32 + rP / w) by
    norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

end Activity

end Poseidon2.Plonky3

/-! ### The independent-key trail bound as an exact ratio

`independent_key_probability` and `independent_key_probability_with_middle` charge a whole
number `dd` of bits per charged S-box, where `u * 2^dd ≤ |K|`. The two results below keep the
ratio `|K| / u` per charged S-box exact. The sample space is the same: one trail, an additional
independent uniform key per round. -/

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
      ≤ u ^ 32 * Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have h := Hades.hades_probability_exact (Idx := Fin 16) (K := K) (u := u)
    4 rP 4 8 {0} (fun _ _ => sbox) (linear hK rP) values (fun _ _ _ => hu)
    (full_prefix hK hprimes rP) (full_suffix hK hprimes rP) h0 x
  rw [show (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 = 32 by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

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
      ≤ u ^ (32 + rP / w) * Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have htriv' : Hades.inactiveSpace
      (internal c hK.scale hK.two hK.shermanMorrison).toLinearMap ({0} : Finset (Fin 16)) w =
        ⊥ := by
    rw [inactiveSpace_internal]
    exact htriv
  have h := Hades.hades_probability_with_middle_exact (Idx := Fin 16) (K := K) (u := u)
    4 rP 4 8 w {0} (fun _ _ => sbox) (linear hK rP) values (fun _ _ _ => hu)
    (full_prefix hK hprimes rP) (full_suffix hK hprimes rP)
    (internal c hK.scale hK.two hK.shermanMorrison) (fun j hj => linear_middle hK rP hj)
    htriv' h0 x
  rw [show (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 + rP / w = 32 + rP / w by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

end Poseidon2.Plonky3
