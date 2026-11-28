/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BabyBear

/-!
# A certificate for the OpenVM v2.1.0 BabyBear Poseidon2 permutation of width sixteen

OpenVM `v2.1.0` (`openvm-org/openvm`, tag `v2.1.0`, commit
`05f3b73e7294fbb6d38155abafc98f1fe2bcfb73`) hashes with the BabyBear Poseidon2 permutation of
width sixteen that `p3-baby-bear` `0.4.3` builds in `default_babybear_poseidon2_16()`
(`src/poseidon2.rs:117-128`). OpenVM's workspace `Cargo.toml` pins every `p3-*` dependency it
declares at `=0.4.3` (`:227-237`; `p3-baby-bear` at `:230`, `p3-poseidon2` at `:235`) and `zkhash`
to `zkhash-axiom` `0.2.0` (`:239`). `Cargo.lock` resolves `p3-baby-bear` `0.4.3` from crates.io
with checksum `3a1a49f4d9c8b8cbdab61e25d9de1b78b3c8347dd2fb88b11d990b3efa8cdd3a`
(`Cargo.lock:5850-5854`), which is the SHA-256 of the crate archive read here; its
`src/poseidon2.rs` has SHA-256 `876c96fe1771693e585131518a81dfd51923deb5ba8eec3c9e69e1232e459d97`.
`Cargo.lock` also resolves `p3-monty-31` `0.4.3`, which the workspace `Cargo.toml` does not
declare (`:5990-5994`, checksum `c9fe0be661891af1f703ceaf57334fcbd540804988984dc2b500dd99740e7c81`),
and `p3-poseidon2` `0.4.3` (`:6013-6017`, checksum
`2c6fc2368447576283f8b3849a36095017f25addf06eab9e33b0ce7f96b0b99d`) from crates.io, with the
checksums of the archives read here. Below, "`p3-x` `0.4.3`" means that crates.io crate, with
paths relative to its root. OpenVM runs the permutation on three code paths:

* **The STARK backend.** `openvm-stark-sdk`, from `openvm-org/stark-backend` at tag `v2.1.0`
  (`Cargo.toml:161`; commit `a6b4761ad9a098f3a166740d22ad60b96400cd65`, `Cargo.lock:5629-5631`),
  imports `default_babybear_poseidon2_16` (`crates/stark-sdk/src/config/baby_bear_poseidon2.rs:18`),
  sets `Perm = Poseidon2BabyBear<WIDTH>` with `WIDTH = 16` (`:23`, `:27`), builds its hash
  `PaddingFreeSponge` and its compression `TruncatedPermutation` from it (`:29-30`, `:65-77`), and
  caches it in `poseidon2_perm()` (`:260-263`) for the duplex sponges (`:279-291`).
* **The VM's Poseidon2 periphery chip**, the direct Poseidon2 AIR of the memory Merkle tree
  (`crates/vm/src/system/mod.rs:260-267`) and its chip (`:416-419`). Both take
  `vm_poseidon2_config()` (`crates/vm/src/arch/config.rs:45-48`), that is
  `Poseidon2Config::default()` (`crates/circuits/poseidon2-air/src/config.rs:18-24`, constants at
  `:60-67`), whose round constants `horizen_round_consts()` selects from
  `zkhash::poseidon2::poseidon2_instance_babybear::RC16` (`src/babybear.rs:22-56`). The chip's
  `Poseidon2SubChip` runs Plonky3's `Poseidon2` over OpenVM's `BabyBearPoseidon2LinearLayers`
  (`src/lib.rs:64-71`, `:126-132`), and its trace generation uses the same layers (`:96-104`):
  `mds_light_permutation` with `MDSMat4` (`src/permute.rs:29-31`) and
  `babybear_internal_linear_layer` with `INTERNAL_DIAG_MONTY_16` (`src/babybear.rs:58-90`).
* **The host-side VM hasher.** `vm_poseidon2_hasher`
  (`crates/vm/src/arch/hasher/poseidon2.rs:15-24`) builds `Poseidon2BabyBear::new` from the
  constants of the same configuration.

This file instantiates the diagonal-generic model `Plonky3.Diag` of
`WideTrail.Poseidon2.Plonky3` with that permutation and discharges every hypothesis by `decide`,
so the theorems below have no remaining premises. Field, S-box, round numbers and external
layer coincide with those of SP1 `5.2.4`'s BabyBear permutation in `WideTrail.Poseidon2.BabyBear`;
the internal layer and the round constants are different. This file reuses that file's field,
S-box and exponent arithmetic.

## The pinned parameters

* **Field and S-box.** Those of `WideTrail.Poseidon2.BabyBear`, reused: `F = ZMod modulus` with
  `modulus = 0x78000001 = 2^31 - 2^27 + 1` (`p3-baby-bear` `0.4.3` `src/baby_bear.rs:18`), prime
  by the Lucas certificate of `WideTrail.Poseidon2.BabyBearPrimality`, and `BabyBear.sbox`,
  `x ↦ x^7` with inverse `x ↦ x^1725656503`. The degree is `BABYBEAR_S_BOX_DEGREE = 7`
  (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:35`), the parameter `D` of `Poseidon2BabyBear`
  (`:41-47`), and OpenVM's own `BABY_BEAR_POSEIDON2_SBOX_DEGREE` is also `7`
  (`crates/circuits/poseidon2-air/src/lib.rs:44`); the code's seventh root is `exp_1725656503`
  (`p3-baby-bear` `0.4.3` `src/baby_bear.rs:32-38`). The S-box has differential uniformity at
  most `6` (`BabyBear.sbox_uniform`).
* **Rounds.** `permute_mut` runs `permute_state_initial`, `permute_state` and
  `permute_state_terminal` (`p3-poseidon2` `0.4.3` `src/lib.rs:107-111`). The first applies
  `mds_light_permutation` (`src/external.rs:321-336`, the call at `:332`) and then one full round
  per row of `BABYBEAR_RC16_EXTERNAL_INITIAL` (four rows; loop at `src/external.rs:299-305`); the
  second runs one partial round per entry of `BABYBEAR_RC16_INTERNAL` (thirteen; loop at
  `p3-monty-31` `0.4.3` `src/poseidon2.rs:76-85`), with the constant and the S-box on `state[0]`
  only (`:78-79`); the third runs one full round per row of `BABYBEAR_RC16_EXTERNAL_FINAL` (four).
  A full round adds the row and raises every coordinate to the seventh power
  (`add_rc_and_sbox_generic`, `p3-poseidon2` `0.4.3` `src/generic.rs:24-30`), then applies the
  external layer. OpenVM's AIR path has the same order
  (`crates/circuits/poseidon2-air/src/permute.rs:62-67`, `:97-125`) and the same counts: width
  `16`, four half-full rounds, thirteen partial rounds (`src/lib.rs:37-41`).
* **External layer.** `external` is `Plonky3.external`, i.e. `circ(2 M4, M4, M4, M4)` with
  `M4 = circ(2, 3, 1, 1)`. `mds_light_permutation` (`p3-poseidon2` `0.4.3`
  `src/external.rs:113-159`, width-sixteen branch `:135-153`) with `MDSMat4` (`apply_mat4`,
  `:60-74`; `MDSMat4`, `:93-102`), passed at `p3-monty-31` `0.4.3` `src/poseidon2.rs:94-111` and at
  OpenVM `src/permute.rs:29-31`, performs the steps that `Plonky3.mdsLight` transcribes: `M4` on
  each block of four, then `sums[i % 4]` added to coordinate `i`. So `external_eq_mdsLight`
  identifies the layer with the code's function.
* **Internal layer.** `internal x i = d_i x_i + ∑_j x_j`, with no scale factor, for the diagonal
  `d = (-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27)`
  (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:221`, and the module comment at `:11`). The Plonky3
  code first sets `state[0] = part_sum - state[0]`, where `part_sum` is the sum of `state[1..]`
  (`p3-monty-31` `0.4.3` `src/poseidon2.rs:80-83`), which gives `d_0 = -2`, and then runs
  `internal_layer_mat_mul` with the full sum (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:216-245`).
  `internalCode` transcribes these statements over `F`, reading `double` as `x + x`, `halve` as
  `x / 2` and `div_2exp_u64(k)` as `x / 2^k`, and `internalCode_eq` proves that it is `internal`.
  That reading of the Montgomery code is not derived in Lean: on representatives, `halve` is
  `halve_u32` (`p3-monty-31` `0.4.3` `src/monty_31.rs:193-195`, `src/utils.rs:91-97`) and
  `div_2exp_u64(k)` for `k ≤ 32` is `monty_reduce(value << (32 - k))` (`src/monty_31.rs:211-223`),
  which are multiplications of the field element by `2^{-1}` and `2^{-k}`; every operation of
  `internal_layer_mat_mul` is a field operation, so there is no factor `R^{-1}`. OpenVM's AIR
  layer `babybear_internal_linear_layer` computes `sum + d_i * state[i]` with `d_i` the canonical
  value of `INTERNAL_DIAG_MONTY_16[i]` (`crates/circuits/poseidon2-air/src/babybear.rs:80-90`);
  `internalAir` transcribes it and `internalAir_eq` proves that it is `internal`. This differs
  from SP1's layer `R^{-1} (diag(-2, 1, 2, 4, …, 2^13, 2^15) + J)`. The trait comment at
  `p3-monty-31` `0.4.3` `src/poseidon2.rs:16-17` ("monty form is `1 + Diag(vec)`", entries "small
  powers of `2`") does not describe this diagonal; the code lines are what is modelled. The
  known-answer test of `Checks/OpenVMBabyBear.lean` exercises the layer end to end and fails with
  the factor `R^{-1}`.
* **The diagonal in `F`.** `diag` lists the canonical representatives; `diag_spec` checks
  `2^{k_i} d_i = n_i` with the numerators `diagNumerator` and exponents `diagShift` of the
  fractions above, so `d_i = n_i / 2^{k_i}` (`diag_eq_div`). Since `15 * 2^27 = p - 1`, the
  entries `1/2^27` and `-1/2^27` are `-15` and `15`. `diagSource` is OpenVM's
  `INTERNAL_DIAG_MONTY_16` with its `u32` expressions in `BabyBear::ORDER_U32 = p`
  (`crates/circuits/poseidon2-air/src/babybear.rs:61-78`; `>> k` is division by `2^k`), and
  `diag_eq_diagSource` shows that it is `diag`.
* **Field conditions.** `conditions : Plonky3.Diag.Conditions diag 1` holds by `decide`: `35 ≠ 0`,
  `d_i ≠ 0` from the table `diagInv` of inverses (`diag_mul_inv`), the Sherman–Morrison condition
  from `1 + ∑ 1/d_i = -2` (`one_add_sum_inv_eq`; the same value over `ℚ`), and the scale `1`.
* **Round constants.** `externalInitial`, `internalConstants` and `externalFinal` are
  `BABYBEAR_RC16_EXTERNAL_INITIAL` (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:60-81`),
  `BABYBEAR_RC16_INTERNAL` (`:112-115`) and `BABYBEAR_RC16_EXTERNAL_FINAL` (`:86-107`), copied
  with the hexadecimal literals of the source. The code maps each literal through
  `BabyBear::new_2d_array` or `new_array` (`p3-monty-31` `0.4.3` `src/monty_31.rs:75-102`), that
  is `MontyField31::new` (`:47-56`), which stores `to_monty` of it (`src/utils.rs:3-9`); so the
  field element is the literal mod `p`, and every literal is below `p`.
  `default_babybear_poseidon2_16` passes the two external tables to
  `ExternalLayerConstants::new(initial, final)` and the internal one to the internal layer.
  `externalConstants` lists the eight external rows in that order, and
  `values = Plonky3.roundValues 13 externalConstants internalConstants` (`values_eq_roundValues`)
  is the `21`-row table whose partial rows are `(c, 0, …, 0)` (`partial_constants_zero`). OpenVM's
  AIR path reads the same values from `RC16` (`zkhash-axiom` `0.2.0`
  `src/poseidon2/poseidon2_instance_babybear.rs:305-663`): rows `0-3`, column `0` of rows `4-16`
  and rows `17-20` (`babybear.rs:32-40`), each converted through its canonical integer
  (`horizen_to_p3_babybear`, `:18-20`). `Checks/OpenVMBabyBear.lean` shows that `values` is `RC16`
  row for row, whose partial rows already vanish off column `0`. The literals were re-extracted
  from `p3-baby-bear` `0.4.3`, from `RC16` with OpenVM's selection, and from Plonky3 `v0.8.0`'s
  `BABYBEAR_POSEIDON2_RC_16_*` (`baby-bear/src/poseidon2.rs:111-177`) outside Lean and compared
  entry by entry with this file; the three sources agree. They are not SP1 `5.2.4`'s table
  `BabyBear.values`.

## Results

No result below has a remaining hypothesis on the field, the diagonal, the S-box or the round
constants.

* `permutation_bijective`; `permutation_bijective_general` for every round-constant table.
* `rounds_apply_prefix`, `rounds_apply_partial`, `rounds_apply_suffix`: each round is the code's
  round with the code's constants.
* `external_isBranchBound`: the external layer has branch number at least `8`.
* `inactive_trivial`, `internal_inactive_trivial`: no nonzero difference stays inactive through
  sixteen consecutive partial rounds, for `diag d + J` and for the code's layer. The proof is the
  diagonal criterion `Plonky3.Diag.inactiveSpace_sixteen_eq_bot_iff`: the entries `d 1, …, d 15`
  are pairwise distinct in `F` (`diag_injOn`, by `decide`). No Krylov table is used.
  `finrank_inactive_eq`: exactly `16 - r` dimensions of differences stay inactive through
  `r ≤ 16` consecutive partial rounds.
* `activity`, `activity_general`: two distinct inputs incur at least `32 + 13 / 16 = 32` charged
  S-box applications over the `21` rounds; the bound counts only S-boxes of the full rounds,
  since the window `16` of the criterion gives `13 / 16 = 0` for the thirteen partial rounds.
* **The partial rounds contribute nothing to this argument**, as for SP1's BabyBear instance:
  `finrank_partial_inactive` (a space of dimension exactly `3` stays inactive through the thirteen
  consecutive partial rounds), `partial_window_term_eq_zero` (every window `w` for which
  `Plonky3.Diag.activity_with_middle` applies has `13 / w = 0`) and `exists_pair_partial_free`
  (distinct inputs whose difference charges no S-box in any of the thirteen partial rounds). This
  is the consequence of having fewer partial rounds than the width; it is not an attack, and such
  pairs still incur the `32` charged S-boxes of the full rounds.
* `independent_key_probability`, `independent_key_probability_general`: for every nonzero trail
  `T`, `keyCount * 2^(28 * (32 + 13 / 16)) ≤ |F^16|^(8 + 13)`; the exponent is `896`
  (`probability_exponent`).
* `independent_key_probability_exact`, `independent_key_probability_sharp`, and their `_general`
  forms: for every nonzero trail `T`, `keyCount * p^32 ≤ 6^32 * |F^16|^(8 + 13)` with
  `32 = 32 + 13 / 16`, and `keyCount * 2^906 ≤ |F^16|^(8 + 13)`. `906` is the largest exponent
  this arithmetic gives (`sharp_exponent_bound`; `Checks/OpenVMBabyBear.lean` shows that `907`
  fails).
* `independent_key_differential_exact`, `independent_key_differential_sharp`, and their
  `_general` forms: for every nonzero input difference `a`, every output difference `b` and every
  input `x`, the key count of the differential `(a, b)` over the `21` rounds that follow the
  initial external layer satisfies `diffKeyCount * p^7 ≤ 6^7 * |F^16|^21` and
  `diffKeyCount * 2^198 ≤ |F^16|^21`. Only `7` S-boxes of the first two full rounds are charged,
  one fewer than the branch number `8`; `198` is the largest exponent this arithmetic gives
  (`BabyBear.differential_sharp_exponent_bound`; `Checks/OpenVMBabyBear.lean` shows that `199`
  fails).

The counts and exponents are those of SP1's BabyBear instance: they depend only on `p`, `u = 6`,
the branch number `8`, the window `16` and the round numbers, which the two instances share.
`Checks/OpenVMBabyBear.lean` holds the known-answer test against the expected output of Plonky3
`v0.8.0`'s `test_default_babybear_poseidon2_width_16`, which uses the deployed constants.

## What is not claimed

The activity counts are lower bounds on charged S-box applications for actual input pairs; they
are not claimed to be attained. The trail-probability statements concern one trail in the model
with an additional independent uniform key per round. The differential statements
(`independent_key_differential_*`) bound the key-averaged differential of the rounds after the
initial external layer, in the same model, and charge only `B - 1 = 7` S-boxes of the first two
full rounds. None of these is a statement about the permutation with its fixed constants, or about
any one key. Nothing is said about subspace-trail resistance beyond the inactive-space statements
here, about algebraic attacks, about the sponge, duplex, compression, Merkle or transcript
constructions built on the permutation, or about equivalence with the Rust code or OpenVM's AIR
(`p3-poseidon2-air` constraints over `BabyBearPoseidon2LinearLayers`) beyond the transcriptions
stated in `WideTrail.Poseidon2.Plonky3` and in this file and the known-answer tests of
`Checks/OpenVMBabyBear.lean`. The AVX2, AVX-512 and NEON code paths, which have their own
internal-layer code, and the CUDA backends are not modelled. The model works with field elements,
not with the Montgomery representatives the code stores. HorizenLabs' own width-sixteen BabyBear
instance `POSEIDON2_BABYBEAR_16_PARAMS` (`zkhash-axiom` `0.2.0`
`src/poseidon2/poseidon2_instance_babybear.rs:2023`) uses the same `RC16` with a different
external matrix (HorizenLabs' `M4`, `src/poseidon2/poseidon2.rs:85-117`) and a different diagonal
(`MAT_DIAG16_M_1`, `poseidon2_instance_babybear.rs:11-28`); it is a different permutation and
nothing here concerns it.
-/

set_option autoImplicit false

open Poseidon2.BabyBear (F State modulus field_card sbox sbox_uniform m4Primes_ne_zero)

namespace Poseidon2.OpenVMBabyBear

/-! ### The internal diagonal -/

/-- The internal diagonal `V = (-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27,
-1/2^8, -1/16, -1/2^27)` (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:221`; `d_0 = -2` from
`p3-monty-31` `0.4.3` `src/poseidon2.rs:82`), entry by entry as canonical representatives in `F`.
`diag_spec` checks each entry against its fraction. -/
def diag : Fin 16 → F :=
  ![2013265919, 1, 2, 1006632961, 3, 4, 1006632960, 2013265918, 2013265917, 2005401601,
    1509949441, 1761607681, 2013265906, 7864320, 125829120, 15]

/-- The numerators `n_i` of the diagonal entries `d_i = n_i / 2^{k_i}`. -/
def diagNumerator : Fin 16 → F := ![-2, 1, 2, 1, 3, 4, -1, -3, -4, 1, 1, 1, 1, -1, -1, -1]

/-- The exponents `k_i` of the denominators of the diagonal entries `d_i = n_i / 2^{k_i}`. -/
def diagShift : Fin 16 → ℕ := ![0, 0, 0, 1, 0, 0, 1, 0, 0, 8, 2, 3, 27, 8, 4, 27]

/-- **The diagonal entries are the code's fractions**: `2^{k_i} d_i = n_i` in `F` for every `i`,
by `decide`. -/
theorem diag_spec : ∀ i, 2 ^ diagShift i * diag i = diagNumerator i := by
  decide

/-- `d_i = n_i / 2^{k_i}` in `F`, from `diag_spec` and `2 ≠ 0`. -/
theorem diag_eq_div (i : Fin 16) : diag i = diagNumerator i / 2 ^ diagShift i := by
  rw [eq_div_iff (pow_ne_zero _ (by decide : (2 : F) ≠ 0)), mul_comm]
  exact diag_spec i

/-- OpenVM's `INTERNAL_DIAG_MONTY_16` (`crates/circuits/poseidon2-air/src/babybear.rs:61-78`),
with the `u32` expressions of the source in `BabyBear::ORDER_U32 = modulus`; the shift `>> k`
is written as division by `2^k`. `BabyBear::new_array` stores each value mod `p`, and the AIR
layer multiplies by its canonical value (`:86-88`). -/
def diagSource : Fin 16 → ℕ :=
  ![modulus - 2, 1, 2, (modulus + 1) / 2, 3, 4, (modulus - 1) / 2, modulus - 3, modulus - 4,
    modulus - (modulus - 1) / 2 ^ 8, modulus - (modulus - 1) / 2 ^ 2,
    modulus - (modulus - 1) / 2 ^ 3, modulus - 15, (modulus - 1) / 2 ^ 8, (modulus - 1) / 2 ^ 4, 15]

/-- **OpenVM's array is the diagonal**, entry by entry, by `decide`. -/
theorem diag_eq_diagSource : ∀ i, diag i = (diagSource i : F) := by
  decide

/-- The inverses `1/d_i = (-1/2, 1, 1/2, 2, 1/3, 1/4, -2, -1/3, -1/4, 2^8, 4, 8, 2^27, -2^8, -16,
-2^27)`, as canonical representatives in `F`. -/
def diagInv : Fin 16 → F :=
  ![1006632960, 1, 1006632961, 2, 1342177281, 1509949441, 2013265919, 671088640, 503316480, 256,
    4, 8, 134217728, 2013265665, 2013265905, 1879048193]

theorem diag_mul_inv : ∀ i, diag i * diagInv i = 1 := by
  decide

/-- Every diagonal entry is nonzero. -/
theorem diag_ne_zero : ∀ i, diag i ≠ 0 :=
  Poseidon2.ne_zero_of_mul_eq_one diag_mul_inv

theorem one_add_sum_diagInv : 1 + ∑ i, diagInv i = -2 := by
  decide

/-- **The Sherman–Morrison quantity** `1 + ∑ 1/d_i` is `-2` in `F`, as it is over `ℚ`. -/
theorem one_add_sum_inv_eq : 1 + ∑ i, (diag i)⁻¹ = -2 := by
  rw [Poseidon2.sum_inv_eq_of_mul_eq_one diag_mul_inv, one_add_sum_diagInv]

theorem one_add_sum_inv_ne_zero : 1 + ∑ i, (diag i)⁻¹ ≠ 0 := by
  rw [one_add_sum_inv_eq]
  decide

/-- **The entries `d 1, …, d 15` are pairwise distinct in `F`**, by `decide`. -/
theorem diag_injOn : Set.InjOn diag {i | i ≠ 0} :=
  Plonky3.Diag.injOn_of_forall (by decide)

/-- The four field conditions of the generic model for `diag` and the scale `1`: `35 ≠ 0`,
`d_i ≠ 0`, `1 + ∑ 1/d_i ≠ 0` and `1 ≠ 0`, from the table of inverses. -/
theorem conditions : Plonky3.Diag.Conditions diag 1 :=
  Plonky3.Diag.Conditions.of_mul_eq_one (by decide) diag_mul_inv
    (by rw [one_add_sum_diagInv]; decide) one_ne_zero

/-! ### The linear layers -/

/-- The external layer `circ(2 M4, M4, M4, M4)`, `M4 = circ(2, 3, 1, 1)`. -/
def external : State ≃ₗ[F] State := Plonky3.external conditions.thirtyFive

/-- The external layer is `mds_light_permutation` (`p3-poseidon2` `0.4.3`
`src/external.rs:113-159`). -/
theorem external_eq_mdsLight (x : State) : external x = Plonky3.mdsLight x :=
  Plonky3.external_eq_mdsLight conditions.thirtyFive x

/-- **Branch number `8`** for the external layer. -/
theorem external_isBranchBound : isBranchBound id external 8 :=
  Plonky3.external_isBranchBound m4Primes_ne_zero conditions.thirtyFive

/-- The internal layer `x ↦ (diag d + J) x`, with no scale factor. -/
def internal : State ≃ₗ[F] State :=
  Plonky3.Diag.internal diag 1 conditions.scale conditions.diag conditions.shermanMorrison

theorem internal_apply (x : State) (i : Fin 16) : internal x i = diag i * x i + ∑ j, x j :=
  (Plonky3.Diag.internal_apply diag 1 _ _ _ x i).trans (one_mul _)

theorem internal_toLinearMap : internal.toLinearMap = diagPlusOnes (1 : F) diag :=
  rfl

/-- The Plonky3 code's internal layer, statement by statement, over `F`:
`state[0] = part_sum - state[0]` with `part_sum` the sum of `state[1..]` (`p3-monty-31` `0.4.3`
`src/poseidon2.rs:80-83`), then `internal_layer_mat_mul` with the full sum `sum` (`p3-baby-bear`
`0.4.3` `src/poseidon2.rs:222-243`), reading `double` as `x + x`, `halve` as `x / 2` and
`div_2exp_u64(k)` as `x / 2^k`. -/
def internalCode (x : State) : State :=
  let partSum := x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 + x 10 + x 11 + x 12 + x 13 +
    x 14 + x 15
  let sum := partSum + x 0
  ![partSum - x 0, x 1 + sum, (x 2 + x 2) + sum, x 3 / 2 + sum, sum + (x 4 + x 4) + x 4,
    sum + ((x 5 + x 5) + (x 5 + x 5)), sum - x 6 / 2, sum - ((x 7 + x 7) + x 7),
    sum - ((x 8 + x 8) + (x 8 + x 8)), x 9 / 2 ^ 8 + sum, x 10 / 2 ^ 2 + sum, x 11 / 2 ^ 3 + sum,
    x 12 / 2 ^ 27 + sum, sum - x 13 / 2 ^ 8, sum - x 14 / 2 ^ 4, sum - x 15 / 2 ^ 27]

/-- **The Plonky3 code's statements compute `internal`**: the transcription `internalCode` is
`x ↦ (diag d + J) x` with the diagonal `diag`. -/
theorem internalCode_eq (x : State) : internalCode x = internal x := by
  funext i
  rw [internal_apply, diag_eq_div]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i <;>
    simp [internalCode, diagNumerator, diagShift] <;> ring

/-- OpenVM's AIR layer `babybear_internal_linear_layer` over `F`
(`crates/circuits/poseidon2-air/src/babybear.rs:80-90`): `sum` is the sum of all coordinates
(`:84`), and coordinate `i` becomes `sum + d_i * state[i]` (`:88`) with `d_i` the canonical
value of `INTERNAL_DIAG_MONTY_16[i]` (`diagSource`). -/
def internalAir (x : State) : State :=
  fun i => (∑ j, x j) + (diagSource i : F) * x i

/-- **OpenVM's AIR layer computes `internal`.** -/
theorem internalAir_eq (x : State) : internalAir x = internal x := by
  funext i
  change (∑ j, x j) + (diagSource i : F) * x i = internal x i
  rw [internal_apply, diag_eq_diagSource, add_comm]

/-! ### Round constants -/

/-- `BABYBEAR_RC16_EXTERNAL_INITIAL` (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:60-81`), the
constants of the four initial full rounds, with the hexadecimal literals of the source. -/
def externalInitial : Fin 4 → State :=
  ![![0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
      0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
      0x221e2e36, 0x1ab7202e],
    ![0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
      0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
      0x52eb6ba2, 0x50642905],
    ![0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
      0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
      0x29fbda49, 0x018afffd],
    ![0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
      0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
      0x2cc78315, 0x1e36ea47]]

/-- `BABYBEAR_RC16_EXTERNAL_FINAL` (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:86-107`), the
constants of the four terminal full rounds, with the hexadecimal literals of the source. -/
def externalFinal : Fin 4 → State :=
  ![![0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
      0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
      0x6a2d3d10, 0x20523767],
    ![0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
      0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
      0x49a12590, 0x35ec52a1],
    ![0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
      0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
      0x45e1547b, 0x4a8db2ab],
    ![0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
      0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
      0x3c8bcd87, 0x608758b8]]

/-- `BABYBEAR_RC16_INTERNAL` (`p3-baby-bear` `0.4.3` `src/poseidon2.rs:112-115`), the thirteen
partial-round constants, added to `state[0]`, with the hexadecimal literals of the source. -/
def internalConstants : Fin 13 → F :=
  ![0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb, 0x61210ce0,
    0x3c318939, 0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d]

/-- The eight external rows in the order the full-round loops read them: `externalInitial`, then
`externalFinal` (`ExternalLayerConstants::new(initial, final)`, `p3-baby-bear` `0.4.3`
`src/poseidon2.rs:121-127`). -/
def externalConstants (r : Fin 8) : State :=
  if h : r.val < 4 then externalInitial ⟨r.val, h⟩ else externalFinal ⟨r.val - 4, by omega⟩

/-- The constant table indexed by round: rows `0-3` are `externalInitial`, row `4 + j` is
`(internalConstants j, 0, …, 0)` for `j < 13`, rows `17-20` are `externalFinal`, and rows past
`20` are zero. -/
def values : ℕ → State := Plonky3.roundValues 13 externalConstants internalConstants

/-- **The table is the code's three arrays**, by definition. -/
theorem values_eq_roundValues :
    values = Plonky3.roundValues 13 externalConstants internalConstants :=
  rfl

/-- Partial rows add their constant only at the S-box coordinate, by `decide`. -/
theorem partial_constants_zero :
    ∀ n : Fin 13, ∀ i : Fin 16, i ≠ 0 → values (4 + n.val) i = 0 := by
  decide

theorem partialRowsAtZero : Plonky3.PartialRowsAtZero 13 values :=
  fun j hj i hi => partial_constants_zero ⟨j, hj⟩ i hi

/-! ### The permutation -/

/-- The `21` rounds: four full, thirteen partial with the S-box on coordinate `0`, four full. -/
def rounds : ℕ → Hades.RoundSpec (Fin 16) F := Plonky3.Diag.rounds conditions 13 sbox values

/-- **The permutation**, the model of `default_babybear_poseidon2_16()`: the initial external
layer, then the `21` rounds. -/
def permutation (x : State) : State := Plonky3.Diag.permutation conditions 13 sbox values x

theorem permutation_eq (x : State) : permutation x = Hades.execute rounds (external x) 21 :=
  rfl

theorem permutation_bijective : Function.Bijective permutation :=
  Plonky3.Diag.permutation_bijective conditions 13 sbox values

/-- Bijectivity holds for every round-constant table. -/
theorem permutation_bijective_general (table : ℕ → State) :
    Function.Bijective (Plonky3.Diag.permutation conditions 13 sbox table) :=
  Plonky3.Diag.permutation_bijective conditions 13 sbox table

/-- An initial full round is the code's round (`p3-poseidon2` `0.4.3`
`src/external.rs:299-305`) with row `j` of `BABYBEAR_RC16_EXTERNAL_INITIAL`. -/
theorem rounds_apply_prefix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds j).apply x = external (fun i => sbox (x i + externalInitial ⟨j, hj⟩ i)) := by
  rw [rounds, Plonky3.Diag.rounds_apply_prefix conditions 13 sbox values hj x, values,
    Plonky3.roundValues_prefix 13 _ _ hj]
  simp [externalConstants, hj]
  rfl

/-- **A partial round is the code's round** (`p3-monty-31` `0.4.3` `src/poseidon2.rs:77-84`):
add `internalConstants j` to `state[0]`, apply the S-box to `state[0]` only, then the internal
layer. -/
theorem rounds_apply_partial {j : ℕ} (hj : j < 13) (x : State) :
    (rounds (4 + j)).apply x =
      internal (Function.update x 0 (sbox (x 0 + internalConstants ⟨j, hj⟩))) :=
  Plonky3.Diag.rounds_roundValues_apply_middle conditions 13 sbox _ _ hj x

/-- A terminal full round is the code's round (`p3-poseidon2` `0.4.3`
`src/external.rs:299-305`) with row `j` of `BABYBEAR_RC16_EXTERNAL_FINAL`. -/
theorem rounds_apply_suffix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds (17 + j)).apply x = external (fun i => sbox (x i + externalFinal ⟨j, hj⟩ i)) := by
  rw [show 17 + j = 4 + 13 + j by omega, rounds,
    Plonky3.Diag.rounds_apply_suffix conditions 13 sbox values hj x, values,
    Plonky3.roundValues_suffix 13 _ _ hj]
  simp [externalConstants]
  rfl

/-! ### The partial rounds -/

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds**, for the
unscaled layer `diag d + J`: the diagonal criterion with `diag_injOn`. -/
theorem inactive_trivial :
    Hades.inactiveSpace (diagPlusOnes (1 : F) diag) ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Plonky3.Diag.inactiveSpace_sixteen_eq_bot_iff.mpr diag_injOn

/-- **The same for the code's internal layer.** OpenVM has only thirteen partial rounds. -/
theorem internal_inactive_trivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Plonky3.Diag.inactiveSpace_internal_sixteen_eq_bot _ _ _ _ _ diag_injOn

/-- **Exactly `16 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds**, for `r ≤ 16`. -/
theorem finrank_inactive_eq {r : ℕ} (hr : r ≤ 16) :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) r) =
      16 - r :=
  Plonky3.Diag.finrank_inactiveSpace_internal_eq _ _ _ _ _ diag_injOn hr

/-- **Exactly three dimensions of differences stay inactive through the thirteen consecutive
partial rounds.** -/
theorem finrank_partial_inactive :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 13) = 3 :=
  finrank_inactive_eq (by norm_num)

/-- **Some nonzero difference stays inactive through the thirteen consecutive partial rounds**,
since `13 < 16` (`Plonky3.Diag.inactiveSpace_internal_ne_bot`). -/
theorem partial_inactive_ne_bot :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 13 ≠ ⊥ :=
  Plonky3.Diag.inactiveSpace_internal_ne_bot _ _ _ _ _ (by norm_num)

/-- **The middle term of `Plonky3.Diag.activity_with_middle` is zero here.** Whatever window `w`
satisfies its hypothesis, `13 / w = 0`, because such a `w` is at least `16`. -/
theorem partial_window_term_eq_zero {w : ℕ}
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : F) diag) ({0} : Finset (Fin 16)) w = ⊥) :
    13 / w = 0 :=
  Plonky3.Diag.middle_term_eq_zero (by norm_num) htriv

/-- **Some distinct inputs charge no S-box in the partial rounds**, for every round-constant
table. Take a nonzero difference `a` that stays inactive through thirteen consecutive partial
rounds; the first four rounds after the initial layer form a bijection, so some pair of inputs
reaches the states `a` and `0` at round `4`. Their difference then crosses all thirteen partial
rounds without reaching coordinate `0` (`Hades.IsTrail.free_window`). This is a structural
property of thirteen partial rounds at width sixteen, not an attack: such pairs still incur the
`32` charged S-boxes of `activity_general` in the full rounds. -/
theorem exists_pair_partial_free (table : ℕ → State) :
    ∃ x y : State, x ≠ y ∧
      Hades.scheduledWeight (Plonky3.Diag.rounds conditions 13 sbox table)
        (Hades.differenceTrace (Plonky3.Diag.rounds conditions 13 sbox table) (external x)
          (external y))
        4 13 = 0 := by
  set R := Plonky3.Diag.rounds conditions 13 sbox table with hR
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp partial_inactive_ne_bot
  have hbij : Function.Bijective (fun z : State => Hades.execute R (external z) 4) :=
    (Hades.execute_bijective R 4).comp external.bijective
  obtain ⟨x, hx⟩ := hbij.surjective a
  obtain ⟨y, hy⟩ := hbij.surjective 0
  simp only at hx hy
  refine ⟨x, y, ?_, ?_⟩
  · rintro rfl
    exact ha0 (hx.symm.trans hy)
  · have hdiff : Hades.differenceTrace R (external x) (external y) 4 = a := by
      rw [Hades.differenceTrace, hx, hy, sub_zero]
    have hT := Hades.differenceTrace_isTrail R (external x) (external y) (8 + 13)
    have h := hT.free_window internal ({0} : Finset (Fin 16)) 4 13 (by norm_num)
      (fun j hj => Plonky3.Diag.linear_middle conditions 13 hj)
      (fun j hj => Hades.hadesMask_middle 4 13 4 _ hj) (by rw [hdiff]; exact ha)
    exact h.2

/-! ### Activity -/

/-- **Thirty-two charged S-boxes, for every round-constant table.** Two distinct inputs incur at
least `32 + 13 / 16 = 32` charged S-box applications over the `21` rounds; the bound counts only
S-boxes of the full rounds, since the window `16` of `inactive_trivial` gives `13 / 16 = 0` for
the partial rounds. A lower bound; it is not claimed to be attained. -/
theorem activity_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    32 + 13 / 16 ≤ Hades.scheduledWeight (Plonky3.Diag.rounds conditions 13 sbox table)
      (Hades.differenceTrace (Plonky3.Diag.rounds conditions 13 sbox table) (external x)
        (external y)) 0 (8 + 13) :=
  Plonky3.Diag.activity_with_middle conditions m4Primes_ne_zero 13 sbox table inactive_trivial hxy

/-- **Thirty-two charged S-boxes** for the pinned permutation. -/
theorem activity {x y : State} (hxy : x ≠ y) :
    32 + 13 / 16 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 (8 + 13) :=
  activity_general values hxy

/-! ### The independent-key trail bound -/

/-- **Trail bound, for every round-constant table.** In the model with an additional independent
uniform key per round, the number of keys realising a fixed nonzero trail `T`, times
`2^(28 * (32 + 13 / 16))`, is at most the number of all key sequences. Here `u = 6`, and `28` is
the largest `dd` with `6 * 2^dd ≤ p` (`BabyBear.probability_margin` gives `6 * 2^28 ≤ p`;
`Checks.twentyNine_too_large` in `Checks/OpenVMBabyBear.lean` shows that `29` fails). This
concerns one trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 13 sbox table) (8 + 13) T x *
        2 ^ (28 * (32 + 13 / 16))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  Plonky3.Diag.independent_key_probability_with_middle conditions m4Primes_ne_zero 13 sbox table
    sbox_uniform BabyBear.probability_margin inactive_trivial h0 x

/-- **Trail bound for the pinned rounds**, in the same model. The exponent keeps its round
arithmetic; `probability_exponent` evaluates it to `896`. -/
theorem independent_key_probability {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 13) T x * 2 ^ (28 * (32 + 13 / 16))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_probability_general values h0 x

/-- The displayed bound's concrete exponent. -/
theorem probability_exponent : 28 * (32 + 13 / 16) = 896 := by
  decide

end Poseidon2.OpenVMBabyBear

/-! ### The exact ratio and the sharp exponent

`independent_key_probability` charges `28` bits per charged S-box, so `896` bits over the `32`
charged S-boxes. Keeping the ratio `p / 6` exact (`independent_key_probability_exact`) gives `906`
bits (`independent_key_probability_sharp`), since `32 * log2 (p / 6) ≈ 906.3`. The exponent
arithmetic is that of SP1's BabyBear instance and is reused from it
(`BabyBear.sharp_exponent_bound`). The `_general` forms state the same for every round-constant
table. The sample space is the same: one trail, an additional independent uniform key per
round. -/

namespace Poseidon2.OpenVMBabyBear

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^(32 + 13 / 16) = p^32` (`p = modulus`), is at most `6^32` times
the number of all key sequences. Here `u = 6` (`BabyBear.sbox_uniform`), and the `32` charged
S-boxes are counted as in `activity_general`. This concerns one trail in that model only: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 13 sbox table) (8 + 13) T x
        * modulus ^ (32 + 13 / 16)
      ≤ 6 ^ (32 + 13 / 16) * Fintype.card (Fin 16 → F) ^ (8 + 13) := by
  have h := Plonky3.Diag.independent_key_probability_with_middle_exact conditions
    m4Primes_ne_zero 13 sbox table sbox_uniform inactive_trivial h0 x
  rw [field_card] at h
  exact h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * p^32 ≤ 6^32 * |F^16|^(8 + 13)`. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 13) T x * modulus ^ (32 + 13 / 16)
      ≤ 6 ^ (32 + 13 / 16) * Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_probability_exact_general values h0 x

/-- `2^906 * 6^32 ≤ p^32`, with the exponent `32` written `32 + 13 / 16`: this is
`BabyBear.sharp_exponent_bound`, whose exponent `(4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2` is also
`32`. `Checks/OpenVMBabyBear.lean` shows that `2^907 * 6^32 ≤ p^32` fails, so `906` is the largest
such exponent. -/
theorem sharp_exponent_bound : 2 ^ 906 * 6 ^ (32 + 13 / 16) ≤ modulus ^ (32 + 13 / 16) := by
  have h := BabyBear.sharp_exponent_bound
  rwa [show (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 = 32 + 13 / 16 by norm_num] at h

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^906`, is at most
the number of all key sequences. It follows from `independent_key_probability_exact_general` and
`sharp_exponent_bound`; `906` is the largest exponent that this arithmetic gives. This concerns
one trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 13 sbox table) (8 + 13) T x * 2 ^ 906
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  Hades.mul_le_of_ratio (independent_key_probability_exact_general table h0 x)
    sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model: for every
nonzero trail `T`, `keyCount * 2^906 ≤ |F^16|^(8 + 13)`. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 13) T x * 2 ^ 906 ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_probability_sharp_general values h0 x

end Poseidon2.OpenVMBabyBear

/-! ### The independent-key differential bound

The trail bounds above concern one trail. `independent_key_differential_exact` bounds a
differential, the sum over all trails from a nonzero input difference `a` to an output difference
`b`, in the same model with an additional independent uniform key per round
(`Plonky3.Diag.independent_key_differential_exact`). It charges `7` S-boxes of the first two full
rounds, one fewer than the branch number `8`, at the ratio `p / 6` each; the other rounds are not
charged. Since `7 * log2 (p / 6) ≈ 198.3`, the sharp exponent is `198`
(`independent_key_differential_sharp`, with `BabyBear.differential_sharp_exponent_bound`). The
`_general` forms state the same for every round-constant table. Nothing here concerns the
permutation with its fixed constants. -/

namespace Poseidon2.OpenVMBabyBear

/-- **Differential bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero input difference `a`, every output
difference `b` and every input `x`, the number of key sequences under which `(x, x + a)` has output
difference `b` after the `21` rounds, times `p^7` (`p = modulus`), is at most `6^7` times the
number of all key sequences. Here `u = 6` (`BabyBear.sbox_uniform`). This concerns the
key-averaged differential only: not the permutation with its fixed constants, and not any one
key. -/
theorem independent_key_differential_exact_general (table : ℕ → State) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.Diag.rounds conditions 13 sbox table) (8 + 13) a b x * modulus ^ 7
      ≤ 6 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 13) := by
  have h := Plonky3.Diag.independent_key_differential_exact conditions m4Primes_ne_zero 13 sbox
    table sbox_uniform ha b x
  rw [field_card] at h
  exact h

/-- **Differential bound as an exact ratio** for the pinned rounds, in the same model: for every
nonzero input difference `a`, the key count of the differential `(a, b)` times `p^7` is at most
`6^7` times the number of all key sequences. This concerns the key-averaged differential only:
not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_exact {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 13) a b x * modulus ^ 7
      ≤ 6 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_differential_exact_general values ha b x

/-- **Differential bound with the sharp exponent, for every round-constant table**, in the same
model: for every nonzero input difference `a`, the key count of the differential `(a, b)`, times
`2^198`, is at most the number of all key sequences. It follows from
`independent_key_differential_exact_general` and `BabyBear.differential_sharp_exponent_bound`
(`2^198 * 6^7 ≤ p^7`); `198` is the largest exponent that this arithmetic gives. This concerns the
key-averaged differential only: not the permutation with its fixed constants, and not any one
key. -/
theorem independent_key_differential_sharp_general (table : ℕ → State) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.Diag.rounds conditions 13 sbox table) (8 + 13) a b x * 2 ^ 198
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  Hades.mul_le_of_ratio (independent_key_differential_exact_general table ha b x)
    BabyBear.differential_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Differential bound with the sharp exponent** for the pinned rounds, in the same model: for
every nonzero input difference `a`, the key count of the differential `(a, b)`, times `2^198`, is
at most the number of all key sequences. This concerns the key-averaged differential only: not
the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_sharp {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 13) a b x * 2 ^ 198 ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_differential_sharp_general values ha b x

end Poseidon2.OpenVMBabyBear
