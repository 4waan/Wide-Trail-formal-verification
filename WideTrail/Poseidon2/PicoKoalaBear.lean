/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.KoalaBear

/-!
# A certificate for the Pico v3.2.0 KoalaBear Poseidon2 permutation of width sixteen

Pico `v3.2.0` (`brevis-network/pico`, workspace version `3.2.0`, `Cargo.toml:7-8`) uses the
permutation `default_koalabear_poseidon2_16()` of `p3-koala-bear`. `KoalaBear::permutation()`
returns it, with `Perm = Poseidon2KoalaBear<PERMUTATION_WIDTH>` and `PERMUTATION_WIDTH = 16`, and
the AIR gadget's round constants are its three tables (`vm/src/machine/field.rs:53-67`, the call
at `:58`; `vm/src/primitives/consts.rs:191`). The RISC-V stage hasher
`PaddingFreeSponge<_, 16, 8, 8>` is built on that permutation (`vm/src/primitives/mod.rs:22-32`),
and the MLE stack's Merkle hasher, compressor and transcript use the same function
(`mle-core/src/config/koala_bear_poseidon2.rs:37-44`, `:52-58`, `:94-97`, `:135-138`;
`mle-cpu/src/engine.rs:84-86`). All thirteen `p3-*` crates are pinned to the fork
`brevis-network/Plonky3` at `rev = "da6ca12c"` (`Cargo.toml:45-57`), which `Cargo.lock` resolves
to the commit `da6ca12c71912ec213d3c5af68b14509d2099bc3`, crate version `0.5.4`
(`Cargo.lock:3400-3402`, `:3449-3451`, `:3482-3484`). Below, "the fork" means that commit, with
paths relative to its root; each fork file cited here was compared outside Lean with the same
file of the crates.io crates `p3-koala-bear`, `p3-poseidon2`, `p3-monty-31` and `p3-field`
`0.5.4`, and they are byte-identical.

This file instantiates the diagonal-generic model `Plonky3.Diag` of
`WideTrail.Poseidon2.Plonky3` with that permutation and discharges every hypothesis by `decide`,
so the theorems below have no remaining premises. Field, S-box, round numbers, external layer and
round constants coincide with those of SP1 v6.10.0's KoalaBear permutation in
`WideTrail.Poseidon2.KoalaBear`; the internal layer is different. This file reuses that file's
field, S-box and exponent arithmetic, and `Checks/PicoKoalaBear.lean` proves that the two
round-constant tables are equal.

## The pinned parameters

* **Field and S-box.** Those of `WideTrail.Poseidon2.KoalaBear`, reused: `F = ZMod modulus` with
  `modulus = 0x7f000001 = 2^31 - 2^24 + 1` (fork `koala-bear/src/koala_bear.rs:21`), prime by
  the Lucas certificate of `WideTrail.Poseidon2.KoalaBearPrimality`, and `KoalaBear.sbox`,
  `x ↦ x^3` with inverse `x ↦ x^1420470955`. The degree is `KOALABEAR_S_BOX_DEGREE = 3`
  (`koala-bear/src/poseidon1.rs:27`), the parameter `D` of `Poseidon2KoalaBear`
  (`koala-bear/src/poseidon2.rs:67-73`), and Pico's own `KOALABEAR_S_BOX_DEGREE` is also `3`
  (`vm/src/primitives/consts.rs:209`); the code's cube root is `exp_1420470955`
  (`koala-bear/src/koala_bear.rs:57-64`). The S-box has differential uniformity at most `2`
  (`KoalaBear.sbox_uniform`).
* **Rounds.** `permute_mut` runs `permute_state_initial`, `permute_state` and
  `permute_state_terminal` (`poseidon2/src/lib.rs:118-122`). The first applies
  `mds_light_permutation` (`poseidon2/src/external.rs:321-336`, the call at `:332`) and then one
  full round per row of `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL` (four rows,
  `koala-bear/src/poseidon2.rs:91`; loop at `poseidon2/src/external.rs:299-305`); the second runs
  one partial round per entry of `KOALABEAR_POSEIDON2_RC_16_INTERNAL` (twenty,
  `koala-bear/src/poseidon2.rs:155`; loop at `monty-31/src/poseidon2.rs:76-85`), with the
  constant and the S-box on `state[0]` only (`:78-79`); the third runs one full round per row of
  `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL` (four, `koala-bear/src/poseidon2.rs:123`). These
  counts agree with `KOALABEAR_POSEIDON2_HALF_FULL_ROUNDS = 4` and
  `KOALABEAR_POSEIDON2_PARTIAL_ROUNDS_16 = 20` (`:37`, `:52`) and with Pico's `KoalaBearConfig`
  (`vm/src/primitives/consts.rs:199-211`). The doc comment of the second constant (`:39-51`)
  first derives `R_P = 85` from an interpolation bound and then states that the round-number
  script gives `20`; the code uses `20`. A full round adds the row and cubes every coordinate
  (`add_rc_and_sbox_generic`, `poseidon2/src/generic.rs:24-30`), then applies the external layer.
* **External layer.** `external` is `Plonky3.external`, i.e. `circ(2 M4, M4, M4, M4)` with
  `M4 = circ(2, 3, 1, 1)`. The fork's `mds_light_permutation` (`poseidon2/src/external.rs:113-159`,
  width-sixteen branch `:135-153`) with `MDSMat4` (`apply_mat4`, `:60-74`; passed at
  `monty-31/src/poseidon2.rs:94-111`) performs the steps that `Plonky3.mdsLight` transcribes:
  `M4` on each block of four, then `sums[i % 4]` added to coordinate `i`. So
  `external_eq_mdsLight` identifies the layer with the code's function.
* **Internal layer.** `internal x i = d_i x_i + ∑_j x_j`, with no scale factor, for the diagonal
  `d = (-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24)`
  (`koala-bear/src/poseidon2.rs:278`, and the module comment at `:11`). The code first sets
  `state[0] = part_sum - state[0]`, where `part_sum` is the sum of `state[1..]`
  (`monty-31/src/poseidon2.rs:80-83`), which gives `d_0 = -2`, and then runs
  `internal_layer_mat_mul` with the full sum (`koala-bear/src/poseidon2.rs:276-301`).
  `internalCode` transcribes these statements over `F`, reading `double` as `x + x`, `halve` as
  `x / 2` and `div_2exp_u64(k)` as `x / 2^k`, and `internalCode_eq` proves that it is `internal`.
  That reading of the Montgomery code is not derived in Lean: on representatives, `halve` is
  `halve_u32` (`monty-31/src/monty_31.rs:201-204`, `src/utils.rs:92-97`) and `div_2exp_u64(k)`
  for `k ≤ 32` is `monty_reduce(value << (32 - k))` (`monty_31.rs:219-233`), which are
  multiplications of the field element by `2^{-1}` and `2^{-k}`; every operation of
  `internal_layer_mat_mul` is a field operation, so there is no factor `R^{-1}`. This differs
  from SP1's layer `R^{-1} (diag(-2, 1, 2, 4, …, 2^13, 2^15) + J)`. The trait comment at
  `monty-31/src/poseidon2.rs:16-17` ("monty form is `1 + Diag(vec)`", entries "small powers of
  `2`") does not describe this diagonal; the code lines are what is modelled. The known-answer
  test of `Checks/PicoKoalaBear.lean` exercises the layer end to end and fails with the factor
  `R^{-1}`.
* **The diagonal in `F`.** `diag` lists the canonical representatives; `diag_spec` checks
  `2^{k_i} d_i = n_i` with the numerators `diagNumerator` and exponents `diagShift` of the
  fractions above, so `d_i = n_i / 2^{k_i}` (`diag_eq_div`). Since `127 * 2^24 = p - 1`, the
  entries `1/2^24` and `-1/2^24` are `-127` and `127`.
* **Field conditions.** `conditions : Plonky3.Diag.Conditions diag 1` holds by `decide`: `35 ≠ 0`,
  `d_i ≠ 0` from the table `diagInv` of inverses (`diag_mul_inv`), the Sherman–Morrison condition
  from `1 + ∑ 1/d_i = -14` (`one_add_sum_inv_eq`; the same value over `ℚ`), and the scale `1`.
* **Round constants.** `externalInitial`, `internalConstants` and `externalFinal` are
  `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL` (`koala-bear/src/poseidon2.rs:91-113`),
  `KOALABEAR_POSEIDON2_RC_16_INTERNAL` (`:155-159`) and `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`
  (`:123-145`), copied with the hexadecimal literals of the source. The code maps each literal
  through `KoalaBear::new_2d_array` or `new_array` (`monty-31/src/monty_31.rs:88-111`), that is
  `MontyField31::new` (`:51-65`), which stores `to_monty` of it (`src/utils.rs:7-9`); so the field
  element is the literal mod `p`, and every literal is below `p`. `default_koalabear_poseidon2_16`
  (`koala-bear/src/poseidon2.rs:162-170`) passes the two external tables to
  `ExternalLayerConstants::new(initial, final)` and the internal one to the internal layer.
  `externalConstants` lists the eight external rows in that order, and
  `values = Plonky3.roundValues 20 externalConstants internalConstants` (`values_eq_roundValues`)
  is the `28`-row table whose partial rows are `(c, 0, …, 0)` (`partial_constants_zero`), the
  layout in which Pico's CUDA trace generation ships the constants
  (`vm/src/chips/gadgets/poseidon2/constants.rs:28-49`). The literals were re-extracted from the
  fork source outside Lean and compared entry by entry with this file. Upstream `p3-koala-bear`
  `0.5.0` to `0.8.0` carry the same three tables; `0.4.3`'s `default_koalabear_poseidon2_16` has
  other internal and final tables (also compared outside Lean). `Checks/PicoKoalaBear.lean` shows
  that `values` is, entry by entry, SP1 v6.10.0's table `KoalaBear.values` (`values_eq_sp1`), so
  this permutation and SP1's differ only in the internal layer.

## Results

Each result holds with no remaining premise.

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
* `activity`, `activity_general`: two distinct inputs incur at least `33` charged S-box
  applications, `32` in the full rounds and `20 / 16 = 1` in the partial rounds.
* `independent_key_probability`, `independent_key_probability_general`: for every nonzero trail
  `T`, `keyCount * 2^(29 * (32 + 20 / 16)) ≤ |F^16|^(8 + 20)`; the exponent is `957`
  (`KoalaBear.probability_exponent`).
* `independent_key_probability_exact`, `independent_key_probability_sharp`, and their `_general`
  forms: for every nonzero trail `T`, `keyCount * p^33 ≤ 2^33 * |F^16|^(8 + 20)` with
  `33 = 32 + 20 / 16`, and `keyCount * 2^989 ≤ |F^16|^(8 + 20)`. `989` is the largest exponent
  this arithmetic gives (`KoalaBear.sharp_exponent_bound`; `Checks/PicoKoalaBear.lean` shows that
  `990` fails).
* `independent_key_differential_exact`, `independent_key_differential_sharp`, and their
  `_general` forms: for every nonzero input difference `a`, every output difference `b` and every
  input `x`, the key count of the differential `(a, b)` over the `28` rounds that follow the
  initial external layer satisfies `diffKeyCount * p^7 ≤ 2^7 * |F^16|^28` and
  `diffKeyCount * 2^209 ≤ |F^16|^28`. Only `7` S-boxes of the first two full rounds are charged,
  one fewer than the branch number `8`; `209` is the largest exponent this arithmetic gives
  (`KoalaBear.differential_sharp_exponent_bound`; `Checks/PicoKoalaBear.lean` shows that `210`
  fails).

The counts and exponents are those of SP1's KoalaBear instance: they depend only on `p`, `u = 2`,
the branch number `8`, the window `16` and the round numbers, which the two instances share.
`Checks/PicoKoalaBear.lean` holds the known-answer test against the expected output of Plonky3's
`test_default_koalabear_poseidon2_width_16`, which uses the deployed constants.

## What is not claimed

The activity counts are lower bounds on charged S-box applications for actual input pairs; they
are not claimed to be attained. The trail-probability statements concern one trail in the model
with an additional independent uniform key per round. The differential statements
(`independent_key_differential_*`) bound the key-averaged differential of the rounds after the
initial external layer, in the same model, and charge only `B - 1 = 7` S-boxes of the first two
full rounds. None of these is a statement about the permutation with its fixed constants, or about
any one key. Nothing is said about subspace-trail resistance beyond the inactive-space statements
here, about algebraic attacks, about the sponge, duplex and compression constructions built on the
permutation, about Pico's recursion chips (which a Pico comment says use this permutation,
`mle-core/src/config/koala_bear_poseidon2.rs:39-40`; not checked), or about equivalence with the
Rust code or Pico's AIR beyond the transcriptions stated in `WideTrail.Poseidon2.Plonky3` and in
this file and the known-answer tests of `Checks/PicoKoalaBear.lean`. The AVX2, AVX-512 and NEON code
paths, which have their own internal-layer code, are not modelled. The model works with field
elements, not with the Montgomery representatives the code stores.
-/

set_option autoImplicit false

open Poseidon2.KoalaBear (F State modulus field_card sbox sbox_uniform m4Primes_ne_zero)

namespace Poseidon2.PicoKoalaBear

/-! ### The internal diagonal -/

/-- The internal diagonal `V = (-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8,
-1/8, -1/16, -1/2^24)` (fork `koala-bear/src/poseidon2.rs:278`; `d_0 = -2` from
`monty-31/src/poseidon2.rs:82`), entry by entry as canonical representatives in `F`. `diag_spec`
checks each entry against its fraction. -/
def diag : Fin 16 → F :=
  ![2130706431, 1, 2, 1065353217, 3, 4, 1065353216, 2130706430, 2130706429, 2122383361,
    1864368129, 2130706306, 8323072, 266338304, 133169152, 127]

/-- The numerators `n_i` of the diagonal entries `d_i = n_i / 2^{k_i}`. -/
def diagNumerator : Fin 16 → F := ![-2, 1, 2, 1, 3, 4, -1, -3, -4, 1, 1, 1, -1, -1, -1, -1]

/-- The exponents `k_i` of the denominators of the diagonal entries `d_i = n_i / 2^{k_i}`. -/
def diagShift : Fin 16 → ℕ := ![0, 0, 0, 1, 0, 0, 1, 0, 0, 8, 3, 24, 8, 3, 4, 24]

/-- **The diagonal entries are the code's fractions**: `2^{k_i} d_i = n_i` in `F` for every `i`,
by `decide`. -/
theorem diag_spec : ∀ i, 2 ^ diagShift i * diag i = diagNumerator i := by
  decide

/-- `d_i = n_i / 2^{k_i}` in `F`, from `diag_spec` and `2 ≠ 0`. -/
theorem diag_eq_div (i : Fin 16) : diag i = diagNumerator i / 2 ^ diagShift i := by
  rw [eq_div_iff (pow_ne_zero _ (by decide : (2 : F) ≠ 0)), mul_comm]
  exact diag_spec i

/-- The inverses `1/d_i = (-1/2, 1, 1/2, 2, 1/3, 1/4, -2, -1/3, -1/4, 2^8, 8, 2^24, -2^8, -8, -16,
-2^24)`, as canonical representatives in `F`. -/
def diagInv : Fin 16 → F :=
  ![1065353216, 1, 1065353217, 2, 710235478, 1598029825, 2130706431, 1420470955, 532676608, 256,
    8, 16777216, 2130706177, 2130706425, 2130706417, 2113929217]

theorem diag_mul_inv : ∀ i, diag i * diagInv i = 1 := by
  decide

/-- Every diagonal entry is nonzero. -/
theorem diag_ne_zero : ∀ i, diag i ≠ 0 :=
  Poseidon2.ne_zero_of_mul_eq_one diag_mul_inv

theorem one_add_sum_diagInv : 1 + ∑ i, diagInv i = -14 := by
  decide

/-- **The Sherman–Morrison quantity** `1 + ∑ 1/d_i` is `-14` in `F`, as it is over `ℚ`. -/
theorem one_add_sum_inv_eq : 1 + ∑ i, (diag i)⁻¹ = -14 := by
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

/-- The external layer is `mds_light_permutation` (fork `poseidon2/src/external.rs:113-159`). -/
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

/-- The code's internal layer, statement by statement, over `F`: `state[0] = part_sum - state[0]`
with `part_sum` the sum of `state[1..]` (`monty-31/src/poseidon2.rs:80-83`), then
`internal_layer_mat_mul` with the full sum `sum` (`koala-bear/src/poseidon2.rs:279-300`), reading
`double` as `x + x`, `halve` as `x / 2` and `div_2exp_u64(k)` as `x / 2^k`. -/
def internalCode (x : State) : State :=
  let partSum := x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 + x 10 + x 11 + x 12 + x 13 +
    x 14 + x 15
  let sum := partSum + x 0
  ![partSum - x 0, x 1 + sum, (x 2 + x 2) + sum, x 3 / 2 + sum, sum + (x 4 + x 4) + x 4,
    sum + ((x 5 + x 5) + (x 5 + x 5)), sum - x 6 / 2, sum - ((x 7 + x 7) + x 7),
    sum - ((x 8 + x 8) + (x 8 + x 8)), x 9 / 2 ^ 8 + sum, x 10 / 2 ^ 3 + sum, x 11 / 2 ^ 24 + sum,
    sum - x 12 / 2 ^ 8, sum - x 13 / 2 ^ 3, sum - x 14 / 2 ^ 4, sum - x 15 / 2 ^ 24]

/-- **The code's statements compute `internal`**: the transcription `internalCode` is
`x ↦ (diag d + J) x` with the diagonal `diag`. -/
theorem internalCode_eq (x : State) : internalCode x = internal x := by
  funext i
  rw [internal_apply, diag_eq_div]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i <;>
    simp [internalCode, diagNumerator, diagShift] <;> ring

/-! ### Round constants -/

/-- `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL` (fork `koala-bear/src/poseidon2.rs:91-113`), the
constants of the four initial full rounds, with the hexadecimal literals of the source. -/
def externalInitial : Fin 4 → State :=
  ![![0x7ee56a48, 0x11367045, 0x12e41941, 0x7ebbc12b, 0x1970b7d5, 0x662b60e8, 0x3e4990c6,
      0x679f91f5, 0x350813bb, 0x00874ad4, 0x28a0081a, 0x18fa5872, 0x5f25b071, 0x5e5d5998,
      0x5e6fd3e7, 0x5b2e2660],
    ![0x6f1837bf, 0x3fe6182b, 0x1edd7ac5, 0x57470d00, 0x43d486d5, 0x1982c70f, 0x0ea53af9,
      0x61d6165b, 0x51639c00, 0x2dec352c, 0x2950e531, 0x2d2cb947, 0x08256cef, 0x1a0109f6,
      0x1f51faf3, 0x5cef1c62],
    ![0x3d65e50e, 0x33d91626, 0x133d5a1e, 0x0ff49b0d, 0x38900cd1, 0x2c22cc3f, 0x28852bb2,
      0x06c65a02, 0x7b2cf7bc, 0x68016e1a, 0x15e16bc0, 0x5248149a, 0x6dd212a0, 0x18d6830a,
      0x5001be82, 0x64dac34e],
    ![0x5902b287, 0x426583a0, 0x0c921632, 0x3fe028a5, 0x245f8e49, 0x43bb297e, 0x7873dbd9,
      0x3cc987df, 0x286bb4ce, 0x640a8dcd, 0x512a8e36, 0x03a4cf55, 0x481837a2, 0x03d6da84,
      0x73726ac7, 0x760e7fdf]]

/-- `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL` (fork `koala-bear/src/poseidon2.rs:123-145`), the
constants of the four terminal full rounds, with the hexadecimal literals of the source. -/
def externalFinal : Fin 4 → State :=
  ![![0x43e7dc24, 0x259a5d61, 0x27e85a3b, 0x1b9133fa, 0x343e5628, 0x485cd4c2, 0x16e269f5,
      0x165b60c6, 0x25f683d9, 0x124f81f9, 0x174331f9, 0x77344dc5, 0x5a821dba, 0x5fc4177f,
      0x54153bf5, 0x5e3f1194],
    ![0x3bdbf191, 0x088c84a3, 0x68256c9b, 0x3c90bbc6, 0x6846166a, 0x03f4238d, 0x463335fb,
      0x5e3d3551, 0x6e59ae6f, 0x32d06cc0, 0x596293f3, 0x6c87edb2, 0x08fc60b5, 0x34bcca80,
      0x24f007f3, 0x62731c6f],
    ![0x1e1db6c6, 0x0ca409bb, 0x585c1e78, 0x56e94edc, 0x16d22734, 0x18e11467, 0x7b2c3730,
      0x770075e4, 0x35d1b18c, 0x22be3db5, 0x4fb1fbb7, 0x477cb3ed, 0x7d5311c6, 0x5b62ae7d,
      0x559c5fa8, 0x77f15048],
    ![0x3211570b, 0x490fef6a, 0x77ec311f, 0x2247171b, 0x4e0ac711, 0x2edf69c9, 0x3b5a8850,
      0x65809421, 0x5619b4aa, 0x362019a7, 0x6bf9d4ed, 0x5b413dff, 0x617e181e, 0x5e7ab57b,
      0x33ad7833, 0x3466c7ca]]

/-- `KOALABEAR_POSEIDON2_RC_16_INTERNAL` (fork `koala-bear/src/poseidon2.rs:155-159`), the twenty
partial-round constants, added to `state[0]`, with the hexadecimal literals of the source. -/
def internalConstants : Fin 20 → F :=
  ![0x54dfeb5d, 0x7d40afd6, 0x722cb316, 0x106a4573, 0x45a7ccdb, 0x44061375, 0x154077a5,
    0x45744faa, 0x4eb5e5ee, 0x3794e83f, 0x47c7093c, 0x5694903c, 0x69cb6299, 0x373df84c,
    0x46a0df58, 0x46b8758a, 0x3241ebcb, 0x0b09d233, 0x1af42357, 0x1e66cec2]

/-- The eight external rows in the order the full-round loops read them: `externalInitial`, then
`externalFinal` (`ExternalLayerConstants::new(initial, final)`,
`koala-bear/src/poseidon2.rs:162-170`). -/
def externalConstants (r : Fin 8) : State :=
  if h : r.val < 4 then externalInitial ⟨r.val, h⟩ else externalFinal ⟨r.val - 4, by omega⟩

/-- The constant table indexed by round: rows `0-3` are `externalInitial`, row `4 + j` is
`(internalConstants j, 0, …, 0)` for `j < 20`, rows `24-27` are `externalFinal`, and rows past
`27` are zero. -/
def values : ℕ → State := Plonky3.roundValues 20 externalConstants internalConstants

/-- **The table is the code's three arrays**, by definition. -/
theorem values_eq_roundValues :
    values = Plonky3.roundValues 20 externalConstants internalConstants :=
  rfl

/-- Partial rows add their constant only at the S-box coordinate, by `decide`. -/
theorem partial_constants_zero :
    ∀ n : Fin 20, ∀ i : Fin 16, i ≠ 0 → values (4 + n.val) i = 0 := by
  decide

theorem partialRowsAtZero : Plonky3.PartialRowsAtZero 20 values :=
  fun j hj i hi => partial_constants_zero ⟨j, hj⟩ i hi

/-! ### The permutation -/

/-- The `28` rounds: four full, twenty partial with the S-box on coordinate `0`, four full. -/
def rounds : ℕ → Hades.RoundSpec (Fin 16) F := Plonky3.Diag.rounds conditions 20 sbox values

/-- **The permutation**, the model of `default_koalabear_poseidon2_16()`: the initial external
layer, then the `28` rounds. -/
def permutation (x : State) : State := Plonky3.Diag.permutation conditions 20 sbox values x

theorem permutation_eq (x : State) : permutation x = Hades.execute rounds (external x) 28 :=
  rfl

theorem permutation_bijective : Function.Bijective permutation :=
  Plonky3.Diag.permutation_bijective conditions 20 sbox values

/-- Bijectivity holds for every round-constant table. -/
theorem permutation_bijective_general (table : ℕ → State) :
    Function.Bijective (Plonky3.Diag.permutation conditions 20 sbox table) :=
  Plonky3.Diag.permutation_bijective conditions 20 sbox table

/-- An initial full round is the code's round (fork `poseidon2/src/external.rs:299-305`) with row
`j` of `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`. -/
theorem rounds_apply_prefix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds j).apply x = external (fun i => sbox (x i + externalInitial ⟨j, hj⟩ i)) := by
  rw [rounds, Plonky3.Diag.rounds_apply_prefix conditions 20 sbox values hj x, values,
    Plonky3.roundValues_prefix 20 _ _ hj]
  simp [externalConstants, hj]
  rfl

/-- **A partial round is the code's round** (fork `monty-31/src/poseidon2.rs:77-84`): add
`internalConstants j` to `state[0]`, apply the S-box to `state[0]` only, then the internal
layer. -/
theorem rounds_apply_partial {j : ℕ} (hj : j < 20) (x : State) :
    (rounds (4 + j)).apply x =
      internal (Function.update x 0 (sbox (x 0 + internalConstants ⟨j, hj⟩))) :=
  Plonky3.Diag.rounds_roundValues_apply_middle conditions 20 sbox _ _ hj x

/-- A terminal full round is the code's round (fork `poseidon2/src/external.rs:299-305`) with row
`j` of `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`. -/
theorem rounds_apply_suffix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds (24 + j)).apply x = external (fun i => sbox (x i + externalFinal ⟨j, hj⟩ i)) := by
  rw [show 24 + j = 4 + 20 + j by omega, rounds,
    Plonky3.Diag.rounds_apply_suffix conditions 20 sbox values hj x, values,
    Plonky3.roundValues_suffix 20 _ _ hj]
  simp [externalConstants]
  rfl

/-! ### The partial rounds -/

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds**, for the
unscaled layer `diag d + J`: the diagonal criterion with `diag_injOn`. -/
theorem inactive_trivial :
    Hades.inactiveSpace (diagPlusOnes (1 : F) diag) ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Plonky3.Diag.inactiveSpace_sixteen_eq_bot_iff.mpr diag_injOn

/-- **The same for the code's internal layer.** -/
theorem internal_inactive_trivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Plonky3.Diag.inactiveSpace_internal_sixteen_eq_bot _ _ _ _ _ diag_injOn

/-- **Exactly `16 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds**, for `r ≤ 16`. For `r = 15` one dimension remains; for `r = 16` none. -/
theorem finrank_inactive_eq {r : ℕ} (hr : r ≤ 16) :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) r) =
      16 - r :=
  Plonky3.Diag.finrank_inactiveSpace_internal_eq _ _ _ _ _ diag_injOn hr

/-! ### Activity -/

/-- **Thirty-three active S-boxes, for every round-constant table.** Two distinct inputs incur at
least `33` charged S-box applications over the `28` rounds: `32` in the full rounds and
`20 / 16 = 1` in the partial rounds. A lower bound; it is not claimed to be attained. -/
theorem activity_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    33 ≤ Hades.scheduledWeight (Plonky3.Diag.rounds conditions 20 sbox table)
      (Hades.differenceTrace (Plonky3.Diag.rounds conditions 20 sbox table) (external x)
        (external y)) 0 28 :=
  Plonky3.Diag.activity_with_middle conditions m4Primes_ne_zero 20 sbox table inactive_trivial hxy

/-- **Thirty-three active S-boxes** for the pinned permutation. -/
theorem activity {x y : State} (hxy : x ≠ y) :
    33 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 28 :=
  activity_general values hxy

/-! ### The independent-key trail bound -/

/-- **Trail bound, for every round-constant table.** In the model with an additional independent
uniform key per round, the number of keys realising a fixed nonzero trail `T`, times
`2^(29 * (32 + 20 / 16))`, is at most the number of all key sequences. Here `u = 2`, and `29` is
the largest `dd` with `2 * 2^dd ≤ p` (`KoalaBear.two_mul_two_pow_le_card`). This concerns one
trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) T x *
        2 ^ (29 * (32 + 20 / 16))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Plonky3.Diag.independent_key_probability_with_middle conditions m4Primes_ne_zero 20 sbox table
    sbox_uniform KoalaBear.two_mul_two_pow_le_card inactive_trivial h0 x

/-- **Trail bound for the pinned rounds**, in the same model. The exponent keeps its round
arithmetic; `KoalaBear.probability_exponent` evaluates it to `957`. -/
theorem independent_key_probability {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * 2 ^ (29 * (32 + 20 / 16))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_general values h0 x

end Poseidon2.PicoKoalaBear

/-! ### The exact ratio and the sharp exponent

`independent_key_probability` charges `29` bits per charged S-box, so `957` bits over the `33`
charged S-boxes. Keeping the ratio `p / 2` exact (`independent_key_probability_exact`) gives `989`
bits (`independent_key_probability_sharp`), since `33 * log2 (p / 2) ≈ 989.6`. The exponent
arithmetic is that of SP1's KoalaBear instance and is reused from it
(`KoalaBear.sharp_exponent_bound`). The `_general` forms state the same for every round-constant
table. The sample space is the same: one trail, an additional independent uniform key per
round. -/

namespace Poseidon2.PicoKoalaBear

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^(32 + 20 / 16) = p^33` (`p = modulus`), is at most `2^33` times
the number of all key sequences. Here `u = 2` (`KoalaBear.sbox_uniform`), and the `33` charged
S-boxes are counted as in `activity_general`. This concerns one trail in that model only: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) T x
        * modulus ^ (32 + 20 / 16)
      ≤ 2 ^ (32 + 20 / 16) * Fintype.card (Fin 16 → F) ^ (8 + 20) := by
  have h := Plonky3.Diag.independent_key_probability_with_middle_exact conditions
    m4Primes_ne_zero 20 sbox table sbox_uniform inactive_trivial h0 x
  rw [field_card] at h
  exact h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * p^33 ≤ 2^33 * |F^16|^(8 + 20)`. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * modulus ^ (32 + 20 / 16)
      ≤ 2 ^ (32 + 20 / 16) * Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_exact_general values h0 x

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^989`, is at most
the number of all key sequences. It follows from `independent_key_probability_exact_general` and
`KoalaBear.sharp_exponent_bound` (`2^989 * 2^33 ≤ p^33`); `989` is the largest exponent that this
arithmetic gives. This concerns one trail in that model only: not the permutation with its fixed
constants, and not a differential. -/
theorem independent_key_probability_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) T x * 2 ^ 989
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Hades.mul_le_of_ratio (independent_key_probability_exact_general table h0 x)
    KoalaBear.sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model: for every
nonzero trail `T`, `keyCount * 2^989 ≤ |F^16|^(8 + 20)`. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * 2 ^ 989 ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_sharp_general values h0 x

end Poseidon2.PicoKoalaBear

/-! ### The independent-key differential bound

The trail bounds above concern one trail. `independent_key_differential_exact` bounds a
differential, the sum over all trails from a nonzero input difference `a` to an output difference
`b`, in the same model with an additional independent uniform key per round
(`Plonky3.Diag.independent_key_differential_exact`). It charges `7` S-boxes of the first two full
rounds, one fewer than the branch number `8`, at the ratio `p / 2` each; the other rounds are not
charged. Since `7 * log2 (p / 2) ≈ 209.9`, the sharp exponent is `209`
(`independent_key_differential_sharp`, with `KoalaBear.differential_sharp_exponent_bound`). The
`_general` forms state the same for every round-constant table. Nothing here concerns the
permutation with its fixed constants. -/

namespace Poseidon2.PicoKoalaBear

/-- **Differential bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero input difference `a`, every output
difference `b` and every input `x`, the number of key sequences under which `(x, x + a)` has output
difference `b` after the `28` rounds, times `p^7` (`p = modulus`), is at most `2^7` times the
number of all key sequences. Here `u = 2` (`KoalaBear.sbox_uniform`). This concerns the
key-averaged differential only: not the permutation with its fixed constants, and not any one
key. -/
theorem independent_key_differential_exact_general (table : ℕ → State) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) a b x * modulus ^ 7
      ≤ 2 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 20) := by
  have h := Plonky3.Diag.independent_key_differential_exact conditions m4Primes_ne_zero 20 sbox
    table sbox_uniform ha b x
  rw [field_card] at h
  exact h

/-- **Differential bound as an exact ratio** for the pinned rounds, in the same model: for every
nonzero input difference `a`, the key count of the differential `(a, b)` times `p^7` is at most
`2^7` times the number of all key sequences. This concerns the key-averaged differential only:
not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_exact {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 20) a b x * modulus ^ 7
      ≤ 2 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_differential_exact_general values ha b x

/-- **Differential bound with the sharp exponent, for every round-constant table**, in the same
model: for every nonzero input difference `a`, the key count of the differential `(a, b)`, times
`2^209`, is at most the number of all key sequences. It follows from
`independent_key_differential_exact_general` and `KoalaBear.differential_sharp_exponent_bound`
(`2^209 * 2^7 ≤ p^7`); `209` is the largest exponent that this arithmetic gives. This concerns the
key-averaged differential only: not the permutation with its fixed constants, and not any one
key. -/
theorem independent_key_differential_sharp_general (table : ℕ → State) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) a b x * 2 ^ 209
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Hades.mul_le_of_ratio (independent_key_differential_exact_general table ha b x)
    KoalaBear.differential_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Differential bound with the sharp exponent** for the pinned rounds, in the same model: for
every nonzero input difference `a`, the key count of the differential `(a, b)`, times `2^209`, is
at most the number of all key sequences. This concerns the key-averaged differential only: not
the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_sharp {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 20) a b x * 2 ^ 209 ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_differential_sharp_general values ha b x

end Poseidon2.PicoKoalaBear
