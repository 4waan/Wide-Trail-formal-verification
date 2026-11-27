/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.OpenVMBabyBear
import WideTrail.Poseidon2.Plonky3Execution
import WideTrail.Poseidon2.Checks.Plonky3KAT

/-!
# Checks for the OpenVM v2.1.0 BabyBear certificate

`WideTrail.Poseidon2.OpenVMBabyBear` instantiates the diagonal-generic Plonky3 model with the
permutation `default_babybear_poseidon2_16()` of `p3-baby-bear` `0.4.3`, which OpenVM v2.1.0
uses. The checks below test that instantiation against Plonky3's test vectors, record which
readings of the code they rule out, and show that the uniformity `6`, the per-S-box exponent
`28`, the branch number `8`, the window `16` and the exponents used by the bounds cannot be
improved. Every finite check is kernel `decide`. The whole-permutation checks run on the runner
`Plonky3.Diag.permutationDense` of `WideTrail.Poseidon2.Plonky3Execution` (diagonal `diagDense`,
scale `1`), and `Plonky3.Diag.permutation_eq_of_dense` and its companions transfer the computed
values to the specification.

## Known-answer tests

* **The deployed permutation** (`upstream_kat`). `test_default_babybear_poseidon2_width_16`
  (Plonky3 `v0.8.0`, commit `a21e3ed42905040ad49c519e402f018381c12d0c`,
  `baby-bear/src/poseidon2.rs:598-616`) builds `default_babybear_poseidon2_16()` (`:612`) and
  asserts its output on a fixed input (input `:600-604`, expected output `:606-610`). That file
  has SHA-256 `94dd94e267e66922104010624f42ba7836805dc2fafe7482d684cd2e042a7327` and is
  byte-identical to `src/poseidon2.rs` of the crates.io crate `p3-baby-bear` `0.8.0`. Its tables
  `BABYBEAR_POSEIDON2_RC_16_*` (`:111-177`) are, value for value, `p3-baby-bear` `0.4.3`'s
  `BABYBEAR_RC16_*` and OpenVM's selection from `RC16` (compared outside Lean), so this is a
  known-answer test of the deployed permutation with the deployed constants:
  `permutation input = expected`, with input and output copied from the source. The test exists
  only in `v0.8.0`, not in the `0.4.3` that OpenVM pins. Its applicability rests on the equal
  constants and on the permutation code being the same in substance from `0.4.3` to `0.8.0`:
  `p3-poseidon2`'s `lib.rs`, `external.rs`, `internal.rs` and `generic.rs`, `p3-monty-31`'s
  `poseidon2.rs` and the BabyBear `internal_layer_mat_mul` were compared outside Lean, and the
  differences are `clone` renamed to `dup`, width-32 support, constant getters returning slices,
  new assertions in the constructor and rewrites of the same operations (`chunks_exact_mut` as
  `as_chunks_mut`; `x + x` as `x.double()` in the HorizenLabs `M4`, which this permutation does
  not use). Both arrays pass through `BabyBear::new_array` (`to_monty` of the literal) and
  `assert_eq!` compares field elements, so the literals are canonical values. No vector for these
  constants was found in OpenVM v2.1.0 or in `p3-baby-bear` `0.4.3`; OpenVM's tree was not
  searched exhaustively.
* **A second constant table** (`rng_kat`). `test_poseidon2_width_16_random` (`p3-baby-bear`
  `0.4.3` `src/poseidon2.rs:314-333`, input `:316-320`, expected output `:322-326`; the same
  vector in Plonky3 `v0.8.0` `baby-bear/src/poseidon2.rs:511-530`) runs the same layers, S-box and
  round numbers with constants drawn by
  `Poseidon2BabyBear::new_from_rng_128(&mut Xoroshiro128Plus::seed_from_u64(1))` (`:328-329`).
  For a 31-bit prime and `(16, 7)`, `poseidon2_round_numbers_128` returns `(8, 13)`
  (`p3-poseidon2` `0.4.3` `src/round_numbers.rs:50`); `new_from_rng` (`src/lib.rs:66-74`) draws
  four initial rows, four terminal rows (`src/external.rs:199-213`) and then thirteen scalars,
  and each sample is a raw Montgomery representative `next_u32() >> 1`, redrawn while it is at
  least `p` (`p3-monty-31` `0.4.3` `src/monty_31.rs:145-156`), so its field element is the sample
  times `R^{-1}`. These are the sampler, the drawing order and the generator of the
  `0.2.3-succinct` test that `Checks/Plonky3KAT.lean` reproduces, and an emulation run outside
  Lean (of `rand_xoshiro` `0.7.0`, `rand` `0.9.4` and this sampler) drew exactly its raw tables
  `BabyBear.Plonky3KAT.extRaw` and `intRaw`; so this file reuses its table
  `BabyBear.Plonky3KAT.katValues`. That the emulation matches the Rust generator is not checked
  directly; the evidence is that the model reproduces the expected outputs of both tests, which
  come from the sources. This test does not exercise the deployed constants.
* **Regression values** (`permutation_zero`, `permutation_range`). `permutation 0` and
  `permutation (0, 1, …, 15)` were computed outside Lean by a model of the code that reproduces
  the two vectors above. They do not come from OpenVM or Plonky3 and serve only to detect
  changes.

## Negative controls

On the input of `upstream_kat`, the expected output is not reproduced with the deployed
constants and SP1 `5.2.4`'s internal layer `R^{-1} (diag(-2, 1, 2, 4, …, 2^13, 2^15) + J)`
(`kat_fails_sp1_internal`); with SP1's diagonal and no factor (`kat_fails_sp1Diag`); with
OpenVM's diagonal and the factor `R^{-1}` (`kat_fails_montyInverse`); without the initial
external layer (`kat_fails_skip_initial`); or with the literals of the three tables read as
Montgomery representatives, that is times `R^{-1}` (`kat_fails_monty_constants`). So the vector
rules out each of these five alternatives to the model.

## Exactness and cross-checks

* `sbox_not_uniform_five`: six solutions of `(x + 1)^7 - x^7 = 1346933384`, so `u = 6` is least.
  `twentyNine_too_large`: `6 * 2^29 > p`, so `28` is the largest `dd` with `6 * 2^dd ≤ p`.
* `external_branchWitness`, `external_not_branch_nine`: a difference of weight four with an image
  of weight four, so the branch number of the external layer is exactly `8`.
* `finrank_inactive_fifteen`, `inactive_fifteen_ne_bot`: a one-dimensional space of differences
  stays inactive through fifteen consecutive partial rounds (`finrank_inactive_eq` at `r = 15`),
  so the window `16` cannot be shortened.
* `sharp_exponent_succ_fails`, `differential_sharp_exponent_succ_fails`: `907` and `199` fail, so
  `906` and `198` are the largest exponents the exact ratios give. `sbox_not_uniform_five` and
  these two repeat checks of `Checks/BabyBear.lean`, which is not imported here because it needs
  about 7 GB of memory to build.
* `values_eq_rc16`: rows `0` to `20` of `values` are the rows of `RC16` (`zkhash-axiom` `0.2.0`
  `src/poseidon2/poseidon2_instance_babybear.rs:305-663`, row `0` at `:306-321`, row `20` at
  `:646-661`), which `rc16` copies with the hexadecimal literals of its `from_hex` calls. Columns
  `1` to `15` of rows `4` to `16` of `RC16` are zero, so OpenVM's selection (column `0` of those
  rows, `crates/circuits/poseidon2-air/src/babybear.rs:36-37`) drops nothing.
* `external_eq_sp1`: the external layer is SP1 `5.2.4`'s; `diag_ne_sp1Diag`, `internal_ne_sp1`
  and `values_ne_sp1`: the diagonal, the internal layer and the round constants are not.

## What is not claimed

The known-answer tests check single inputs. They show that the model computes the outputs that
the sources assert; they do not prove that model and code agree on every input. `upstream_kat`
comes from Plonky3 `v0.8.0`, not from the `0.4.3` that OpenVM pins, and `rng_kat` relies on
constants regenerated outside Lean. The regression values are outputs of an outside model, not of
OpenVM. Nothing here is a comparison with a built binary, with the SIMD or CUDA code paths or with
OpenVM's AIR, and nothing here strengthens the security claims of
`WideTrail.Poseidon2.OpenVMBabyBear`.

The axiom footprints of every theorem of this file and of `WideTrail.Poseidon2.OpenVMBabyBear`
are pinned at the end of the file.
-/

set_option autoImplicit false
-- Each `decide` on the runner unfolds all rounds at once; the default depth is too small.
set_option maxRecDepth 4000

open Poseidon2.BabyBear (F State modulus field_card sbox sbox_toFun)

namespace Poseidon2.OpenVMBabyBear.Checks

open Plonky3 (Dense)

/-! ### The runner -/

/-- The diagonal `diag` as the sixteen coordinates of a runner state. -/
def diagDense : Dense F :=
  ⟨2013265919, 1, 2, 1006632961, 3, 4, 1006632960, 2013265918, 2013265917, 2005401601,
    1509949441, 1761607681, 2013265906, 7864320, 125829120, 15⟩

theorem diagDense_toState : diagDense.toState = diag :=
  rfl

/-! ### The deployed permutation -/

/-- The input of `test_default_babybear_poseidon2_width_16` (Plonky3 `v0.8.0`
`baby-bear/src/poseidon2.rs:600-604`) and of `test_poseidon2_width_16_random` (`p3-baby-bear`
`0.4.3` `src/poseidon2.rs:316-320`), as canonical values. -/
def input : State :=
  ![894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
    19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913]

/-- The expected output of `test_default_babybear_poseidon2_width_16` (Plonky3 `v0.8.0`
`baby-bear/src/poseidon2.rs:606-610`), as canonical values. -/
def expected : State :=
  ![516096821, 90309867, 1101817252, 1660784290, 360715097, 1789519026, 1788910906, 563338433,
    319524748, 1741414159, 1650859320, 894311162, 1121347488, 1692793758, 1052633829, 1344246938]

/-- The runner sends the test's input to the expected output. -/
theorem kat_dense :
    Plonky3.Diag.permutationDense diagDense 1 13 sbox values (Dense.ofState input) =
      Dense.ofState expected := by
  decide

/-- **The model reproduces the known-answer test of the deployed permutation**
(`test_default_babybear_poseidon2_width_16`, Plonky3 `v0.8.0` `baby-bear/src/poseidon2.rs:598-616`,
whose constants are the deployed ones). -/
theorem upstream_kat : permutation input = expected :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 13 sbox values kat_dense

/-! ### A second constant table -/

/-- The expected output of `test_poseidon2_width_16_random` (`p3-baby-bear` `0.4.3`
`src/poseidon2.rs:322-326`), as canonical values. -/
def rngExpected : State :=
  ![1255099308, 941729227, 93609187, 112406640, 492658670, 1824768948, 812517469, 1055381989,
    670973674, 1407235524, 891397172, 1003245378, 1381303998, 1564172645, 1399931635, 1005462965]

/-- The runner, with the constants `BabyBear.Plonky3KAT.katValues`, sends the test's input to the
expected output. -/
theorem rng_kat_dense :
    Plonky3.Diag.permutationDense diagDense 1 13 sbox BabyBear.Plonky3KAT.katValues
        (Dense.ofState input) =
      Dense.ofState rngExpected := by
  decide

/-- **The model reproduces `test_poseidon2_width_16_random`** (`p3-baby-bear` `0.4.3`
`src/poseidon2.rs:314-333`): the deployed layers, S-box and round numbers, with the constants of
`Xoroshiro128Plus::seed_from_u64(1)` (`BabyBear.Plonky3KAT.katValues`) in place of the deployed
table. -/
theorem rng_kat :
    Plonky3.Diag.permutation conditions 13 sbox BabyBear.Plonky3KAT.katValues input =
      rngExpected :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 13 sbox
    BabyBear.Plonky3KAT.katValues rng_kat_dense

/-! ### Regression values -/

/-- **Regression value: the permutation on `0`.** Computed outside Lean by a model of the code;
not an OpenVM or Plonky3 test vector. -/
theorem permutation_zero :
    permutation 0 =
      ![1168947398, 128782440, 747404447, 883925857, 360581875, 1704698758, 1878363991,
        1054281681, 682225194, 705839125, 1218819873, 41544645, 1095344608, 174996601,
        1678438226, 11259290] :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 13 sbox values (by decide)

/-- **Regression value: the permutation on `(0, 1, …, 15)`.** Computed outside Lean by a model of
the code; not an OpenVM or Plonky3 test vector. -/
theorem permutation_range :
    permutation ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] =
      ![1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001,
        1761127344, 1552405120, 417318995, 36799261, 1215172152, 614923223, 1300746575,
        957311597, 304856115] :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 13 sbox values (by decide)

/-! ### Negative controls -/

/-- **Negative control: SP1's internal layer.** With the deployed constants and SP1 `5.2.4`'s
internal layer `R^{-1} (diag(-2, 1, 2, 4, …, 2^13, 2^15) + J)` (`Plonky3.permutation` with
`BabyBear.conditions`), the test fails. -/
theorem kat_fails_sp1_internal :
    Plonky3.permutation BabyBear.conditions 13 sbox values input ≠ expected :=
  Plonky3.permutation_ne_of_dense BabyBear.conditions 13 sbox values (by decide)

/-- **Negative control: SP1's diagonal without the factor.** With the deployed constants and the
layer `diag(-2, 1, 2, 4, …, 2^13, 2^15) + J`, the test fails. -/
theorem kat_fails_sp1Diag :
    Plonky3.permutation BabyBear.Plonky3KAT.conditions_one 13 sbox values input ≠ expected :=
  Plonky3.permutation_ne_of_dense BabyBear.Plonky3KAT.conditions_one 13 sbox values (by decide)

/-- The field conditions for OpenVM's diagonal with the scale `R^{-1}` of SP1's layer. -/
theorem conditions_montyInverse : Plonky3.Diag.Conditions diag BabyBear.montyInverse :=
  Plonky3.Diag.Conditions.of_mul_eq_one (by decide) diag_mul_inv
    (by rw [one_add_sum_diagInv]; decide) (by decide)

/-- **Negative control: no factor `R^{-1}`.** With OpenVM's diagonal scaled by `R^{-1}`, the test
fails. -/
theorem kat_fails_montyInverse :
    Plonky3.Diag.permutation conditions_montyInverse 13 sbox values input ≠ expected :=
  Plonky3.Diag.permutation_ne_of_dense (d := diagDense) conditions_montyInverse 13 sbox values
    (by decide)

/-- **Negative control: the initial external layer is needed.** -/
theorem kat_fails_skip_initial : Hades.execute rounds input 21 ≠ expected :=
  Plonky3.Diag.execute_ne_of_dense (d := diagDense) conditions 13 sbox values (by decide)

/-- **Negative control: the literals are canonical values.** Read as Montgomery representatives,
that is multiplied by `R^{-1}`, the three tables do not reproduce the test. -/
theorem kat_fails_monty_constants :
    Plonky3.Diag.permutation conditions 13 sbox
      (Plonky3.roundValues 13 (fun r i => externalConstants r i * BabyBear.montyInverse)
        (fun j => internalConstants j * BabyBear.montyInverse)) input ≠ expected :=
  Plonky3.Diag.permutation_ne_of_dense (d := diagDense) conditions 13 sbox _ (by decide)

/-! ### The bounds `u = 6`, `dd = 28` and `8` are attained -/

/-- Six solutions of `(x + 1)^7 - x^7 = 1346933384`, found outside Lean by exact root finding
mod `p`; the same witnesses as in `Checks/BabyBear.lean`. -/
def diffWitnesses : Finset F :=
  {216551164, 323534659, 937428934, 1075836986, 1689731261, 1796714756}

/-- **`x ↦ x^7` is not differentially `5`-uniform.** For input difference `1`, the output
difference `1346933384` has the six solutions `diffWitnesses`. With `BabyBear.sbox_uniform`, the
differential uniformity is exactly `6`. -/
theorem sbox_not_uniform_five : ¬ IsDiffUniform sbox 5 := by
  intro h
  have hle := h 1 one_ne_zero 1346933384
  have hsub : diffWitnesses ⊆ diffSet sbox 1 1346933384 := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [sbox_toFun]
    simp only [diffWitnesses, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hcard : diffWitnesses.card = 6 := by decide
  have hge := Finset.card_le_card hsub
  rw [hcard] at hge
  unfold diffCount at hle
  omega

/-- **`28` is the largest `dd` with `6 * 2^dd ≤ p`.** -/
theorem twentyNine_too_large : ¬ 6 * 2 ^ 29 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- A nonzero difference of weight four whose image also has weight four. -/
def branchWitness : State := ![-1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 4, 0, 0, 0]

/-- The first three blocks of `branchWitness` cancel against the block sum `e_0`; the last
becomes `5 M4 e_0 = (10, 5, 5, 15)`. -/
theorem external_branchWitness :
    external branchWitness = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 5, 5, 15] := by
  rw [external_eq_mdsLight]
  decide

/-- **The bound `8` of `external_isBranchBound` is attained.** -/
theorem external_not_branch_nine : ¬ isBranchBound id external 9 := by
  intro h
  have hw := h branchWitness (by decide)
  rw [external_branchWitness] at hw
  revert hw
  decide

/-! ### The window length -/

/-- **One dimension of differences stays inactive through fifteen consecutive partial rounds**
(`finrank_inactive_eq` at `r = 15`). -/
theorem finrank_inactive_fifteen :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 15) = 1 :=
  finrank_inactive_eq (by norm_num)

/-- **The window `16` cannot be shortened**: some nonzero difference stays inactive through
fifteen consecutive partial rounds. -/
theorem inactive_fifteen_ne_bot :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 15 ≠ ⊥ := by
  intro h
  have h1 := finrank_inactive_fifteen
  rw [h, finrank_bot] at h1
  exact absurd h1 (by norm_num)

/-! ### The exponents cannot be raised -/

set_option exponentiation.threshold 1000 in
/-- **`906` is the largest exponent the exact trail ratio gives.** `2^907 * 6^32 ≤ p^32` fails;
with `sharp_exponent_bound`, `906` is the largest `E` with `2^E * 6^32 ≤ p^32`. -/
theorem sharp_exponent_succ_fails :
    ¬ 2 ^ 907 * 6 ^ (32 + 13 / 16) ≤ modulus ^ (32 + 13 / 16) := by
  decide

/-- **`198` is the largest exponent the differential ratio gives.** `2^199 * 6^7 ≤ p^7` fails;
with `BabyBear.differential_sharp_exponent_bound`, `198` is the largest `E` with
`2^E * 6^7 ≤ p^7`. -/
theorem differential_sharp_exponent_succ_fails : ¬ 2 ^ 199 * 6 ^ 7 ≤ modulus ^ 7 := by
  decide

/-! ### Cross-checks with `RC16` and with SP1 `5.2.4` -/

/-- `RC16` (`zkhash-axiom` `0.2.0` `src/poseidon2/poseidon2_instance_babybear.rs:305-663`, the
same file as HorizenLabs `poseidon2` at `055bde3f4782731ba5f5ce5888a440a94327eaf3`), all
twenty-one rows, with the hexadecimal literals of its `from_hex` calls. -/
def rc16 : Fin 21 → State :=
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
      0x2cc78315, 0x1e36ea47],
    ![0x5a8053c0, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x693be639, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x3858867d, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x19334f6b, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x128f0fd8, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x4e2b1ccb, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x61210ce0, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x3c318939, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x0b5b2f22, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x2edb11d5, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x213effdf, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x0cac4606, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x241af16d, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
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

theorem values_eq_rc16_lt : ∀ n : Fin 21, ∀ i : Fin 16, values n.val i = rc16 n i := by
  decide

/-- **The round-constant table is `RC16` row for row**: round `n < 21` of the schedule reads row
`n` of `RC16`, the table from which OpenVM's AIR path selects its constants
(`crates/circuits/poseidon2-air/src/babybear.rs:22-47`). -/
theorem values_eq_rc16 (n : Fin 21) : values n.val = rc16 n := by
  funext i
  exact values_eq_rc16_lt n i

/-- The external layer is SP1 `5.2.4`'s, by definition. -/
theorem external_eq_sp1 : external = BabyBear.external :=
  rfl

/-- The diagonal is not SP1's. -/
theorem diag_ne_sp1Diag : diag ≠ Plonky3.sp1Diag F := by
  decide

/-- **The internal layer is not SP1's**: on `e_0`, coordinate `0` is `-1` here and `-R^{-1}` in
SP1's layer. -/
theorem internal_ne_sp1 : internal (Pi.single 0 1) 0 ≠ BabyBear.internal (Pi.single 0 1) 0 := by
  decide

/-- **The round constants are not SP1's**: the first constant of SP1 `5.2.4`'s table
`BabyBear.values` (row `0` of `RC_16_30`) differs. -/
theorem values_ne_sp1 : values 0 0 ≠ BabyBear.values 0 0 := by
  decide

end Poseidon2.OpenVMBabyBear.Checks

/-! ### Axiom footprints -/

/-! #### The diagonal and the field conditions -/

/-- info: 'Poseidon2.OpenVMBabyBear.diag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.diag_spec

/-- info: 'Poseidon2.OpenVMBabyBear.diag_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.diag_eq_div

/-- info: 'Poseidon2.OpenVMBabyBear.diag_eq_diagSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.diag_eq_diagSource

/-- info: 'Poseidon2.OpenVMBabyBear.diag_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.diag_mul_inv

/-- info: 'Poseidon2.OpenVMBabyBear.diag_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.diag_ne_zero

/-- info: 'Poseidon2.OpenVMBabyBear.one_add_sum_diagInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.one_add_sum_diagInv

/-- info: 'Poseidon2.OpenVMBabyBear.one_add_sum_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.one_add_sum_inv_eq

/-- info: 'Poseidon2.OpenVMBabyBear.one_add_sum_inv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.one_add_sum_inv_ne_zero

/-- info: 'Poseidon2.OpenVMBabyBear.diag_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.diag_injOn

/-- info: 'Poseidon2.OpenVMBabyBear.conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.conditions

/-! #### The linear layers -/

/-- info: 'Poseidon2.OpenVMBabyBear.external_eq_mdsLight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.external_eq_mdsLight

/-- info: 'Poseidon2.OpenVMBabyBear.external_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.external_isBranchBound

/-- info: 'Poseidon2.OpenVMBabyBear.internal_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.internal_apply

/-- info: 'Poseidon2.OpenVMBabyBear.internal_toLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.internal_toLinearMap

/-- info: 'Poseidon2.OpenVMBabyBear.internalCode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.internalCode_eq

/-- info: 'Poseidon2.OpenVMBabyBear.internalAir_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.internalAir_eq

/-! #### Round constants and rounds -/

/-- info: 'Poseidon2.OpenVMBabyBear.values_eq_roundValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.values_eq_roundValues

/-- info: 'Poseidon2.OpenVMBabyBear.partial_constants_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.partial_constants_zero

/-- info: 'Poseidon2.OpenVMBabyBear.partialRowsAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.partialRowsAtZero

/-- info: 'Poseidon2.OpenVMBabyBear.permutation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.permutation_eq

/-- info: 'Poseidon2.OpenVMBabyBear.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.permutation_bijective

/-- info: 'Poseidon2.OpenVMBabyBear.permutation_bijective_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.permutation_bijective_general

/-- info: 'Poseidon2.OpenVMBabyBear.rounds_apply_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.rounds_apply_prefix

/-- info: 'Poseidon2.OpenVMBabyBear.rounds_apply_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.rounds_apply_partial

/-- info: 'Poseidon2.OpenVMBabyBear.rounds_apply_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.rounds_apply_suffix

/-! #### The partial rounds and activity -/

/-- info: 'Poseidon2.OpenVMBabyBear.inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.inactive_trivial

/-- info: 'Poseidon2.OpenVMBabyBear.internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.internal_inactive_trivial

/-- info: 'Poseidon2.OpenVMBabyBear.finrank_inactive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.finrank_inactive_eq

/-- info: 'Poseidon2.OpenVMBabyBear.finrank_partial_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.finrank_partial_inactive

/-- info: 'Poseidon2.OpenVMBabyBear.partial_inactive_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.partial_inactive_ne_bot

/-- info: 'Poseidon2.OpenVMBabyBear.partial_window_term_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.partial_window_term_eq_zero

/-- info: 'Poseidon2.OpenVMBabyBear.exists_pair_partial_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.exists_pair_partial_free

/-- info: 'Poseidon2.OpenVMBabyBear.activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.activity_general

/-- info: 'Poseidon2.OpenVMBabyBear.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.activity

/-! #### The independent-key trail bounds -/

/--
info: 'Poseidon2.OpenVMBabyBear.independent_key_probability_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_probability_general

/-- info: 'Poseidon2.OpenVMBabyBear.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_probability

/-- info: 'Poseidon2.OpenVMBabyBear.probability_exponent' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.probability_exponent

/--
info: 'Poseidon2.OpenVMBabyBear.independent_key_probability_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_probability_exact_general

/-- info: 'Poseidon2.OpenVMBabyBear.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_probability_exact

/-- info: 'Poseidon2.OpenVMBabyBear.sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.sharp_exponent_bound

/--
info: 'Poseidon2.OpenVMBabyBear.independent_key_probability_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_probability_sharp_general

/-- info: 'Poseidon2.OpenVMBabyBear.independent_key_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_probability_sharp

/-! #### The independent-key differential bounds -/

/--
info: 'Poseidon2.OpenVMBabyBear.independent_key_differential_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_differential_exact_general

/-- info: 'Poseidon2.OpenVMBabyBear.independent_key_differential_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_differential_exact

/--
info: 'Poseidon2.OpenVMBabyBear.independent_key_differential_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_differential_sharp_general

/-- info: 'Poseidon2.OpenVMBabyBear.independent_key_differential_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.independent_key_differential_sharp

/-! #### The checks of this file -/

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.diagDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.diagDense_toState

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.kat_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.kat_dense

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.upstream_kat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.upstream_kat

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.rng_kat_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.rng_kat_dense

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.rng_kat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.rng_kat

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.permutation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.permutation_zero

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.permutation_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.permutation_range

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.kat_fails_sp1_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.kat_fails_sp1_internal

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.kat_fails_sp1Diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.kat_fails_sp1Diag

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.conditions_montyInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.conditions_montyInverse

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.kat_fails_montyInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.kat_fails_montyInverse

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.kat_fails_skip_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.kat_fails_skip_initial

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.kat_fails_monty_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.kat_fails_monty_constants

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.sbox_not_uniform_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.sbox_not_uniform_five

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.twentyNine_too_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.twentyNine_too_large

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.external_branchWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.external_branchWitness

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.external_not_branch_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.external_not_branch_nine

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.finrank_inactive_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.finrank_inactive_fifteen

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.inactive_fifteen_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.inactive_fifteen_ne_bot

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.sharp_exponent_succ_fails

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.differential_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.differential_sharp_exponent_succ_fails

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.values_eq_rc16_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.values_eq_rc16_lt

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.values_eq_rc16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.values_eq_rc16

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.external_eq_sp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.external_eq_sp1

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.diag_ne_sp1Diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.diag_ne_sp1Diag

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.internal_ne_sp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.internal_ne_sp1

/-- info: 'Poseidon2.OpenVMBabyBear.Checks.values_ne_sp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.Checks.values_ne_sp1
