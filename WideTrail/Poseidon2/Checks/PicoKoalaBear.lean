/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.PicoKoalaBear
import WideTrail.Poseidon2.Plonky3Execution
import WideTrail.Poseidon2.Checks.Plonky3KAT

/-!
# Checks for the Pico v3.2.0 KoalaBear certificate

`WideTrail.Poseidon2.PicoKoalaBear` instantiates the diagonal-generic Plonky3 model with the
permutation `default_koalabear_poseidon2_16()` of the fork `brevis-network/Plonky3` at
`da6ca12c71912ec213d3c5af68b14509d2099bc3` (crate version `0.5.4`), which Pico v3.2.0 uses. The
checks below test that instantiation against the source's test vectors, record which readings of
the code they rule out, and show that the uniformity `2`, the branch number `8`, the window `16`
and the exponents used by the bounds cannot be improved. Every finite check is kernel `decide`.
The whole-permutation checks run on the runner `Plonky3.Diag.permutationDense` of
`WideTrail.Poseidon2.Plonky3Execution` (diagonal `diagDense`, scale `1`), and
`Plonky3.Diag.permutation_eq_of_dense` and its companions transfer the computed values to the
specification.

## Known-answer tests

* **The deployed permutation** (`upstream_kat`). `test_default_koalabear_poseidon2_width_16`
  (fork `koala-bear/src/poseidon2.rs:524-542`) builds `default_koalabear_poseidon2_16()` (`:538`)
  and asserts its output on a fixed input (input `:526-530`, expected output `:532-536`). The
  test uses the deployed round constants, so this is a known-answer test of the permutation
  itself: `permutation input = expected`, with input and output copied from the source. The same
  pair is `PLONKY3_INPUT` / `PLONKY3_KOALABEAR_OUTPUT` in Pico
  (`vm/src/primitives/poseidon2_kat.rs:98-107`), asserted there against the host permutation
  (`:121`) and against Pico's AIR gadget (`:125`), and Pico's MLE configuration replays it
  (`mle-core/src/config/poseidon2_kat.rs:89-106`). Upstream `p3-koala-bear` `0.8.0` carries the
  same test with the same values (`src/poseidon2.rs:613-631`; compared outside Lean). Both arrays
  pass through `KoalaBear::new_array` (`to_monty` of the literal) or `from_u32`, and the
  comparisons are of field elements or of canonical values, so the literals are canonical values.
* **A second constant table** (`rng_kat`). `test_poseidon2_width_16_random` (fork
  `koala-bear/src/poseidon2.rs:438-457`, the same input at `:440-444`, expected output
  `:446-450`) runs the same layers, S-box and round numbers with constants drawn by
  `Poseidon2KoalaBear::new_from_rng_128(&mut Xoroshiro128Plus::seed_from_u64(1))`. For a
  31-bit prime and `(16, 3)`, `poseidon2_round_numbers_128` returns `(8, 20)`
  (`poseidon2/src/round_numbers.rs:55`); `new_from_rng` (`poseidon2/src/lib.rs:77-85`) draws four
  initial rows, four terminal rows (`poseidon2/src/external.rs:199-213`) and then twenty
  scalars, and each sample is a raw Montgomery representative `next_u32() >> 1`, redrawn while it
  is at least `p` (`monty-31/src/monty_31.rs:154-165`), so its field element is the sample times
  `R^{-1}`. These are the sampler, the drawing order and the generator of the `0.4.3-succinct`
  test that `Checks/Plonky3KAT.lean` reproduces, and an emulation run outside Lean drew exactly
  its raw tables `KoalaBear.Plonky3KAT.extRaw` and `intRaw`; so this file reuses its table
  `KoalaBear.Plonky3KAT.katValues`. That the emulation matches the Rust generator is not checked
  directly; the evidence is that the model reproduces the expected outputs of both tests, which
  come from the sources. This test does not exercise the deployed constants.
* **Pico's own pin** (`permutation_range`). Pico records the output of its permutation on
  `(0, 1, …, 15)` as `KAT_PERMUTATION_KOALABEAR` (`vm/src/primitives/poseidon2_kat.rs:146-149`,
  test `:154-158`, input `seq(0)` from `:42-44`) and again in
  `mle-core/src/config/poseidon2_kat.rs:60-64` ("Pinned on Plonky3 0.5.4", `:49-50`). These are
  values Pico computed with its own permutation, not independent evidence; the model reproduces
  them.
* **A regression value** (`permutation_zero`). `permutation 0` was computed outside Lean by a
  model of the code that reproduces the vectors above. It does not come from Pico or Plonky3 and
  serves only to detect changes.

## Negative controls

On the input of `upstream_kat`, the expected output is not reproduced by SP1 v6.10.0's
permutation `KoalaBear.permutation`, which has the same round constants and the internal layer
`R^{-1} (diag(-2, 1, 2, 4, …, 2^13, 2^15) + J)` (`kat_fails_sp1`); by Pico's diagonal with the
factor `R^{-1}` (`kat_fails_montyInverse`); without the initial external layer
(`kat_fails_skip_initial`); or with the literals of the three tables read as Montgomery
representatives, that is times `R^{-1}` (`kat_fails_monty_constants`). So the vector rules out
each of these four alternatives to the model.

## Exactness and cross-checks

* `sbox_not_uniform_one`: the cube S-box is not differentially `1`-uniform, so `u = 2` is
  least. `thirty_too_large`: `2 * 2^30 > p`, so `29` is the largest `dd` with `2 * 2^dd ≤ p`.
* `external_branchWitness`, `external_not_branch_nine`: a difference of weight four with an image
  of weight four, so the branch number of the external layer is exactly `8`.
* `finrank_inactive_fifteen`, `inactive_fifteen_ne_bot`: a one-dimensional space of differences
  stays inactive through fifteen consecutive partial rounds (`finrank_inactive_eq` at `r = 15`),
  so the window `16` cannot be shortened.
* `sharp_exponent_succ_fails`, `differential_sharp_exponent_succ_fails`: `990` and `210` fail, so
  `989` and `209` are the largest exponents the exact ratios give. These repeat checks of
  `Checks/KoalaBear.lean`, which is not imported here because it needs about 12 GB of memory to
  build.
* `values_eq_sp1`: the round-constant table is, entry by entry, SP1 v6.10.0's
  `KoalaBear.values` (`RC16`, `slop-koala-bear` `6.10.0` `src/koala_bear_poseidon2.rs:96`);
  `external_eq_sp1`: the external layers coincide; `diag_ne_sp1Diag` and `internal_ne_sp1`: the
  diagonals and the internal layers differ.

## What is not claimed

The known-answer tests check single inputs. They show that the model computes the outputs that
the sources assert; they do not prove that model and code agree on every input. `rng_kat` relies
on constants regenerated outside Lean. `permutation_range` reproduces a value that Pico pinned
from its own implementation, and `permutation_zero` is an output of an outside model, not of Pico.
Nothing here is a comparison with a built binary, with the SIMD code paths or with Pico's AIR
beyond the source's assertion that the AIR gadget reproduces the vector of `upstream_kat`, and
nothing here strengthens the security claims of `WideTrail.Poseidon2.PicoKoalaBear`.

The axiom footprints of every theorem of this file and of `WideTrail.Poseidon2.PicoKoalaBear`
are pinned at the end of the file.
-/

set_option autoImplicit false
-- Each `decide` on the runner unfolds all rounds at once; the default depth is too small.
set_option maxRecDepth 4000

open Poseidon2.KoalaBear (F State modulus field_card sbox sbox_toFun)

namespace Poseidon2.PicoKoalaBear.Checks

open Plonky3 (Dense)

/-! ### The runner -/

/-- The diagonal `diag` as the sixteen coordinates of a runner state. -/
def diagDense : Dense F :=
  ⟨2130706431, 1, 2, 1065353217, 3, 4, 1065353216, 2130706430, 2130706429, 2122383361,
    1864368129, 2130706306, 8323072, 266338304, 133169152, 127⟩

theorem diagDense_toState : diagDense.toState = diag :=
  rfl

/-! ### The deployed permutation -/

/-- The input of `test_default_koalabear_poseidon2_width_16` (fork
`koala-bear/src/poseidon2.rs:526-530`) and of `test_poseidon2_width_16_random` (`:440-444`), as
canonical values. -/
def input : State :=
  ![894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
    19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913]

/-- The expected output of `test_default_koalabear_poseidon2_width_16` (fork
`koala-bear/src/poseidon2.rs:532-536`; Pico's `PLONKY3_KOALABEAR_OUTPUT`,
`vm/src/primitives/poseidon2_kat.rs:104-107`), as canonical values. -/
def expected : State :=
  ![1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110, 1391183747, 351743874,
    1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461, 748270449, 651545025]

/-- The runner sends the test's input to the expected output. -/
theorem kat_dense :
    Plonky3.Diag.permutationDense diagDense 1 20 sbox values (Dense.ofState input) =
      Dense.ofState expected := by
  decide

/-- **The model reproduces the known-answer test of the deployed permutation**
(`test_default_koalabear_poseidon2_width_16`, fork `koala-bear/src/poseidon2.rs:524-542`, with the
deployed round constants). -/
theorem upstream_kat : permutation input = expected :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 20 sbox values kat_dense

/-! ### A second constant table -/

/-- The expected output of `test_poseidon2_width_16_random` (fork
`koala-bear/src/poseidon2.rs:446-450`), as canonical values. -/
def rngExpected : State :=
  ![652590279, 1200629963, 1013089423, 1840372851, 19101828, 561050015, 1714865585, 994637181,
    498949829, 729884572, 1957973925, 263012103, 535029297, 2121808603, 964663675, 1473622080]

/-- The runner, with the constants `KoalaBear.Plonky3KAT.katValues`, sends the test's input to
the expected output. -/
theorem rng_kat_dense :
    Plonky3.Diag.permutationDense diagDense 1 20 sbox KoalaBear.Plonky3KAT.katValues
        (Dense.ofState input) =
      Dense.ofState rngExpected := by
  decide

/-- **The model reproduces `test_poseidon2_width_16_random`** (fork
`koala-bear/src/poseidon2.rs:438-457`): Pico's layers, S-box and round numbers, with the constants
of `Xoroshiro128Plus::seed_from_u64(1)` (`KoalaBear.Plonky3KAT.katValues`) in place of the
deployed table. -/
theorem rng_kat :
    Plonky3.Diag.permutation conditions 20 sbox KoalaBear.Plonky3KAT.katValues input =
      rngExpected :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 20 sbox
    KoalaBear.Plonky3KAT.katValues rng_kat_dense

/-! ### Pico's pin and a regression value -/

/-- **Pico's pinned value on `(0, 1, …, 15)`**: `KAT_PERMUTATION_KOALABEAR`
(`vm/src/primitives/poseidon2_kat.rs:146-149`; `mle-core/src/config/poseidon2_kat.rs:60-64`).
Pico recorded it from its own permutation; it is not an independent vector. -/
theorem permutation_range :
    permutation ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] =
      ![1259554834, 663463928, 1989430097, 476523442, 836740795, 1803459961, 1229318262,
        2023956904, 2054405130, 1556655036, 1455339712, 1471465890, 423337459, 353979748,
        1203410294, 1592576868] :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 20 sbox values (by decide)

/-- **Regression value: the permutation on `0`.** Computed outside Lean by a model of the code;
not a Pico or Plonky3 test vector. -/
theorem permutation_zero :
    permutation 0 =
      ![1467453764, 68262570, 2085334433, 1711169726, 869537427, 698494029, 1998923102, 727938840,
        1236421175, 857433239, 1995651691, 1526804549, 968729910, 15322618, 1511105384,
        1900792116] :=
  Plonky3.Diag.permutation_eq_of_dense (d := diagDense) conditions 20 sbox values (by decide)

/-! ### Negative controls -/

/-- **SP1 v6.10.0's permutation fails Pico's vector.** It has the same round constants
(`values_eq_sp1`) and the internal layer `R^{-1} (diag(-2, 1, 2, 4, …, 2^13, 2^15) + J)`. -/
theorem kat_fails_sp1 : KoalaBear.permutation input ≠ expected :=
  Plonky3.permutation_ne_of_dense KoalaBear.conditions 20 sbox KoalaBear.values (by decide)

/-- The field conditions for Pico's diagonal with the scale `R^{-1}` of SP1's layer. -/
theorem conditions_montyInverse : Plonky3.Diag.Conditions diag KoalaBear.montyInverse :=
  Plonky3.Diag.Conditions.of_mul_eq_one (by decide) diag_mul_inv
    (by rw [one_add_sum_diagInv]; decide) (by decide)

/-- **Negative control: no factor `R^{-1}`.** With Pico's diagonal scaled by `R^{-1}`, the test
fails. -/
theorem kat_fails_montyInverse :
    Plonky3.Diag.permutation conditions_montyInverse 20 sbox values input ≠ expected :=
  Plonky3.Diag.permutation_ne_of_dense (d := diagDense) conditions_montyInverse 20 sbox values
    (by decide)

/-- **Negative control: the initial external layer is needed.** -/
theorem kat_fails_skip_initial : Hades.execute rounds input 28 ≠ expected :=
  Plonky3.Diag.execute_ne_of_dense (d := diagDense) conditions 20 sbox values (by decide)

/-- **Negative control: the literals are canonical values.** Read as Montgomery representatives,
that is multiplied by `R^{-1}`, the three tables do not reproduce the test. -/
theorem kat_fails_monty_constants :
    Plonky3.Diag.permutation conditions 20 sbox
      (Plonky3.roundValues 20 (fun r i => externalConstants r i * KoalaBear.montyInverse)
        (fun j => internalConstants j * KoalaBear.montyInverse)) input ≠ expected :=
  Plonky3.Diag.permutation_ne_of_dense (d := diagDense) conditions 20 sbox _ (by decide)

/-! ### The bounds `u = 2`, `dd = 29` and `8` are attained -/

/-- **The cube S-box is not differentially `1`-uniform.** For input difference `1`, the output
difference `1` has the two solutions `0` and `-1` of `(x + 1)^3 - x^3 = 1`. With
`KoalaBear.sbox_uniform`, the differential uniformity is exactly `2`. -/
theorem sbox_not_uniform_one : ¬ IsDiffUniform sbox 1 := by
  intro h
  have hle := h 1 one_ne_zero 1
  have hsub : ({0, -1} : Finset F) ⊆ diffSet sbox 1 1 := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [sbox_toFun]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · decide
    · rw [Finset.mem_singleton.mp hx]
      decide
  have hcard : ({0, -1} : Finset F).card = 2 := by decide
  have hge := Finset.card_le_card hsub
  rw [hcard] at hge
  unfold diffCount at hle
  omega

/-- **`29` is the largest `dd` with `2 * 2^dd ≤ p`.** -/
theorem thirty_too_large : ¬ 2 * 2 ^ 30 ≤ Fintype.card F := by
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
/-- **`989` is the largest exponent the exact trail ratio gives.** `2^990 * 2^33 ≤ p^33` fails;
with `KoalaBear.sharp_exponent_bound`, `989` is the largest `E` with `2^E * 2^33 ≤ p^33`. -/
theorem sharp_exponent_succ_fails :
    ¬ 2 ^ 990 * 2 ^ (32 + 20 / 16) ≤ modulus ^ (32 + 20 / 16) := by
  decide

/-- **`209` is the largest exponent the differential ratio gives.** `2^210 * 2^7 ≤ p^7` fails;
with `KoalaBear.differential_sharp_exponent_bound`, `209` is the largest `E` with
`2^E * 2^7 ≤ p^7`. -/
theorem differential_sharp_exponent_succ_fails : ¬ 2 ^ 210 * 2 ^ 7 ≤ modulus ^ 7 := by
  decide

/-! ### Cross-checks with SP1 v6.10.0 -/

theorem values_eq_sp1_lt :
    ∀ n : Fin 28, ∀ i : Fin 16, values n.val i = KoalaBear.values n.val i := by
  decide

/-- **The round-constant table is SP1 v6.10.0's**, entry by entry: `values` is
`KoalaBear.values`, the table `RC16` of `slop-koala-bear` `6.10.0`
(`src/koala_bear_poseidon2.rs:96`). -/
theorem values_eq_sp1 : values = KoalaBear.values := by
  funext n i
  by_cases hn : n < 28
  · exact values_eq_sp1_lt ⟨n, hn⟩ i
  · simp [values, KoalaBear.values, Plonky3.roundValues, hn, show ¬n < 4 by omega,
      show ¬n < 4 + 20 by omega]

/-- The external layer is SP1's, by definition. -/
theorem external_eq_sp1 : external = KoalaBear.external :=
  rfl

/-- The diagonal is not SP1's. -/
theorem diag_ne_sp1Diag : diag ≠ Plonky3.sp1Diag F := by
  decide

/-- **The internal layer is not SP1's**: on `e_0`, coordinate `0` is `-1` here and `-R^{-1}` in
SP1's layer. -/
theorem internal_ne_sp1 : internal (Pi.single 0 1) 0 ≠ KoalaBear.internal (Pi.single 0 1) 0 := by
  decide

end Poseidon2.PicoKoalaBear.Checks

/-! ### Axiom footprints -/

/-! #### The diagonal and the field conditions -/

/-- info: 'Poseidon2.PicoKoalaBear.diag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.diag_spec

/-- info: 'Poseidon2.PicoKoalaBear.diag_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.diag_eq_div

/-- info: 'Poseidon2.PicoKoalaBear.diag_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.diag_mul_inv

/-- info: 'Poseidon2.PicoKoalaBear.diag_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.diag_ne_zero

/-- info: 'Poseidon2.PicoKoalaBear.one_add_sum_diagInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.one_add_sum_diagInv

/-- info: 'Poseidon2.PicoKoalaBear.one_add_sum_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.one_add_sum_inv_eq

/-- info: 'Poseidon2.PicoKoalaBear.one_add_sum_inv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.one_add_sum_inv_ne_zero

/-- info: 'Poseidon2.PicoKoalaBear.diag_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.diag_injOn

/-- info: 'Poseidon2.PicoKoalaBear.conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.conditions

/-! #### The linear layers -/

/-- info: 'Poseidon2.PicoKoalaBear.external_eq_mdsLight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.external_eq_mdsLight

/-- info: 'Poseidon2.PicoKoalaBear.external_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.external_isBranchBound

/-- info: 'Poseidon2.PicoKoalaBear.internal_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.internal_apply

/-- info: 'Poseidon2.PicoKoalaBear.internal_toLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.internal_toLinearMap

/-- info: 'Poseidon2.PicoKoalaBear.internalCode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.internalCode_eq

/-! #### Round constants and rounds -/

/-- info: 'Poseidon2.PicoKoalaBear.values_eq_roundValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.values_eq_roundValues

/-- info: 'Poseidon2.PicoKoalaBear.partial_constants_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.partial_constants_zero

/-- info: 'Poseidon2.PicoKoalaBear.partialRowsAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.partialRowsAtZero

/-- info: 'Poseidon2.PicoKoalaBear.permutation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.permutation_eq

/-- info: 'Poseidon2.PicoKoalaBear.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.permutation_bijective

/-- info: 'Poseidon2.PicoKoalaBear.permutation_bijective_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.permutation_bijective_general

/-- info: 'Poseidon2.PicoKoalaBear.rounds_apply_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.rounds_apply_prefix

/-- info: 'Poseidon2.PicoKoalaBear.rounds_apply_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.rounds_apply_partial

/-- info: 'Poseidon2.PicoKoalaBear.rounds_apply_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.rounds_apply_suffix

/-! #### The partial rounds and activity -/

/-- info: 'Poseidon2.PicoKoalaBear.inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.inactive_trivial

/-- info: 'Poseidon2.PicoKoalaBear.internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.internal_inactive_trivial

/-- info: 'Poseidon2.PicoKoalaBear.finrank_inactive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.finrank_inactive_eq

/-- info: 'Poseidon2.PicoKoalaBear.activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.activity_general

/-- info: 'Poseidon2.PicoKoalaBear.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.activity

/-! #### The independent-key trail bounds -/

/-- info: 'Poseidon2.PicoKoalaBear.independent_key_probability_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_general

/-- info: 'Poseidon2.PicoKoalaBear.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_probability_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_exact_general

/-- info: 'Poseidon2.PicoKoalaBear.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_exact

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_probability_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_sharp_general

/-- info: 'Poseidon2.PicoKoalaBear.independent_key_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_sharp

/-! #### The independent-key differential bounds -/

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_differential_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_differential_exact_general

/-- info: 'Poseidon2.PicoKoalaBear.independent_key_differential_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_differential_exact

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_differential_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_differential_sharp_general

/-- info: 'Poseidon2.PicoKoalaBear.independent_key_differential_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_differential_sharp

/-! #### The checks of this file -/

/-- info: 'Poseidon2.PicoKoalaBear.Checks.diagDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.diagDense_toState

/-- info: 'Poseidon2.PicoKoalaBear.Checks.kat_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.kat_dense

/-- info: 'Poseidon2.PicoKoalaBear.Checks.upstream_kat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.upstream_kat

/-- info: 'Poseidon2.PicoKoalaBear.Checks.rng_kat_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.rng_kat_dense

/-- info: 'Poseidon2.PicoKoalaBear.Checks.rng_kat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.rng_kat

/-- info: 'Poseidon2.PicoKoalaBear.Checks.permutation_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.permutation_range

/-- info: 'Poseidon2.PicoKoalaBear.Checks.permutation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.permutation_zero

/-- info: 'Poseidon2.PicoKoalaBear.Checks.kat_fails_sp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.kat_fails_sp1

/-- info: 'Poseidon2.PicoKoalaBear.Checks.conditions_montyInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.conditions_montyInverse

/-- info: 'Poseidon2.PicoKoalaBear.Checks.kat_fails_montyInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.kat_fails_montyInverse

/-- info: 'Poseidon2.PicoKoalaBear.Checks.kat_fails_skip_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.kat_fails_skip_initial

/-- info: 'Poseidon2.PicoKoalaBear.Checks.kat_fails_monty_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.kat_fails_monty_constants

/-- info: 'Poseidon2.PicoKoalaBear.Checks.sbox_not_uniform_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.sbox_not_uniform_one

/-- info: 'Poseidon2.PicoKoalaBear.Checks.thirty_too_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.thirty_too_large

/-- info: 'Poseidon2.PicoKoalaBear.Checks.external_branchWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.external_branchWitness

/-- info: 'Poseidon2.PicoKoalaBear.Checks.external_not_branch_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.external_not_branch_nine

/-- info: 'Poseidon2.PicoKoalaBear.Checks.finrank_inactive_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.finrank_inactive_fifteen

/-- info: 'Poseidon2.PicoKoalaBear.Checks.inactive_fifteen_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.inactive_fifteen_ne_bot

/-- info: 'Poseidon2.PicoKoalaBear.Checks.sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.sharp_exponent_succ_fails

/-- info: 'Poseidon2.PicoKoalaBear.Checks.differential_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.differential_sharp_exponent_succ_fails

/-- info: 'Poseidon2.PicoKoalaBear.Checks.values_eq_sp1_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.values_eq_sp1_lt

/-- info: 'Poseidon2.PicoKoalaBear.Checks.values_eq_sp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.values_eq_sp1

/-- info: 'Poseidon2.PicoKoalaBear.Checks.external_eq_sp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.external_eq_sp1

/-- info: 'Poseidon2.PicoKoalaBear.Checks.diag_ne_sp1Diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.diag_ne_sp1Diag

/-- info: 'Poseidon2.PicoKoalaBear.Checks.internal_ne_sp1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.Checks.internal_ne_sp1
