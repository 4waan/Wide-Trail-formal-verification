/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.Plonky3Execution
import WideTrail.Poseidon2.KoalaBear
import WideTrail.Poseidon2.BabyBear

/-!
# Upstream known-answer tests for the width-sixteen Plonky3 Poseidon2 permutation

`p3-koala-bear` `0.4.3-succinct` and `p3-baby-bear` `0.2.3-succinct` each test the width-sixteen
permutation on one fixed input: `test_poseidon2_width_16_random`, KoalaBear
`src/poseidon2.rs:174-191` with `D = 3`, BabyBear `src/poseidon2.rs:164-181` with `D = 7`. Each
test builds `Poseidon2<F, Poseidon2ExternalMatrixGeneral, DiffusionMatrix…, 16, D>` (KoalaBear
`src/poseidon2.rs:154-167`, BabyBear `:144-157`): the external layer, the internal layer with its
diagonal and Montgomery factor, the S-box and the round numbers of SP1's instance, with other
round constants. This file proves, by `decide` on the runner of
`WideTrail.Poseidon2.Plonky3Execution` and its refinement theorem, that the generic model
`Plonky3.permutation`, with the scale, S-box and round count of `WideTrail.Poseidon2.KoalaBear`
and `WideTrail.Poseidon2.BabyBear` and with the test's round constants, sends the test's input
to the test's expected output. This exercises the model end to end against the crates' test
vectors: the initial external layer, the external layer `circ(2 M4, M4, M4, M4)`, the internal
layer with its factor `R^{-1}`, the S-box, the partial rounds on `state[0]` and the schedule.

## What the tests run

* **Round numbers.** `Poseidon2::new_from_rng_128` (`p3-poseidon2` `src/lib.rs:142-166`, the
  same text in `0.4.3-succinct` and `0.2.3-succinct`) takes `(rounds_f, rounds_p)` from
  `poseidon2_round_numbers_128::<F>(16, D)` (`src/round_numbers.rs:31-72`). That function asserts
  `gcd(D, p - 1) = 1` (line 33) and, for a prime of `31` bits (line 36), returns `(8, 20)` for
  `(16, 3)` (line 40) and `(8, 13)` for `(16, 7)` (line 42); `round_numbers` checks the bit
  length and the gcd. So the tests run `4 + 20 + 4` and `4 + 13 + 4` rounds after the initial
  external layer (`src/lib.rs:177-202`), the round numbers of SP1's instances.
* **Round constants.** `new_from_rng_128` draws from `Xoroshiro128Plus::seed_from_u64(1)`
  (KoalaBear `src/poseidon2.rs:160`, BabyBear `:150`) eight rows of sixteen field samples
  (`src/lib.rs:152-155`), then `rounds_p` single samples (`:156`). The first four rows are the
  constants of the first four full rounds and the last four those of the last four
  (`src/lib.rs:183-184`, `:197-198`); the single samples are added to `state[0]` in the partial
  rounds (`:191`). A sample (`Distribution<F> for Standard`, KoalaBear `src/koala_bear.rs:73-84`,
  BabyBear `src/baby_bear.rs:68-79`) is `next_u32() >> 1`, drawn again while it is at least `p`,
  and stored as the raw Montgomery representative, `F { value: next_u31 }`. Its field element is
  therefore `value * R^{-1}` with `R = 2^32` (`fromMonty`; `fromMonty_mul` records
  `fromMonty v * R = v`).
* **Input and expected output.** Both arrays are integer literals mapped through
  `F::from_canonical_u32` (KoalaBear `src/poseidon2.rs:175-180` and `:182-187`, BabyBear
  `:165-170` and `:172-177`), which stores `to_monty(n) = n R mod p`, the representative of the
  field element `n` (KoalaBear `src/koala_bear.rs:145-148`, `:163-165`; BabyBear
  `src/baby_bear.rs:140-143`, `:158-160`). The test compares with `assert_eq!` (KoalaBear line
  `190`, BabyBear line `180`) through the derived `PartialEq` on the representative (KoalaBear
  `src/koala_bear.rs:31-37`, BabyBear `src/baby_bear.rs:26-32`), which is injective on field
  elements. So both arrays are canonical values; they appear here as numerals of `F` (`input`,
  `expected`), copied from the crate sources.

## How the constant tables were made

`extRaw` and `intRaw` are not text from any source. They were regenerated outside Lean by a
Python emulation of the generator: `seed_from_u64(1)` fills the two state words with two
consecutive SplitMix64 outputs from the seed `1`; `next_u64` is xoroshiro128+ (output `s0 + s1`,
then `s1 ^= s0`, `s0 = rotl(s0, 24) ^ s1 ^ (s1 << 16)`, `s1 = rotl(s1, 37)`); `next_u32` is the
upper half of `next_u64`. This is the generator of `rand_xoshiro` `0.6`, the dev-dependency of
`p3-baby-bear` `0.2.3-succinct` (`Cargo.toml:77-78`); the published manifest of
`p3-koala-bear` `0.4.3-succinct` names no dev-dependencies. The sampler's rejection step
discarded two draws for KoalaBear and eleven for BabyBear. The tables list the accepted raw
values in drawing order. No Rust code was run, so that the emulation matches the Rust generator
is not checked directly; the evidence for it is that the model with these constants reproduces
both expected outputs, which come from the crate sources. For KoalaBear, `fromMonty` of these
tables gives the field elements `katExternal` and `katInternal` of `Checks/KoalaBear.lean`, which
were generated separately; the two were compared outside Lean.

## Results

For each field, with `katValues = Plonky3.roundValues rP katExternal katInternal`:

* `upstream_kat`: `Plonky3.permutation conditions rP sbox katValues input = expected`, where
  `conditions` carries the scale `montyInverse = R^{-1}`, `sbox` is `x ↦ x^D`, and `rP = 20`
  (KoalaBear) or `13` (BabyBear). It follows from `kat_dense`, a `decide` on
  `Plonky3.permutationDense`, by `Plonky3.permutation_eq_of_dense`. The partial rows of
  `katValues` vanish off coordinate `0`, so its partial rounds are the code's
  (`Plonky3.rounds_roundValues_apply_middle`).
* **Negative controls.** The test is not reproduced with the scale `1` in place of `R^{-1}`
  (`kat_fails_unscaled`), without the initial external layer
  (`kat_fails_skip_initial`), or with the raw samples read as canonical values rather
  than as Montgomery representatives (`kat_fails_raw_constants`). So the test fixes each of these
  three readings of the code.
* **Regression values with SP1's constants.** `permutation_zero` and `permutation_range`
  evaluate the pinned permutations `KoalaBear.permutation` and `BabyBear.permutation`, which are
  the model of `upstream_kat` with SP1's table (`permutation_eq_model`), on `0` and on
  `(0, 1, …, 15)`. The expected values were computed outside Lean by a Python model of
  the specification, the model that also reproduces the upstream tests. They do not come from an
  SP1 test or from running SP1, and serve only to detect changes. `permutation_zero` repeats, by
  another route, `zero_permutation` of `Checks/KoalaBear.lean` and `permutation_zero` of
  `Checks/BabyBear.lean`.

Each `decide` evaluates the whole permutation at once on the runner.

## What is not claimed

A known-answer test checks one input, with round constants that are not SP1's. It shows that the
model, with the regenerated constants, computes the output that the crate's test asserts on that
input; it does not prove that model and code agree on every input, and the agreement of the
model's round-constant tables with SP1's rests on the source comparisons recorded in
`WideTrail.Poseidon2.KoalaBear` and `WideTrail.Poseidon2.BabyBear`. The regression values are
outputs of the model, not of SP1. No security statement is made here: the activity counts of
the instances are lower bounds on charged S-boxes for actual input pairs, and their probability
statements concern one trail in the model with an additional independent uniform key per round,
not the permutation with its fixed constants and not a differential. Nothing is said about
subspace-trail resistance, algebraic attacks, sponge or duplex constructions, or equivalence
with SP1's AIR, the gnark circuit or a built binary.
-/

set_option autoImplicit false
-- Each `decide` below unfolds all rounds of the runner at once; the default depth is too small.
set_option maxRecDepth 4000

/-! ### KoalaBear, `D = 3` -/

namespace Poseidon2.KoalaBear.Plonky3KAT

open Plonky3 (Dense permutationDense roundValues permutation_eq_of_dense permutation_ne_of_dense
  execute_ne_of_dense)

/-- The field element `v R^{-1}`, `R = 2^32`: for `v < p`, the element whose Montgomery
representative is `v`. -/
def fromMonty (v : ℕ) : F := (v : F) * montyInverse

/-- `v * R^{-1} * R = v` in `F`; for `v < p` (`raw_lt_modulus`) this makes `v` the Montgomery
representative of `fromMonty v`. -/
theorem fromMonty_mul (v : ℕ) : fromMonty v * 2 ^ 32 = v := by
  rw [fromMonty, mul_assoc, montyInverse_mul, mul_one]

/-- `p` has `31` bits and `gcd(3, p - 1) = 1`, so `poseidon2_round_numbers_128` returns
`(8, 20)` for width `16` and `D = 3` (`p3-poseidon2` `0.4.3-succinct`
`src/round_numbers.rs:33-40`). -/
theorem round_numbers : 2 ^ 30 ≤ modulus ∧ modulus < 2 ^ 31 ∧ Nat.gcd 3 (modulus - 1) = 1 := by
  decide

/-- The raw Montgomery representatives of the test's eight external rows, in drawing order.
Regenerated outside Lean (see the module docstring); not text from any source. -/
def extRaw : Fin 8 → Fin 16 → ℕ :=
  ![![670752198, 2052960689, 867595173, 1121120522, 1732216065, 1777538858, 974826695, 857651441,
      1509218160, 933669702, 308743513, 1606546523, 1395707998, 1248974626, 733565087, 1614794869],
    ![1457687568, 311580733, 2055660101, 1735187654, 1563765150, 358422393, 615368408, 1022914986,
      1745808542, 1451694789, 1010294888, 478426997, 974777474, 836569592, 553962986, 354722588],
    ![1099724285, 957403621, 1171073730, 1314307614, 1575313895, 511348931, 1777322674, 743793854,
      821769216, 365270850, 2100202195, 1610545562, 1781773041, 1642480066, 968153742, 107763776],
    ![304102504, 1048805912, 670079580, 1825005418, 699322108, 372969254, 1347088819, 1017368981,
      695522824, 1491107118, 1656304581, 934311777, 1538050768, 1121275927, 1281424936, 1609172128],
    ![302658704, 2055094098, 16103019, 802016690, 359041126, 1491417545, 151742200, 122792040,
      802809388, 2020259742, 437172020, 1610027373, 1217130568, 1833171446, 60728125, 173288461],
    ![1580136315, 2058149815, 1766051075, 458819359, 1495214374, 696367131, 367271168, 4549961,
      718747682, 1943893587, 1536582683, 1574838747, 1735444335, 848039704, 1689611743, 173154748],
    ![427470023, 1004172913, 2077368442, 782638163, 1744615017, 1082619536, 297763826, 1160504957,
      618979668, 1687696498, 37211066, 2117379525, 1790329919, 1183379851, 545339302, 1229207547],
    ![723170958, 1927785244, 1080767281, 1903150401, 1929310598, 95801870, 637696247, 1214340530,
      1722126248, 1823128363, 926128391, 210718841, 1667233644, 688337540, 129024239, 1282387121]]

/-- The raw Montgomery representatives of the test's twenty internal constants, drawn after the
external rows. -/
def intRaw : Fin 20 → ℕ :=
  ![2004475442, 535738304, 1985680653, 895998816, 1108547306, 776893336, 1108245527, 574331301,
      1825109420, 1194870642, 1497066195, 1664793266, 1178412180, 1275811987, 764620473, 668520154,
      1778964353, 869842094, 2128984066, 747581376]

/-- Every sample is below `p`, as the sampler's rejection step ensures. -/
theorem raw_lt_modulus : (∀ r i, extRaw r i < modulus) ∧ ∀ j, intRaw j < modulus := by
  decide

/-- The external rows as field elements. -/
def katExternal (r : Fin 8) (i : Fin 16) : F := fromMonty (extRaw r i)

/-- The internal constants as field elements. -/
def katInternal (j : Fin 20) : F := fromMonty (intRaw j)

/-- The test's round-constant table. -/
def katValues : ℕ → State := roundValues 20 katExternal katInternal

/-- The input of `test_poseidon2_width_16_random` (`p3-koala-bear` `0.4.3-succinct`
`src/poseidon2.rs:175-180`), as canonical values. -/
def input : State :=
  ![894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
      19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913]

/-- The expected output of the test (`src/poseidon2.rs:182-187`), as canonical values. -/
def expected : State :=
  ![575479740, 1350824762, 2117880331, 1034350182, 1722317281, 988412135, 1272198010, 2022533539,
      1465703323, 648698653, 439658904, 878238659, 1163940027, 287402877, 685135400, 1397893936]

/-- The runner sends the test's input to the expected output. -/
theorem kat_dense :
    permutationDense montyInverse 20 sbox katValues (Dense.ofState input) =
      Dense.ofState expected := by
  decide

/-- **The model reproduces the upstream known-answer test** (`p3-koala-bear` `0.4.3-succinct`
`src/poseidon2.rs:174-191`). -/
theorem upstream_kat : Plonky3.permutation conditions 20 sbox katValues input = expected :=
  permutation_eq_of_dense conditions 20 sbox katValues kat_dense

/-- The pinned permutation is the model of `upstream_kat` with SP1's table `values` in place of
the test's table `katValues`. -/
theorem permutation_eq_model : permutation = Plonky3.permutation conditions 20 sbox values :=
  rfl

/-- The field conditions also hold for the scale `1`. -/
theorem conditions_one : Plonky3.Conditions (1 : F) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Negative control: the factor `R^{-1}` is needed.** With the internal layer `diag d + J`,
the test fails. -/
theorem kat_fails_unscaled :
    Plonky3.permutation conditions_one 20 sbox katValues input ≠ expected :=
  permutation_ne_of_dense conditions_one 20 sbox katValues (by decide)

/-- **Negative control: the initial external layer is needed.** -/
theorem kat_fails_skip_initial :
    Hades.execute (Plonky3.rounds conditions 20 sbox katValues) input 28 ≠ expected :=
  execute_ne_of_dense conditions 20 sbox katValues (by decide)

/-- **Negative control: the samples are Montgomery representatives.** Read as canonical values,
the test fails. -/
theorem kat_fails_raw_constants :
    Plonky3.permutation conditions 20 sbox
      (roundValues 20 (fun r i => (extRaw r i : F)) (fun j => (intRaw j : F))) input ≠
        expected :=
  permutation_ne_of_dense conditions 20 sbox _ (by decide)

/-- **Regression value: the pinned permutation on `0`.** Computed outside Lean by a model of the
specification; not an SP1 test vector. -/
theorem permutation_zero :
    permutation 0 =
      ![145589356, 1876041682, 1734203622, 499355069, 673349476, 595701365, 270340205, 131707822,
          1236787881, 1085405948, 2065733208, 1999012278, 2062318124, 1616707536, 324813015,
          749520722] :=
  permutation_eq_of_dense conditions 20 sbox values (by decide)

/-- **Regression value: the pinned permutation on `(0, 1, …, 15)`.** Computed outside Lean by a
model of the specification; not an SP1 test vector. -/
theorem permutation_range :
    permutation ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] =
      ![1028402160, 1336023551, 1247226230, 452505083, 576410521, 24192935, 496452173, 951188711,
          1739107831, 1383428939, 1192826830, 1741569479, 278097016, 868568656, 1450886773,
          121831630] :=
  permutation_eq_of_dense conditions 20 sbox values (by decide)

end Poseidon2.KoalaBear.Plonky3KAT

/-! ### BabyBear, `D = 7` -/

namespace Poseidon2.BabyBear.Plonky3KAT

open Plonky3 (Dense permutationDense roundValues permutation_eq_of_dense permutation_ne_of_dense
  execute_ne_of_dense)

/-- The field element `v R^{-1}`, `R = 2^32`: for `v < p`, the element whose Montgomery
representative is `v`. -/
def fromMonty (v : ℕ) : F := (v : F) * montyInverse

/-- `v * R^{-1} * R = v` in `F`; for `v < p` (`raw_lt_modulus`) this makes `v` the Montgomery
representative of `fromMonty v`. -/
theorem fromMonty_mul (v : ℕ) : fromMonty v * 2 ^ 32 = v := by
  rw [fromMonty, mul_assoc, montyInverse_mul, mul_one]

/-- `p` has `31` bits and `gcd(7, p - 1) = 1`, so `poseidon2_round_numbers_128` returns
`(8, 13)` for width `16` and `D = 7` (`p3-poseidon2` `0.2.3-succinct`
`src/round_numbers.rs:33-42`). -/
theorem round_numbers : 2 ^ 30 ≤ modulus ∧ modulus < 2 ^ 31 ∧ Nat.gcd 7 (modulus - 1) = 1 := by
  decide

/-- The raw Montgomery representatives of the test's eight external rows, in drawing order.
Regenerated outside Lean (see the module docstring); not text from any source. -/
def extRaw : Fin 8 → Fin 16 → ℕ :=
  ![![670752198, 867595173, 1121120522, 1732216065, 1777538858, 974826695, 857651441, 1509218160,
      933669702, 308743513, 1606546523, 1395707998, 1248974626, 733565087, 1614794869, 1457687568],
    ![311580733, 1735187654, 1563765150, 358422393, 615368408, 1022914986, 1745808542, 1451694789,
      1010294888, 478426997, 974777474, 836569592, 553962986, 354722588, 1099724285, 957403621],
    ![1171073730, 1314307614, 1575313895, 511348931, 1777322674, 743793854, 821769216, 365270850,
      1610545562, 1781773041, 1642480066, 968153742, 107763776, 304102504, 1048805912, 670079580],
    ![1825005418, 699322108, 372969254, 1347088819, 1017368981, 695522824, 1491107118, 1656304581,
      934311777, 1538050768, 1121275927, 1281424936, 1609172128, 302658704, 16103019, 802016690],
    ![359041126, 1491417545, 151742200, 122792040, 802809388, 437172020, 1610027373, 1217130568,
      1833171446, 60728125, 173288461, 1580136315, 1766051075, 458819359, 1495214374, 696367131],
    ![367271168, 4549961, 718747682, 1943893587, 1536582683, 1574838747, 1735444335, 848039704,
      1689611743, 173154748, 427470023, 1004172913, 782638163, 1744615017, 1082619536, 297763826],
    ![1160504957, 618979668, 1687696498, 37211066, 1790329919, 1183379851, 545339302, 1229207547,
      723170958, 1927785244, 1080767281, 1903150401, 1929310598, 95801870, 637696247, 1214340530],
    ![1722126248, 1823128363, 926128391, 210718841, 1667233644, 688337540, 129024239, 1282387121,
      2004475442, 535738304, 1985680653, 895998816, 1108547306, 776893336, 1108245527, 574331301]]

/-- The raw Montgomery representatives of the test's thirteen internal constants, drawn after
the external rows. -/
def intRaw : Fin 13 → ℕ :=
  ![1825109420, 1194870642, 1497066195, 1664793266, 1178412180, 1275811987, 764620473, 668520154,
      1778964353, 869842094, 747581376, 1519350472, 1866059985]

/-- Every sample is below `p`, as the sampler's rejection step ensures. -/
theorem raw_lt_modulus : (∀ r i, extRaw r i < modulus) ∧ ∀ j, intRaw j < modulus := by
  decide

/-- The external rows as field elements. -/
def katExternal (r : Fin 8) (i : Fin 16) : F := fromMonty (extRaw r i)

/-- The internal constants as field elements. -/
def katInternal (j : Fin 13) : F := fromMonty (intRaw j)

/-- The test's round-constant table. -/
def katValues : ℕ → State := roundValues 13 katExternal katInternal

/-- The input of `test_poseidon2_width_16_random` (`p3-baby-bear` `0.2.3-succinct`
`src/poseidon2.rs:165-170`), as canonical values. -/
def input : State :=
  ![894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
      19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913]

/-- The expected output of the test (`src/poseidon2.rs:172-177`), as canonical values. -/
def expected : State :=
  ![512585766, 975869435, 1921378527, 1238606951, 899635794, 132650430, 1426417547, 1734425242,
      57415409, 67173027, 1535042492, 1318033394, 1070659233, 17258943, 856719028, 1500534995]

/-- The runner sends the test's input to the expected output. -/
theorem kat_dense :
    permutationDense montyInverse 13 sbox katValues (Dense.ofState input) =
      Dense.ofState expected := by
  decide

/-- **The model reproduces the upstream known-answer test** (`p3-baby-bear` `0.2.3-succinct`
`src/poseidon2.rs:164-181`). -/
theorem upstream_kat : Plonky3.permutation conditions 13 sbox katValues input = expected :=
  permutation_eq_of_dense conditions 13 sbox katValues kat_dense

/-- The pinned permutation is the model of `upstream_kat` with SP1's table `values` in place of
the test's table `katValues`. -/
theorem permutation_eq_model : permutation = Plonky3.permutation conditions 13 sbox values :=
  rfl

/-- The field conditions also hold for the scale `1`. -/
theorem conditions_one : Plonky3.Conditions (1 : F) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **Negative control: the factor `R^{-1}` is needed.** With the internal layer `diag d + J`,
the test fails. -/
theorem kat_fails_unscaled :
    Plonky3.permutation conditions_one 13 sbox katValues input ≠ expected :=
  permutation_ne_of_dense conditions_one 13 sbox katValues (by decide)

/-- **Negative control: the initial external layer is needed.** -/
theorem kat_fails_skip_initial :
    Hades.execute (Plonky3.rounds conditions 13 sbox katValues) input 21 ≠ expected :=
  execute_ne_of_dense conditions 13 sbox katValues (by decide)

/-- **Negative control: the samples are Montgomery representatives.** Read as canonical values,
the test fails. -/
theorem kat_fails_raw_constants :
    Plonky3.permutation conditions 13 sbox
      (roundValues 13 (fun r i => (extRaw r i : F)) (fun j => (intRaw j : F))) input ≠
        expected :=
  permutation_ne_of_dense conditions 13 sbox _ (by decide)

/-- **Regression value: the pinned permutation on `0`.** Computed outside Lean by a model of the
specification; not an SP1 test vector. -/
theorem permutation_zero :
    permutation 0 =
      ![348670919, 1568590631, 1535107508, 186917780, 587749971, 1827585060, 1218809104, 691692291,
          1480664293, 1491566329, 366224457, 490018300, 732772134, 560796067, 484676252,
          405025962] :=
  permutation_eq_of_dense conditions 13 sbox values (by decide)

/-- **Regression value: the pinned permutation on `(0, 1, …, 15)`.** Computed outside Lean by a
model of the specification; not an SP1 test vector. -/
theorem permutation_range :
    permutation ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] =
      ![410552856, 1147418997, 535364858, 1334196174, 1968893922, 861940529, 937007407, 259610178,
          1058452787, 534763410, 1540431395, 130847742, 1250518650, 1612262570, 1379296618,
          1649520075] :=
  permutation_eq_of_dense conditions 13 sbox values (by decide)

end Poseidon2.BabyBear.Plonky3KAT

/-- info: 'Poseidon2.Plonky3.executeDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.executeDense_toState

/-- info: 'Poseidon2.Plonky3.permutation_eq_permutationDense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.permutation_eq_permutationDense

/-- info: 'Poseidon2.KoalaBear.Plonky3KAT.raw_lt_modulus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Plonky3KAT.raw_lt_modulus

/-- info: 'Poseidon2.KoalaBear.Plonky3KAT.upstream_kat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Plonky3KAT.upstream_kat

/-- info: 'Poseidon2.KoalaBear.Plonky3KAT.kat_fails_unscaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Plonky3KAT.kat_fails_unscaled

/-- info: 'Poseidon2.KoalaBear.Plonky3KAT.kat_fails_skip_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Plonky3KAT.kat_fails_skip_initial

/-- info: 'Poseidon2.KoalaBear.Plonky3KAT.kat_fails_raw_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Plonky3KAT.kat_fails_raw_constants

/-- info: 'Poseidon2.KoalaBear.Plonky3KAT.permutation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Plonky3KAT.permutation_zero

/-- info: 'Poseidon2.KoalaBear.Plonky3KAT.permutation_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.Plonky3KAT.permutation_range

/-- info: 'Poseidon2.BabyBear.Plonky3KAT.raw_lt_modulus' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Plonky3KAT.raw_lt_modulus

/-- info: 'Poseidon2.BabyBear.Plonky3KAT.upstream_kat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Plonky3KAT.upstream_kat

/-- info: 'Poseidon2.BabyBear.Plonky3KAT.kat_fails_unscaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Plonky3KAT.kat_fails_unscaled

/-- info: 'Poseidon2.BabyBear.Plonky3KAT.kat_fails_skip_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Plonky3KAT.kat_fails_skip_initial

/-- info: 'Poseidon2.BabyBear.Plonky3KAT.kat_fails_raw_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Plonky3KAT.kat_fails_raw_constants

/-- info: 'Poseidon2.BabyBear.Plonky3KAT.permutation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Plonky3KAT.permutation_zero

/-- info: 'Poseidon2.BabyBear.Plonky3KAT.permutation_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.Plonky3KAT.permutation_range
