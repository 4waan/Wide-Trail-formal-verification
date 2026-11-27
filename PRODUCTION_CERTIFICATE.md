# Concrete obligations and the pinned Poseidon2 certificates

This certificate establishes particular mathematical properties of an executable
permutation. Every listed property has a Lean proof. A premise in a generic
theorem is not counted as a discharged property of the concrete instance.

## AES S-box

`Algebra/AESSbox.lean` defines inversion followed by the FIPS 197 binary affine
map with constant `0x63`, an executable inverse, and a proof of bijectivity.
`Differential/Polynomial.lean` bounds inversion's differential count by four:
apart from inputs `0` and `-a`, a differential solution is a root of a nonzero
quadratic. The root bound is structural and works over any finite field.

`Differential/AESConcrete.lean` transports this bound through the affine map,
proves that four is attained, and discharges both S-box hypotheses in the
4-, 10-, 12-, and 14-round independent-key trail bounds. The exponents remain
150, 330, 450, and 480. These model the existing repeated AES linear layer and
independent round keys, not the real AES key schedule or a differential hull.

Reference: [NIST FIPS 197](https://csrc.nist.gov/pubs/fips/197/final), SubBytes.

## HADES connection

`Hades/Counting.lean` factors the exact masked differential count, including the
identity-coordinate equality constraints, and proves

```text
diffCount(masked S-box layer, a, b)
  <= u ^ sboxWeight(mask, a) * q ^ (width - sboxWeight(mask, a)).
```

`Differential/Scheduled.lean` proves the product formula for round-specific
linear and nonlinear maps by counting all independent round-key vectors.
`Hades/Probability.lean` derives a support-correct trail from a nonzero count,
applies the full outer-block bound, and obtains the corresponding exact integer
probability inequality. Fixed additions are retained in the round definition.
An additional independent uniform key per round is the sample space.

The same files keep the ratio `|K| / u` per charged S-box exact instead of rounding it
down to a whole number of bits: for `A` charged S-boxes,
`keyCount * |K|^A <= u^A * N`, where `N` is the number of key sequences
(`hades_probability_exact`, `hades_probability_with_middle_exact`), and
`mul_le_of_ratio` turns such a ratio into a power of two.

`Hades/Hull.lean` bounds a differential, the sum over all trails from one input
difference to one output difference, in the same sample space: if two adjacent full
rounds have S-boxes of uniformity at most `u` and the linear layer of the first has
branch number at least `B`, the key-averaged probability of every differential with a
nonzero input difference is at most `(u / |K|)^(B - 1)`
(`diffKeyCount_bound_of_two_full_rounds`; `hades_differential_bound` for the first two
rounds of a HADES schedule). Only those two rounds are charged; the other rounds enter
only through bijectivity.

`Hades/Dimension.lean` concerns the differences that stay inactive through `r`
consecutive partial rounds with one S-box coordinate `i0`. For an internal layer
`c • (diag d + J)` with `c ≠ 0`, no nonzero difference stays inactive through `width`
consecutive partial rounds exactly when the diagonal entries `d i`, `i ≠ i0`, are
pairwise distinct (`Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff`), and under that
condition those differences form a space of dimension exactly `width - r` for
`r <= width` (`Hades.finrank_inactiveSpace_diagPlusOnes`).

## Pinned BN254 instance

The first instance is the reference BN254 width-three Poseidon2 permutation.
The two 31-bit-field configurations SP1 uses for its main proof system have their
own section below. The BN254 parameters are:

- Prime modulus: `21888242871839275222246405745257275088548364400416034343698204186575808495617`.
- Width three, S-box `x^5`, four full rounds, 56 partial rounds, four full rounds.
- Partial S-box coordinate zero.
- Initial external mixing, then pre-addition rounds and their respective mixing.
- External matrix `[[2,1,1],[1,2,1],[1,1,2]]`.
- Internal matrix `[[2,1,1],[1,2,1],[1,1,3]]`.
- All 192 constants copied in their original 64-by-3 layout, including zero
  entries outside the partial-round S-box coordinate.

Immutable source: [HorizenLabs/poseidon2 at 055bde3f4782731ba5f5ce5888a440a94327eaf3](https://github.com/HorizenLabs/poseidon2/tree/055bde3f4782731ba5f5ce5888a440a94327eaf3).
Files below are relative to `plain_implementations/src/`:

- `poseidon2/poseidon2_instance_bn256.rs`, SHA-256
  `7b34cc6574424ea4ea56af1a8b568f99c449e092ceaa372e5226c4308937e7ac`.
- `poseidon2/poseidon2.rs`, SHA-256
  `09e1e033ca02ca9c136510cb4ffc619d4dc869b7cc97b0c3ee06152b1793360c`.
- `poseidon2/poseidon2_params.rs`, SHA-256
  `b804a9d026be54fbcf9d7004231acc87557555cecaf9b4b512563583bbab6ad4`.
- `fields/bn256.rs`, SHA-256
  `9d3468d9a36b0e4d6880c8be79ba0bea329bbf35cc49571b83415e130296bc29`.

## Certified claims

`Poseidon2/BN254Primality.lean` proves primality with Lucas certificates. Their
factorizations and modular exponentiations are kernel-checked. The certificate
generator and its factorization library are outside the trust boundary.

`Poseidon2/BN254.lean` proves the power S-box bijective using an explicit inverse
exponent, proves differential uniformity at most four from a quartic root bound,
proves external mixing MDS, and supplies explicit inverses for both linear maps.
The complete permutation is bijective, and every distinct input pair incurs at
least 16 active S-box applications in the outer rounds. No S-box, primality,
matrix, or branch-number premise remains for these concrete results.

`Poseidon2/BN254Middle.lean` charges the 56 internal rounds as well. No nonzero
difference stays off the S-box coordinate through three consecutive partial rounds
(`internal_inactive_trivial`), and some nonzero difference stays inactive through two
(`internal_inactive_two_nontrivial`), so the window cannot be shortened. Each of the
eighteen disjoint three-round windows therefore applies the S-box to a nonzero
difference, so every distinct input pair incurs at least 34 active S-box applications
(`activity_with_partial`). This is a pigeonhole lower bound. It is not claimed to be
attained.

The internal matrix is `diag (1, 1, 2) + J` (`internal_toLinearMap_eq`), and its
diagonal entries off coordinate zero, `1` and `2`, are distinct
(`internalDiag_injOn`). The criterion `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff`
therefore proves the three-round statement a second time
(`internal_inactive_trivial_by_criterion`), and by
`Hades.finrank_inactiveSpace_diagPlusOnes` the differences that stay inactive through
`r <= 3` consecutive partial rounds form a space of dimension exactly `3 - r`
(`finrank_internal_inactive`).

The independently keyed variant has individual-trail probability at most
`2^(-4016)`, since each charged S-box costs at least 251 bits in that sample
space. The theorem retains the original round-count arithmetic in its type;
`probability_exponent` proves that its exponent is 4016. This avoids conversion
expanding the enormous key space. This statement does not concern the
probability of a trail under the fixed public constants alone.

With the internal rounds charged, the same independently keyed trail bound becomes
`2^(-8534)` (`independent_key_probability_with_partial`, with the exponent
evaluated by `probability_exponent_with_partial`). The sample space and the
caveats above are unchanged. Both exponents are far past any attack threshold, so
the larger one completes the accounting rather than changing a security conclusion.

The whole-bit exponents charge 251 bits per S-box, from `4 * 2^251 <= p`. Keeping
the ratio `p / 4` exact for each of the 34 charged S-boxes gives
`keyCount * p^34 <= 4^34 * |F^3|^64` for every nonzero trail
(`independent_key_probability_exact`), and from it the exponent 8554
(`independent_key_probability_sharp`, with `sharp_exponent_bound`).
`BN254Checks.lean` shows that `2^8555 * 4^34 <= p^34` fails
(`Checks.sharp_exponent_succ_fails`), so 8554 is the largest exponent this
arithmetic gives. It is still an upper bound on the key-averaged probability of one
trail, in the same sample space, and it is not claimed to be attained. No exact-ratio
form of the 16-S-box bound `independent_key_probability` is stated.

`BN254Middle.lean` also bounds a differential, the sum over all trails from a nonzero
input difference `a` to an output difference `b`, in the same additional-independent-key
model. Over the 64 rounds that follow the initial external layer, the number of key
sequences under which `(x, x + a)` reaches the difference `b`, times `p^3`, is at most
`4^3` times the number of all key sequences (`independent_key_differential_exact`);
times `2^754` it is at most that number (`independent_key_differential_sharp`), and
`2^755 * 4^3 <= p^3` fails (`Checks.differential_sharp_exponent_succ_fails`). Only
three S-boxes of the first two external rounds are charged, one fewer than the branch
number four (`external_branch`); the other rounds enter only through bijectivity. This
is the key-averaged differential in that model. It is not a statement about the
permutation with its fixed constants or about any one key:
`Differential/Checks/Hull.lean` exhibits a toy cipher whose differential, with both
keys fixed to zero, exceeds the corresponding bound
(`Scheduled.HullChecks.toy_fixed_exceeds`).

`Poseidon2/BN254Checks.lean` checks all 64 transitions of a supplied execution
trace and proves the pinned upstream `[0,1,2]` known-answer vector. A finite
trace is checked locally before induction connects it to the executable model.

`Poseidon2/Checks/BN254SP1.lean` proves a second vector, from SP1. SP1 6.10.0
runs this permutation as `OuterPerm` for its outer recursion, wrap and SNARK
stages (`sp1-primitives` 6.10.0 `src/lib.rs:36-38`, `slop-bn254` 6.10.0
`src/lib.rs:32-57`). Its 192 constants were compared entry by entry, outside Lean,
with `slop-bn254`'s `src/poseidon2_rc.rs` and with the gnark chip's `constants.go`.
`sp1_gnark_vector` proves the output that SP1's gnark chip test expects for input
`(0, 0, 0)` (`sp1-recursion-gnark-ffi` 6.10.0,
`go/sp1/poseidon2/poseidon2_test.go:37-47`). The certificate covers the
permutation only, not the sponge, compression function or challenger SP1 builds
on it.

`Poseidon2/BN254Execution.lean` provides a materialized three-coordinate runner.
Its refinement theorem proves equality with every intermediate specification
state for all inputs and round counts. This makes the executable comparison
practical without changing the mathematical permutation.

## SP1 width-sixteen instances

SP1's main proof system hashes with a width-sixteen Poseidon2 permutation built by
the Plonky3 code: over KoalaBear in SP1 6.10.0 and over BabyBear in SP1 5.2.4.
`Poseidon2/Plonky3.lean` models that permutation once, over any field;
`Poseidon2/KoalaBear.lean` and `Poseidon2/BabyBear.lean` fix every parameter and
discharge every hypothesis by `decide`.

### Sources

All sources are crates.io archives. Each archive's SHA-256 matched the checksum in
the crates.io index, and line references in the Lean docstrings are to these
archives.

| Crate | SHA-256 of the `.crate` archive |
|---|---|
| `sp1-primitives` 6.10.0 | `f2ad891be0e48ab9ca110486f122cf799a707e5ca327a75669cfc2792b086882` |
| `slop-koala-bear` 6.10.0 | `627eb3ed4c0918f2dd2e70d2a1d312049ec3d2aa57fa0f7dbe2c3d9cd94993e4` |
| `p3-koala-bear` 0.4.3-succinct | `3a9683cd0ef68100df7c62490533047bcf19c04c4a0fa1efc9d7c1e03e31f6b3` |
| `p3-poseidon2` 0.4.3-succinct | `522986377b2164c5f94f2dae88e0e0a3d169cc6239202ef4aeb4322d60feffd0` |
| `sp1-recursion-gnark-ffi` 6.10.0 | `e56340adcfa47da2f24dde5da6b6bfd25bb3a80b3c9deb3b8ad6a518effa6b7f` |
| `sp1-primitives` 5.2.4 | `7e69a03098f827102c54c31a5e57280eb45b2c085de433b3f702e4f9e3ec1641` |
| `sp1-stark` 5.2.4 | `0e99d1cc89ba28fc95736afb1e6ad22b9eb689e95a1dbb29cf0e9d1fa4fc2a5c` |
| `p3-baby-bear` 0.2.3-succinct | `7521838ecab2ddf4f7bc4ceebad06ec02414729598485c1ada516c39900820e8` |
| `p3-poseidon2` 0.2.3-succinct | `7da1eec7e1b6900581bedd95e76e1ef4975608dd55be9872c9d257a8a9651c3a` |

The permutation code of `p3-poseidon2` is byte-identical in the two versions, so
SP1 5.2.4 and 6.10.0 share one permutation skeleton.

### Parameters

| | KoalaBear (SP1 6.10.0) | BabyBear (SP1 5.2.4) |
|---|---|---|
| Prime | `2^31 - 2^24 + 1 = 2130706433` | `2^31 - 2^27 + 1 = 2013265921` |
| S-box | `x^3` | `x^7` |
| Rounds | 4 full, 20 partial, 4 full | 4 full, 13 partial, 4 full |
| `R^{-1}` for `R = 2^32` | `1057030144` | `943718400` |
| Round constants | `RC16`, 28 rows | rows 0–20 of `RC_16_30`, selected as the code does |

Both use the same layers. The external layer is the block circulant
`circ(2 M4, M4, M4, M4)` with `M4 = circ(2, 3, 1, 1)`, and is proved equal to a
transcription of the code's `mds_light_permutation`. The internal layer is
`x_i ↦ R^{-1} (d_i x_i + ∑_j x_j)` with `d = (-2, 1, 2, 4, …, 2^13, 2^15)`. This is
the field-level meaning of the code's Montgomery arithmetic; the Montgomery
representatives themselves are not modelled. Partial rounds add a constant and
apply the S-box on coordinate zero only.

For KoalaBear, the partial rows of `RC16` are zero outside column zero, which is
proved (`partial_constants_zero`). For BabyBear, the code takes column zero of rows
4 to 16 of `RC_16_30` as the partial constants and rows 0–3 and 17–20 as the full
rounds; the other columns of rows 4 to 16 are nonzero but never read. The Lean
table zeroes them, and `rounds_apply_partial` shows each partial round is then the
code's round. The tables were checked against the crate sources outside Lean.

### Certified claims

Shared, from `Plonky3.lean`, for every constant table: the permutation is bijective;
the external layer has branch number at least 8 whenever `2, 3, 5, 7, 11, 17` are
nonzero; and, for a nonzero scale and `2 ≠ 0`, the internal layer is invertible
exactly when `81917 = 11^2 · 677` is nonzero. No nonzero difference stays inactive
through sixteen consecutive partial rounds with `diag d + J` exactly when the fifteen
diagonal entries off coordinate zero are pairwise distinct in the field
(`inactiveSpace_sixteen_eq_bot_iff`); under that condition exactly `16 - r` dimensions
of differences stay inactive through `r <= 16` consecutive partial rounds of the
code's internal layer (`finrank_inactiveSpace_internal_eq`). The trail bounds are also
stated as exact ratios (`independent_key_probability_exact`,
`independent_key_probability_with_middle_exact`), and the key-averaged differential is
bounded over the first two full rounds (`independent_key_differential_exact`): seven
S-boxes are charged, one fewer than the branch number 8, and the partial rounds and the
other full rounds are not charged.

KoalaBear:

- Primality by Lucas certificates (`KoalaBearPrimality.lean`).
- `x^3` is a bijection with an explicit inverse exponent, and its differential
  uniformity is at most 2 (`sbox_uniform`). It is exactly 2: `x^3` is not
  differentially 1-uniform (`Checks.sbox_not_uniform_one`).
- The external layer's branch number is exactly 8: at least 8
  (`external_isBranchBound`), and a difference of weight four has an image of weight
  four (`Checks.external_not_branch_nine`).
- No nonzero difference stays off the S-box coordinate through sixteen consecutive
  partial rounds (`internal_inactive_trivial`, a Krylov certificate checked by
  `decide`), and some difference does through fifteen
  (`Checks.inactive_fifteen_ne_bot`), so the window is exactly 16. The explicit
  difference `Checks.witness15` stays inactive through fifteen consecutive partial
  rounds with `diag d + J` (`Checks.witness15_mem`) and not through sixteen
  (`Checks.witness15_not_mem_sixteen`). The sixteen-round statement is proved a second
  time, with no table, by the diagonal criterion: the diagonal entries off coordinate
  zero are pairwise distinct in the field (`diag_injOn`), which gives
  `internal_inactive_trivial_by_criterion`. Exactly `16 - r` dimensions of differences
  stay inactive through `r <= 16` consecutive partial rounds (`finrank_inactive_eq`).
- Every distinct input pair incurs at least 33 active S-box applications: 32 in
  the full rounds and one from the twenty partial rounds (`activity`).
- The independently keyed trail bound has exponent 957 (`independent_key_probability`,
  `probability_exponent`): 29 bits per charged S-box, the largest whole number with
  `2 * 2^29 <= p` (`Checks.thirty_too_large`). Keeping the ratio `p / 2` exact gives
  `keyCount * p^33 <= 2^33 * |F^16|^28` for every nonzero trail
  (`independent_key_probability_exact`) and the exponent 989
  (`independent_key_probability_sharp`, with `sharp_exponent_bound`);
  `2^990 * 2^33 <= p^33` fails (`Checks.sharp_exponent_succ_fails`), so 989 is the
  largest exponent this arithmetic gives.
- The key-averaged differential over the 28 rounds that follow the initial external
  layer satisfies `diffKeyCount * p^7 <= 2^7 * |F^16|^28` for every nonzero input
  difference (`independent_key_differential_exact`), hence the exponent 209
  (`independent_key_differential_sharp`); `2^210 * 2^7 <= p^7` fails
  (`Checks.differential_sharp_exponent_succ_fails`).

BabyBear:

- Primality by a Lucas certificate (`BabyBearPrimality.lean`).
- `x^7` is a bijection with an explicit inverse exponent, and its differential
  uniformity is at most 6 (`sbox_uniform`). It is exactly 6: one differential has six
  solutions (`Checks.sbox_not_uniform_five`). The checks show `x^3` and `x^5` are not
  permutations of this field (`Checks.cube_not_injective`,
  `Checks.fifth_not_injective`).
- The external layer's branch number is exactly 8 (`external_isBranchBound`,
  `Checks.external_not_branch_nine`).
- Every distinct input pair incurs at least 32 active S-box applications, all
  counted in the full rounds (`activity`). The independently keyed trail bound has
  exponent 896 (`independent_key_probability`, `probability_exponent`): 28 bits per
  charged S-box, the largest whole number with `6 * 2^28 <= p`
  (`Checks.probability_margin_sharp`). Keeping the ratio `p / 6` exact gives
  `keyCount * p^32 <= 6^32 * |F^16|^21` for every nonzero trail
  (`independent_key_probability_exact`) and the exponent 906
  (`independent_key_probability_sharp`, with `sharp_exponent_bound`);
  `2^907 * 6^32 <= p^32` fails (`Checks.sharp_exponent_succ_fails`), so 906 is the
  largest exponent this arithmetic gives.
- The key-averaged differential over the 21 rounds that follow the initial external
  layer satisfies `diffKeyCount * p^7 <= 6^7 * |F^16|^21` for every nonzero input
  difference (`independent_key_differential_exact`), hence the exponent 198
  (`independent_key_differential_sharp`); `2^199 * 6^7 <= p^7` fails
  (`Checks.differential_sharp_exponent_succ_fails`).
- The thirteen partial rounds add nothing to this count. The differences that stay
  off the S-box coordinate through all thirteen form a space of dimension exactly 3
  (`finrank_partial_inactive`; `three_le_finrank_partial_inactive` is the lower bound
  from rank–nullity), and there are input pairs whose difference reaches no S-box in
  any partial round (`exists_pair_partial_free`). This follows from having fewer
  partial rounds than the width. It is not an attack: such pairs still incur the 32
  S-boxes of the full rounds. With the same internal layer, no nonzero difference
  would stay inactive through sixteen consecutive partial rounds (`inactive_sixteen`,
  by the diagonal criterion with `diag_injOn`; `Checks.inactive_sixteen`, by a Krylov
  certificate for `diag d + J`). Exactly `16 - r` dimensions of differences stay
  inactive through `r <= 16` consecutive partial rounds (`finrank_inactive_eq`), so
  with `r = 15` some nonzero difference does stay inactive through fifteen
  (`Checks.inactive_fifteen_ne_bot` states this for `diag d + J`). The window is
  exactly 16 here as well, and every window `w` that satisfies the hypothesis of the
  window theorem gives `13 / w = 0` (`partial_window_term_eq_zero`).
- Each round of the schedule is the code's round with the selected constants
  (`rounds_apply_prefix`, `rounds_apply_partial`, `rounds_apply_suffix`).

Every statement above about activity, trails or differentials also has a `_general`
form for every round-constant table (`activity_general`,
`independent_key_probability_general`, `independent_key_probability_exact_general`,
`independent_key_probability_sharp_general`,
`independent_key_differential_exact_general`,
`independent_key_differential_sharp_general`).

The same sample-space caveats as for BN254 apply to every exponent above. The trail
exponents bound one trail, and the differential exponents the key-averaged
differential, both in the model with an additional independent uniform key per round;
neither is a statement about the permutation with its fixed constants or about any one
key. The activity counts are lower bounds and are not claimed to be attained. The
exactness checks concern the uniformity, the branch number and the window that the
bounds use, not the counts or the exponents themselves.

### Structure of the linear layers

These are facts about the two linear layers alone, from `Plonky3.lean` and
`Algebra/Transpose.lean`, over every field satisfying the stated hypotheses. None is a
statement about whole rounds, the S-box or an attack.

- States whose four blocks of four coordinates sum to zero form a subspace of
  dimension 12 (`blockSumZeroFlat`, `finrank_blockSumZeroFlat`). Under `35 ≠ 0` the
  external layer equals `M4` applied to each block separately, with no mixing between
  blocks, exactly on this subspace (`external_eq_mat4Blocks_iff`), and a state lies in
  the subspace exactly when its image does (`external_mem_blockSumZeroFlat_iff`). Over
  every commutative ring, the position sums of the output of the code's
  `mds_light_permutation` are 5 times `M4` applied to those of the input
  (`positionSums_mdsLight`). The S-box layer of a full round acts on every coordinate
  and need not keep a state in this subspace. The subspace is singled out because
  recent round-skipping work on Poseidon2 (IACR ePrint 2026/306) exploits the structure
  of the linear-layer matrices; no claim is made about which properties that work uses,
  and its authors state that their attacks do not mean that the primitive falls short of
  its claimed security level.
- The transpose of the external layer is `circ(2 M4ᵀ, M4ᵀ, M4ᵀ, M4ᵀ)`
  (`external_dotProduct`), and it has branch number at least 8 under the same
  hypothesis as the layer (`external_transpose_isBranchBound`). `M4ᵀ = circ(2, 1, 1, 3)`
  is MDS under exactly the hypothesis that makes `M4` MDS
  (`Poseidon2.m4_transpose_isMDS_iff`). The internal layer is its own transpose
  (`internal_dotProduct`). If the linear branch number of a map is taken to be the
  differential branch number of its transpose, which is a definition here and not a
  proved statement about correlations, these bounds carry over to linear branch
  numbers. No correlation, linear trail, linear hull or linear-attack bound is proved.

### Execution checks

No published known-answer vector exists for either SP1 permutation with its pinned
constants. The checks therefore use two weaker kinds of evidence:

- Upstream crate vectors, with each test's own round constants.
  `Checks/Plonky3KAT.lean` proves that the generic model, with each instance's scale,
  S-box and round count, sends the input of `test_poseidon2_width_16_random` to that
  test's expected output, for `p3-koala-bear` 0.4.3-succinct (`src/poseidon2.rs:174-191`,
  `KoalaBear.Plonky3KAT.upstream_kat`) and for `p3-baby-bear` 0.2.3-succinct
  (`src/poseidon2.rs:164-181`, `BabyBear.Plonky3KAT.upstream_kat`). The tests' constants
  come from a seeded random generator and were regenerated outside Lean by an emulation
  of that generator. No Rust code was run; the evidence that the emulation is right is
  that both expected outputs, copied from the crate sources, are reproduced. Negative
  controls show that the vectors are not reproduced without the factor `R^{-1}`
  (`kat_fails_unscaled`), without the initial external layer (`kat_fails_skip_initial`),
  or with the raw samples read as canonical values (`kat_fails_raw_constants`). This
  validates the layers, the S-box and the schedule, but not the pinned tables.
  `Checks/KoalaBear.lean` also checks the KoalaBear vector round by round
  (`Checks.upstream_kat`).
- For both instances, the output for input zero with the pinned constants matches a
  value computed by an outside model of the code (`Checks.zero_permutation`,
  `Checks.permutation_zero`), and `Checks/Plonky3KAT.lean` checks input zero again and
  input `(0, 1, …, 15)` (`Plonky3KAT.permutation_zero`, `Plonky3KAT.permutation_range`).
  These are regression values, not upstream vectors and not outputs of SP1.

`Poseidon2/Plonky3Execution.lean` provides the materialized runner these checks
evaluate: every coordinate is a named field, every layer is written out coordinate by
coordinate, and `apply_mat4` keeps the code's addition chain. It is proved equal to the
specification for every scale, S-box, constant table, number of partial rounds, input
and round count (`Plonky3.executeDense_toState`,
`Plonky3.permutation_eq_permutationDense`).

KoalaBear's diagonal is also checked against the gnark recursion chip
(`Checks.sp1Diag_eq_gnark`).

## Pico and OpenVM width-sixteen instances

Two more deployed permutations are built by the same Plonky3 code, but with a different
internal layer from SP1's. `Poseidon2/Plonky3.lean` therefore also states the model with the
diagonal `d` and the scale `c` as parameters (`Plonky3.Diag`). Its hypotheses are collected in
`Diag.Conditions d c`: `35 ≠ 0`, every `d i ≠ 0`, `1 + ∑ 1/d i ≠ 0` and `c ≠ 0`. The SP1
permutations are the case `d = sp1Diag`, `c = R⁻¹`, and their statements are unchanged.
`Poseidon2/PicoKoalaBear.lean` and `Poseidon2/OpenVMBabyBear.lean` fix every parameter and
discharge every hypothesis by `decide`.

### Sources

| Pin | Value |
|---|---|
| Pico | `brevis-network/pico` tag `v3.2.0`. The tag was not resolved to a commit; the SHA-256 of each file read was recorded outside Lean. |
| Pico's Plonky3 | the fork `brevis-network/Plonky3` at `da6ca12c71912ec213d3c5af68b14509d2099bc3`, crate version 0.5.4. Each fork file cited is byte-identical to the crates.io 0.5.4 file. `koala-bear/src/poseidon2.rs` has SHA-256 `dd37c0c35e191aac6a4f23149ff8c923d1dfdb4a119d006e1a573fadc2866143`. |
| OpenVM | `openvm-org/openvm` tag `v2.1.0`, commit `05f3b73e7294fbb6d38155abafc98f1fe2bcfb73`; `openvm-org/stark-backend` tag `v2.1.0`, commit `a6b4761ad9a098f3a166740d22ad60b96400cd65`. |
| `p3-baby-bear` 0.4.3 | `.crate` SHA-256 `3a1a49f4d9c8b8cbdab61e25d9de1b78b3c8347dd2fb88b11d990b3efa8cdd3a`, equal to OpenVM's `Cargo.lock` checksum. |
| `p3-monty-31` 0.4.3 | `c9fe0be661891af1f703ceaf57334fcbd540804988984dc2b500dd99740e7c81` (`Cargo.lock`) |
| `p3-poseidon2` 0.4.3 | `2c6fc2368447576283f8b3849a36095017f25addf06eab9e33b0ce7f96b0b99d` (`Cargo.lock`) |
| Plonky3 `v0.8.0` (OpenVM's vector) | commit `a21e3ed42905040ad49c519e402f018381c12d0c`; `baby-bear/src/poseidon2.rs` has SHA-256 `94dd94e267e66922104010624f42ba7836805dc2fafe7482d684cd2e042a7327`, the same as the crates.io 0.8.0 file. |

### Parameters

| | Pico KoalaBear (v3.2.0) | OpenVM BabyBear (v2.1.0) |
|---|---|---|
| Field, S-box, rounds | those of SP1's KoalaBear: `x^3`, 4 + 20 + 4 | those of SP1's BabyBear: `x^7`, 4 + 13 + 4 |
| External layer | `circ(2 M4, M4, M4, M4)`, as for SP1 | the same |
| Internal diagonal | `(-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24)` | `(-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27)` |
| Scale | 1 (no `R⁻¹`) | 1 (no `R⁻¹`) |
| `1 + ∑ 1/d i` | `-14` | `-2` |
| Round constants | Plonky3's KoalaBear tables, equal entry by entry to SP1's `RC16` (`Checks.values_eq_sp1`) | HorizenLabs' `RC16` as `p3-baby-bear` 0.4.3 selects it (`Checks.values_eq_rc16`) |

Each internal layer is proved equal to a transcription of the code's
`internal_layer_mat_mul` (`internalCode_eq`); OpenVM's is also proved equal to its AIR's
layer (`internalAir_eq`). The transcriptions read `halve` and `div_2exp_u64(k)` as division of
the field element by `2` and `2^k`, which is the field-level meaning of the Montgomery code.
The Montgomery representatives themselves are not modelled.

### Certified claims

Each claim has no remaining premise, and the `_general` forms hold for every round-constant
table.

- Bijectivity; each round equals the code's round with the code's constants.
- No nonzero difference stays inactive through sixteen consecutive partial rounds, because
  the diagonal entries off coordinate 0 are pairwise distinct (`diag_injOn`). Exactly `16 - r`
  dimensions stay inactive through `r ≤ 16` rounds (`finrank_inactive_eq`).
- Pico: at least 33 charged S-boxes per distinct input pair. The trail exponent is 957, or
  989 with the exact ratio, and the two-round differential exponent is 209. These are the
  numbers of SP1's KoalaBear instance, since they depend only on the field, the uniformity,
  the branch number, the window and the round numbers.
- OpenVM: at least 32. The trail exponent is 896, or 906 with the exact ratio, and the
  two-round differential exponent is 198. The thirteen partial rounds add nothing: exactly 3
  dimensions of differences stay inactive through them (`finrank_partial_inactive`), and the
  window term is zero for every window the criterion allows (`partial_window_term_eq_zero`).

### Execution checks

Unlike the SP1 instances, both have a known-answer vector with the deployed constants. Both
are proved by `decide` on the runner `Plonky3.Diag.permutationDense` and transferred to the
specification.

- Pico (`Checks.upstream_kat`): `test_default_koalabear_poseidon2_width_16` of the fork
  (`koala-bear/src/poseidon2.rs:524-542`). Pico itself asserts the same pair against its host
  permutation and its AIR gadget (`vm/src/primitives/poseidon2_kat.rs:98-107`, asserted at
  `:121` and `:125`).
- OpenVM (`Checks.upstream_kat`): `test_default_babybear_poseidon2_width_16` of Plonky3
  `v0.8.0` (`baby-bear/src/poseidon2.rs:598-616`). The test is not in the 0.4.3 that OpenVM
  pins. Its tables equal 0.4.3's, and the permutation code was compared between the two
  versions outside Lean.
- Both: the seeded-random test of the same crate version (`Checks.rng_kat`), with the
  constants regenerated as for `Checks/Plonky3KAT.lean`, and regression values. For Pico, the
  input `(0, 1, …, 15)` is a value Pico pinned from its own implementation.
- Negative controls. Each of the following fails the vector:
  - Pico: SP1's permutation, the factor `R⁻¹`, skipping the initial layer, and the constants
    read as Montgomery representatives.
  - OpenVM: SP1's internal layer, SP1's diagonal without `R⁻¹`, the factor `R⁻¹`, skipping
    the initial layer, the constants read as Montgomery representatives, and one internal
    constant increased by one.

The checks repeat the cheap exactness facts of the SP1 checks: the uniformity, the branch
number 8, the window 16, and that each sharp exponent plus one fails. So these modules stay
in the default library. Each peaks at about 2.5 to 2.7 GB.

## Boundary of the certificate

These boundaries apply to every instance above. The certificate does not prove
that the selected round counts provide a claimed security level against every
attack. The internal-round count is a window argument giving a lower bound on
activity; it does not prove absence of subspace trails, algebraic attack
resistance, sponge indifferentiability, collision or preimage resistance, Rust
machine-code equivalence, AIR equivalence, or zkVM soundness. The
inactive-dimension and criterion results concern only the differences that avoid
the partial-round S-box coordinate, not subspace trails in general. The trail and
differential exponents are upper bounds on probabilities averaged over an
additional independent uniform key per round; the differential bounds charge only
the first two full rounds, and none of these results establishes, for the
permutation with its fixed constants, the Poseidon designers' criterion that every
differential has probability at most `p^(-t)`. No linear-cryptanalysis bound is
proved. Checking a reference vector is narrower than proving universal Rust
implementation equivalence. The immutable source, constants, model conventions,
and these boundaries are part of the certificate's meaning.

Every module is imported by `WideTrail` or, for the three memory-heavy check modules
(`Poseidon2/Checks/Plonky3.lean`, `KoalaBear.lean`, `BabyBear.lean`), by `WideTrailHeavy`.
The complete declaration audit in `scripts/AuditAxiomsHeavy.lean` covers both libraries,
`scripts/AuditAxioms.lean` covers the default library, and both permit only the existing
standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Independent implementation checks

An out-of-tree Python model uses full binary-polynomial reduction and exhaustive
inverse lookup for AES, and integer matrix multiplication modulo the pinned
prime for Poseidon2. It shares no Lean field, equivalence, or counting primitives.
The formalization and these checks share an author; this is not an independent
expert review of the model.

The comparisons passed for all 256 AES outputs, all 65,280 nonzero-input AES DDT
cells, all 2,500 toy masked DDT cells across four masks, 128 production permutation
outputs, and 16 production charged-activity counts. The production corpus includes
zero, modulus boundaries, sparse inputs, and deterministic multi-limb samples.
All 192 constants match the immutable source. All 30 Lucas certificates were
also checked separately with integer arithmetic.

The upstream known-answer vector changes when initial mixing is omitted, the
internal matrix is replaced, or a round constant is altered. These deliberate
mutations were detected. Production differential uniformity is a universal
quartic-root proof, not an estimate from the sampled input corpus.
