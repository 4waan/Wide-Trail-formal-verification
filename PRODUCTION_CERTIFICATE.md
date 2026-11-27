# Concrete obligations and the pinned Poseidon and Poseidon2 certificates

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

`Hades/MiddleBound.lean` replaces the window term by any proved lower bound on the S-boxes
charged in the partial rounds, in the activity bound and in the trail count
(`Hades.outer_middle_bound_of`, `Hades.hades_probability_with_middle_bound_exact`), and
`Hades/WindowRelation.lean` and `Hades/Automaton.lean` prove such bounds from finite
certificates; see [Counting more partial rounds](#counting-more-partial-rounds).

## Pinned BN254 instance

The first instance is the reference BN254 width-three Poseidon2 permutation.
The two 31-bit-field configurations SP1 uses for its main proof system, the Pico and
OpenVM permutations, the Aztec and Noir width-four permutation and Starknet's Poseidon
have their own sections below. The BN254 parameters are:

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
attained. As a lower bound it is superseded by 43 (`Poseidon2/BN254MiddleSharp.lean`; see
[Counting more partial rounds](#counting-more-partial-rounds)); the statements above are
unchanged.

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
  the full rounds and one from the twenty partial rounds (`activity`). As a lower bound this
  is superseded by 35 (`activity_middle`, in `KoalaBearMiddle.lean`; see
  [Counting more partial rounds](#counting-more-partial-rounds)).
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
  the branch number, the window and the round numbers. `PicoKoalaBearMiddle.lean` raises the
  count to 35, as for SP1 (see [Counting more partial rounds](#counting-more-partial-rounds)).
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

## Aztec and Noir BN254 width-four instance

Aztec's barretenberg and Noir's ACVM black-box solver hash with a Poseidon2 permutation of width
four over the BN254 scalar field. It has the field and the S-box `x^5` of the width-three
instance above, but different linear layers. `Poseidon2/HorizenLabsM4.lean` treats its external
matrix over every field, and `Poseidon2/AztecBN254.lean` fixes every parameter and discharges
every hypothesis by `decide`.

It is barretenberg's `Poseidon2Permutation<Poseidon2Bn254ScalarFieldParams>`, which the sponge
hash, the WASM export `poseidon2_permutation`, the world-state Merkle trees and the in-circuit
gadget instantiate, and Noir's black-box solver `poseidon2_permutation`, reached from
`std::hash::poseidon2_permutation`, through which the Aztec protocol circuits hash. The
docstring of `AztecBN254.lean` gives the line references.

### Sources

| Pin | Value |
|---|---|
| aztec-packages | `AztecProtocol/aztec-packages` tag `v1.0.0`, commit `79e9bd1698f4bba6deade8f76c676f9bbb12ff74`, and tag `v6.1.0`, commit `6595672787600ce14bb6dd0dd612b2ae6219b061`. In `v1.0.0`, `barretenberg/cpp/src/barretenberg/crypto/poseidon2/poseidon2_params.hpp` has SHA-256 `dcc6951d77e00e7e7cc9bea86ff8bd24429cf8d84d5f8255883257dfde451b78` and `poseidon2_permutation.hpp` has SHA-256 `0e931f6c21db7664ac46b18cece3d1cb5707ab0daf140af1a08062c3b0befd9a`. |
| Noir | `noir-lang/noir` tag `v1.0.0`, commit `275d3ab1a5c916c6ea73e8d6b943f685f574500c`. `acvm-repo/bn254_blackbox_solver/src/poseidon2.rs` has SHA-256 `b337e12594a8d59d097d2bd84c8e0e6f3dcd4d07a88a0735c45935bc251afa42` and `poseidon2_constants.rs` has SHA-256 `97e0985b1ecb4400ee3526c5273ee1f44a80397ef7b822e8b9924b6c123175f7`. |
| Noir vendored by aztec-packages `v1.0.0` | tag `nightly-2025-06-19`, commit `e96b40c4214967f14da5beabf2570a2b082940e7`. |
| HorizenLabs reference code | crate `zkhash` 0.2.0, `.crate` SHA-256 `4352d1081da6922701401cdd4cbf29a2723feb4cfabb5771f6fee8e9276da1c7`, equal to the crates.io index checksum. It has no BN254 width-four instance. |

The SHA-256 of each file read was recorded outside Lean. The 256 round constants and the four
diagonal entries are identical in aztec-packages `v1.0.0` and `v6.1.0`, Noir `v1.0.0` and Noir
`nightly-2025-06-19` (compared outside Lean); `v6.1.0` renames the diagonal
`internal_matrix_diagonal_minus_one`.

### Parameters

- Field and S-box: those of the width-three instance, the BN254 scalar field `Poseidon2.BN254.F`
  with its Lucas certificates, and `x ↦ x^5`. Field elements are canonical values; barretenberg's
  Montgomery form is a representation of the same element.
- Rounds: the initial external layer, then four full rounds, 56 partial rounds with the S-box on
  coordinate 0, and four full rounds. Each round adds its constants, applies the S-box layer,
  then the linear layer.
- External layer: HorizenLabs' `M4 = [[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]]`
  (`hlMat4`), row `i` giving output `i`. It is not Plonky3's `circ(2, 3, 1, 1)`.
  `AztecBN254Execution.lean` transcribes the code's addition chain and proves that it computes
  these rows (`mat4_toState`).
- Internal layer: `x_i ↦ d_i x_i + ∑_j x_j`, that is `diag(d) + J`, with no scale factor. The
  code stores `d` itself (`internalDiag`), so the diagonal entries of the matrix are `d_i + 1`.
  The array `internal_matrix` that `v1.0.0` declares, and the permutation does not read, is that
  matrix (`Checks.declaredInternalMatrix_eq`).
- Round constants: the `64 × 4` table of the parameter file, copied literally
  (`roundConstants`). The code adds only `round_constants[r][0]`, to `state[0]`, in a partial
  round; the table is zero off coordinate 0 in those rows (`partial_constants_zero`), so the
  HADES round, which adds the whole row, is the code's round (`rounds_apply_partial`).

### Certified claims

Over every field (`HorizenLabsM4.lean`): `det M4 = -64` (`hlMat4_det`); if `2 ≠ 0`, `M4` is a
linear equivalence with inverse `y ↦ 8⁻¹ • hlMat4Inv8 y` (`hlMat4Equiv`); and `M4` is MDS exactly
when `2, 3, 5, 7, 11, 13, 19, 23` are nonzero (`hlMat4_isMDS_iff`), in which case its branch
number is at least 5 (`hlMat4_isBranchBound`).

For the instance, each claim has no remaining premise, and each activity, trail and differential
statement also has a `_general` form for every round-constant table.

- Bijectivity (`permutation_bijective`).
- The external layer is MDS over BN254 (`external_mds`), with branch number exactly 5: at
  least 5 (`external_branch`), and `e_0` is sent to `(5, 4, 1, 1)` (`Checks.external_unit`,
  `Checks.external_not_branch_six`).
- The internal layer is invertible: every stored entry `d_i` is nonzero
  (`internalDiag_ne_zero`), and `1 + ∑ 1/d_i ≠ 0` (`one_add_sum_inv_ne_zero`). The stored
  entries off coordinate 0 are pairwise distinct (`internalDiag_injOn`), so no nonzero difference
  stays inactive through four consecutive partial rounds (`internal_inactive_trivial`), some
  does through three (`internal_inactive_three_ne_bot`), and exactly `4 - r` dimensions stay
  inactive through `r ≤ 4` (`finrank_internal_inactive`).
- Every distinct input pair incurs at least 20 charged S-box applications in the full rounds
  (`activity`), and at least 34 with the `56 / 4 = 14` of the partial rounds
  (`activity_with_partial`). As a lower bound, 34 is superseded by 44
  (`AztecBN254Middle.lean`; see [Counting more partial rounds](#counting-more-partial-rounds)).
- Trail bounds, for one trail with an additional independent uniform key per round:
  `keyCount * 2^5020 <= |F^4|^64` and `keyCount * 2^8534 <= |F^4|^64`, 251 bits per charged S-box
  (`independent_key_probability`, `independent_key_probability_with_partial`), and
  `keyCount * p^34 <= 4^34 * |F^4|^64` (`independent_key_probability_exact`), hence the exponent
  8554 (`independent_key_probability_sharp`). `4 * 2^252 > p` (`Checks.whole_bits_succ_fails`)
  and `2^8555 * 4^34 <= p^34` fails (`Checks.sharp_exponent_succ_fails`), so 251 and 8554 are
  the largest values this arithmetic gives.
- The key-averaged differential over the 64 rounds that follow the initial external layer
  satisfies `diffKeyCount * p^4 <= 4^4 * |F^4|^64` for every nonzero input difference
  (`independent_key_differential_exact`), hence the exponent 1006
  (`independent_key_differential_sharp`); `2^1007 * 4^4 <= p^4` fails
  (`Checks.differential_sharp_exponent_succ_fails`). Four S-boxes of the first two full rounds
  are charged, one fewer than the branch number.

### Execution checks

`AztecBN254Execution.lean` is a materialised runner written after the code's loop: the S-box as
`x * (x^2)^2`, the addition chain of `matrix_multiplication_4x4`, and the internal layer as the
sum of the coordinates followed by `state[i] * d_i + sum`. It is proved to compute the
specification for every input (`permutationDense_toState`), and `permutation_eq_of_dense` and
`permutation_ne_of_dense` carry values computed on it over to `permutation`. Every
vector below is proved by `decide` on the runner and uses the deployed constants; inputs and
outputs are copied from the sources.

- `Checks.test_vector`: input `(0, 1, 2, 3)`, `TEST_VECTOR_INPUT` and `TEST_VECTOR_OUTPUT` of the
  `v1.0.0` parameter file, checked by barretenberg's permutation test. The same pair is a bb.js
  test, Noir's "sequential small values" case, the example of Noir's documentation (coordinate
  0) and the test vector of `v6.1.0`. It was emitted by the script that generated the constants.
- `Checks.consistency_vector`: barretenberg's `ConsistencyCheck`, four copies of a 256-bit
  literal that the code reduces mod `p` (`Checks.consistency_literal_eq`). The test's comment
  says that its values were extracted from the code under test, so this vector is
  self-generated.
- `Checks.noir_vector_bbjs`: input `(1, 2, 3, 10 · 2^64)`, the bb.js test "test vectors from Noir
  should match", which gives no further provenance.
- `Checks.zkhash_zeros`, `Checks.zkhash_u128_max`, `Checks.zkhash_p_sub_one`,
  `Checks.zkhash_arbitrary`: the other four cases of Noir's solver tests. Their outputs were
  produced by the generic Poseidon2 code of `zkhash` 0.2.0 fed Noir's parameters, so they check
  the loop and the layers against a second implementation, not where the constants came from.
  The all-zero output is also the smoke test of Noir `nightly-2025-06-19`.

These are seven distinct inputs. A known-answer test checks a single input; it shows that the
model computes the output the source asserts, not that model and code agree on every input. The
sponge vectors of the same code bases are out of scope: no sponge is modelled.

Negative controls. Each of the following fails `Checks.test_vector`: the transpose of `M4` as
the external layer (`Checks.test_vector_fails_transposed`); `diag(d + 1) + J` as the internal
layer (`Checks.test_vector_fails_diag_succ`); `diag(d - 1) + J`, the reading of the stored array
as the diagonal of the matrix (`Checks.test_vector_fails_diag_pred`); and no initial external
layer (`Checks.test_vector_fails_skip_initial`).

The checks also show that the 32 full-round constants and the 56 partial-round constants at
coordinate 0 are nonzero (`Checks.full_constants_ne_zero`, `Checks.partial_constants_ne_zero`),
and that the integer matrix of `Algebra/Checks/MDS4.lean` is `hlMat4 ℤ`
(`Checks.mds4Checks_hlMat4_eq`). The axiom footprints are pinned at the end of
`Checks/AztecBN254.lean`. Each of the four modules peaks at about 2.4 to 2.7 GB.

## Starknet's Poseidon (HADES) instance

`WideTrail/Poseidon/` holds certificates for the original Poseidon, the HADES design, as opposed
to Poseidon2. Its one instance is Starknet's permutation. Unlike the instances above, it has no
linear layer before round 0, uses one matrix in the full and the partial rounds, and applies the
partial-round S-box to the last coordinate.

It is cairo-lang's `poseidon_perm`; the permutation of the Cairo VM's Poseidon builtin and of the
Poseidon builtin of the Starknet-layout STARK AIR (8 full and 83 partial rounds); the Cairo
corelib's `hades_permutation` libfunc; the permutation of the Rust stack, where
starknet-types-core wraps lambdaworks-crypto and cairo-vm and starknet-crypto hash through it;
and that of the full node pathfinder. Starknet hashes protocol objects, among them class hashes,
v3 transaction hashes and the global state root, with `poseidon_hash_many`, a sponge built on the
permutation; no sponge is modelled. The docstring of `Starknet.lean` gives the line references.

### Sources

| Pin | Value |
|---|---|
| cairo-lang | `starkware-libs/cairo-lang` tag `v0.14.0.1`, commit `66355d7d99f1962ff9ccba8d0dbacbce3bd79bf8`; `src/starkware/cairo/common/poseidon_utils.py` has SHA-256 `4ceee649f41f14bfeed28611a254676a3e4c596debaeedbfaa6b03a47e52958f`. |
| cairo-lang on PyPI | `cairo-lang-0.14.0.1.zip`, SHA-256 `d53473245f8d0d7d62d77ad5c1715959f61ce128bb369e8e7662040aabed98df`, the digest PyPI publishes. It holds byte-identical copies of `poseidon_utils.py`, `poseidon_hash.py` and `cairo_constants.py`, and does not contain the AIR file `autogenerated.cairo`. |
| Cairo corelib | `starkware-libs/cairo` tag `v2.22.0`, commit `118efdadf76745701dbf019ef9ead25b2cbea29b`. |
| pathfinder | `eqlabs/pathfinder` commit `00a1a74a90a7b8a7f1d07ac3e616be1cb39cf8f1`. |
| CryptoExperts | `CryptoExperts/poseidon` commit `68a88df9cb894fe1e0ee8b1b1b5825602c83635a`. |

| Crate | SHA-256 of the `.crate` archive |
|---|---|
| `lambdaworks-crypto` 0.13.0 | `58b1a1c1102a5a7fbbda117b79fb3a01e033459c738a3c1642269603484fd1c1` |
| `starknet-types-core` 1.0.0 | `8a12690813e587969cb4a9e7d8ebdb069d4bb7ec8d03275c5f719310c8e1f07c` |
| `cairo-vm` 4.0.0 | `48f446081a0d89517067597db438c04d1a97b58c77f26d665dca55f63e3635df` |
| `starknet-crypto` 0.8.1 | `1004a16c25dc6113c19d4f9d0c19ff97d85804829894bba22c0d0e9e7b249812` |
| `starknet-crypto-codegen` 0.3.3 | `bbc159a1934c7be9761c237333a57febe060ace2bc9e3b337a59a37af206d19f` |

Each archive's SHA-256 equals the checksum in the crates.io index. The SHA-256 of each other file
read was recorded outside Lean.

### Parameters

- Prime `p = 2^251 + 17 · 2^192 + 1 =
  3618502788666131213697322783095070105623107215331596699973092056135872020481`, cairo-lang's
  `DEFAULT_PRIME`. `Poseidon/StarkPrimality.lean` proves it prime by Lucas certificates
  (witness 3, `p - 1 = 2^192 · 5 · 7 · 98714381 · 166848103`).
- Width 3 (rate 2, capacity 1) and S-box `x^3`, a permutation since `3 d = 2 (p - 1) + 1` for
  `d = (2 p - 1) / 3`.
- Rounds: four full, 83 partial, four full, with no linear layer before round 0
  (`Hades.hadesSchedule 4 83 4 {2}`). A partial round applies the S-box to coordinate 2 only
  (`values[-1]`, the capacity cell).
- Linear layer: `M = [[3, 1, 1], [1, -1, 1], [1, 1, -2]]` in every round, row `r` giving output
  `r` (`SmallMds.dot_mod`), with `det M = 8` (`mds_det`) and inverse `adj(M) / 8`
  (`mds_symm_apply`). The `mix` of the Rust code, `t = s0 + s1 + s2` and then
  `(t + 2 s0, t - 2 s1, t - 3 s2)`, computes the same map (`mixT_eq_dotMod`). Comments at
  starknet-crypto 0.6.2 `src/poseidon_hash.rs:117` and pathfinder `poseidon.rs:9` print the last
  entry as `+2`; the code computes `-2`.
- Round constants: the `91 × 3` table `C[i][j] = sha256("Hades" ++ str(3 i + j)) mod p`
  (`roundConstants`). Every round, partial rounds included, adds all three constants of its row,
  and none of the 273 constants is zero (`Checks.values_ne_zero`). Outside Lean, a script
  recomputed all 273 entries from the SHA-256 rule, re-extracted them from four pinned tables
  (starknet-crypto-codegen 0.3.3, pathfinder, CryptoExperts, lambdaworks-crypto 0.13.0) and
  compared them with the Lean literals; all agree. Row 0 and `C[4][2]` are also constants of the
  Starknet-layout AIR (`Checks.values_zero_eq_air`, `Checks.values_four_two_eq_air`). The
  docstring of `generate_round_constant` says that the first element is `sha256('Poseidon0')`,
  but the code passes `"Hades"`; outside Lean, the `"Poseidon"` reading reproduces none of the
  published permutation vectors.
- Compressed constants: the 107 constants of lambdaworks-crypto 0.13.0's
  `OPTIMIZED_ROUND_CONSTANTS` (`compressedConstants`), read with three entries per full round and
  one, added to coordinate 2, per partial round (`compressedValues`). The same script re-derived
  them from `roundConstants` by the folding procedure of starknet-crypto-codegen 0.3.3.

### Certified claims

Each claim has no remaining premise, and each bijectivity, activity, trail and differential
statement also has a `_general` form for every round-constant table.

- The S-box has differential uniformity at most 2 (`sbox_uniform`), and 2 is attained
  (`sbox_diffCount_attained`).
- `M` is MDS (`mds_isMDS`; over `ℤ` its 19 square minors are nonzero, with prime factors among 2,
  3 and 7, `Checks.mdsInt_minors_one`, `Checks.mdsInt_minors_two`, `Checks.mdsInt_det`), with
  branch number exactly 4: at least 4 (`mds_branch`), and `e_0` is sent to `(3, 1, 1)`
  (`Checks.mds_unit`, `Checks.mds_not_branch_five`). `M = diag (2, -2, -3) + J`
  (`mds_toLinearMap_eq`).
- Bijectivity (`permutation_bijective`); each round is the code's round (`rounds_apply_full`,
  `rounds_apply_partial`).
- Every distinct input pair incurs at least 16 charged S-box applications in the full rounds
  (`activity`), and at least 43 with the `83 / 3 = 27` of the partial rounds
  (`activity_with_partial`). The diagonal entries 2 and -2 off coordinate 2 are distinct
  (`mdsDiag_injOn`), so no nonzero difference stays inactive through three consecutive partial
  rounds (`mds_inactive_trivial`), exactly `3 - r` dimensions stay inactive through `r ≤ 3`
  (`finrank_mds_inactive`), and some nonzero difference stays inactive through two
  (`mds_inactive_two_ne_bot`). As a lower bound, 43 is superseded by 57 (`StarknetMiddle.lean`;
  see [Counting more partial rounds](#counting-more-partial-rounds)).
- Trail bounds, for one trail with an additional independent uniform key per round:
  `keyCount * 2^4000 <= |F^3|^91` and `keyCount * 2^10750 <= |F^3|^91`, 250 bits per charged
  S-box (`independent_key_probability`, `independent_key_probability_with_partial`). The exact
  ratios `keyCount * p^16 <= 2^16 * |F^3|^91` (`independent_key_probability_outer_exact`) and
  `keyCount * p^43 <= 2^43 * |F^3|^91` (`independent_key_probability_exact`) give the same
  exponents 4000 (`Checks.outer_sharp_exponent_bound`) and 10750
  (`independent_key_probability_sharp`), since `p` is barely above `2^251`. `2 * 2^251 > p`
  (`Checks.whole_bits_succ_fails`), and 4001 and 10751 fail
  (`Checks.outer_sharp_exponent_succ_fails`, `Checks.sharp_exponent_succ_fails`).
- The key-averaged differential over the 91 rounds satisfies
  `diffKeyCount * p^3 <= 2^3 * |F^3|^91` for every nonzero input difference
  (`independent_key_differential_exact`), hence the exponent 750
  (`independent_key_differential_sharp`); `2^751 * 2^3 <= p^3` fails
  (`Checks.differential_sharp_exponent_succ_fails`). Three S-boxes of the first two full rounds
  are charged, one fewer than the branch number.

### The compressed schedule

Most deployed implementations do not run cairo-lang's loop: lambdaworks-crypto and the crates
built on it (starknet-types-core, starknet-crypto from 0.7.2, cairo-vm), pathfinder's
`permute_comp`, and starknet-crypto up to 0.7.1 use the 107 compressed constants. A partial round
adds one constant, to coordinate 2, and the first round of the last full block absorbs the
constants of coordinates 0 and 1 of the partial rounds, pushed forward through `M`.

`Poseidon/ConstantFolding.lean` proves, for arbitrary scheduled rounds, that such a rewriting
does not change the computed function. A masked S-box layer is the identity off its mask, so
adding a vector `e` that is zero on the mask commutes with it, and a round with constant `c' + e`
is the round with constant `c'` followed by adding `L e`, which the next round's constant can
absorb (`roundSpec_apply_add_of_eq_zero`). `execute_eq_add_of_fold` and `execute_eq_of_fold`
follow the offsets between the two schedules' states through the rounds, and
`hadesSchedule_execute_eq_of_fold` is the case of two HADES schedules that differ only in their
constants.

`Poseidon/StarknetCompressed.lean` applies it with offsets `foldOffset` computed outside Lean,
whose conditions are checked by `decide` (`foldOffset_zero`, `foldOffset_end`, `fold_mask_zero`,
`fold_next`):

- `compressedPermutation_eq`: for every input `x`, the compressed schedule computes
  `permutation x`.
- `keyed_compressed_eq`: for every key sequence `k` and every input `x`, the schedules with the
  tables `compressedValues n + k n` and `values n + k n` compute the same state after 91 rounds.
  The folding conditions involve the two tables only through their difference, which adding the
  same `k n` to both leaves unchanged.
- `keyCount_compressed_eq`: the trail count `Hades.keyCount` of the independent-key model is the
  same for both schedules, for every number of rounds, trail and input; it involves only the
  masks, S-boxes and linear layers.
- `compressed_partial_constants_zero`: the partial rows of the compressed table are zero off
  coordinate 2, which is false for the unoptimised table (`Checks.values_partial_ne_zero`). The
  two tables cannot be mixed: they differ in row 87 (`compressedValues_ne_values_87`) and at
  coordinate 2 of every partial round from 5 to 86 (`compressedValues_ne_values_partial`), and
  agree in rounds 0 to 3 and 88 to 90 (`compressedValues_eq_values_full`) and at coordinate 2 of
  round 4 (`compressedValues_eq_values_4`).

The independent-key statements of `Starknet.lean` have `_general` forms for every table, so they
also hold for the compressed table. Nothing further is stated about the differential count of
the compressed schedule.

### Execution checks

`Poseidon/StarknetExecution.lean` is a materialised runner written after cairo-lang's loop,
proved to compute the specification for every input (`permutationDense_toState`);
`permutation_eq_of_dense` and `permutation_ne_of_dense` carry values computed on it over to
`permutation`. `Checks/Starknet.lean` proves, by `decide` on the runner, the three
distinct permutation-level vectors that the sources publish, all with the deployed constants; the
compressed schedule reproduces them too (`Checks.compressed_vectors`). Inputs and outputs are
copied from the sources.

- `Checks.zero_vector`: input `(0, 0, 0)`, the expected output of pathfinder's tests of `permute`
  and `permute_comp`, which credit starkware-industries/poseidon, and, in decimal, the test
  vector of CryptoExperts (`Checks.zeroOutput_eq_cryptoexperts`).
- `Checks.lambdaworks_vector`: input `(9, 11, 2)`, `test_hades_permutation` of
  starknet-types-core 1.0.0 and of lambdaworks-crypto 0.13.0, the code that cairo-vm 4.0.0 runs
  for its Poseidon builtin. Both run the compressed table.
- `Checks.corelib_vector`: input `(1, 2, 3)`, `test_poseidon_hades_permutation` of the Cairo
  corelib, which calls the `hades_permutation` libfunc.

The 23 hash-level vectors that the same code bases publish are out of scope: no sponge is
modelled. A known-answer test checks a single input; it does not show that model and code agree
on every input.

Negative controls. Each of the following fails the vectors named:

- the partial-round S-box on coordinate 0 instead of 2: all three
  (`Checks.zero_vector_fails_sbox_first`, `Checks.lambdaworks_vector_fails_sbox_first`,
  `Checks.corelib_vector_fails_sbox_first`);
- the last entry of `M` read as `+2`, as the comments print it: all three
  (`Checks.zero_vector_fails_plus_two`, `Checks.lambdaworks_vector_fails_plus_two`,
  `Checks.corelib_vector_fails_plus_two`);
- an extra `M` in front of the rounds, a Poseidon2-style initial layer: the two nonzero vectors
  (`Checks.lambdaworks_vector_fails_initial_layer`, `Checks.corelib_vector_fails_initial_layer`);
  the zero vector cannot detect it, since `M 0 = 0` (`Checks.zero_vector_blind_to_initial_layer`);
- the unoptimised table with only the coordinate-2 constant added in the partial rounds:
  `(9, 11, 2)` (`Checks.lambdaworks_vector_fails_partial_at_two_only`);
- the table read column-major: `(9, 11, 2)` (`Checks.lambdaworks_vector_fails_transposed`).

The docstring reading of the constants, `sha256("Poseidon" ++ str(k))`, is not tested in Lean,
since it would need another 273 literals. `Poseidon/Checks/Axioms.lean` pins the axiom
footprints. Every module of `WideTrail.Poseidon` peaks at about 3.4 GB or less; the largest is
`StarknetCompressed.lean`.

## Counting more partial rounds

`Hades/MiddleBound.lean` takes a lower bound on the partial rounds as a hypothesis,
`MiddleBound A mask m μ`: every trail in the `IsTrail` model through `m` consecutive rounds with
linear map `A` and that mask, from a nonzero difference, charges at least `μ` S-boxes. The window
argument is the case `μ = m / w`. Window relations (`Hades/WindowRelation.lean`) and
forward-space automata (`Hades/Automaton.lean`) prove larger bounds from finite certificates,
checked by `decide +kernel` in files that import only the Boolean checkers
(`Hades/RelationCheck.lean`, `Hades/AutomatonCheck.lean`) and, through them,
`Mathlib.Data.ZMod.Basic`. The certificate data were computed outside Lean from the literals of
the instance files; nothing depends on how they were found, since the checks are complete.
[The HADES mechanics](MECHANICS_HADES.md#counting-more-partial-rounds) explain the argument.

The new counts are lower bounds on charged S-box applications. For BN254 width three, Aztec and
Starknet they hold for every trail in the `IsTrail` model through the whole schedule from a
nonzero difference (`isTrail_activity_middle_general`), and hence for every pair of distinct
inputs. For SP1's and Pico's KoalaBear, Lean states them for every pair of distinct inputs
(`activity_middle`, `activity_middle_general`), from the middle bound `3`, which holds for every
trail through the twenty partial rounds; no statement there covers every trail through the
whole schedule. All hold for the pinned constants and, in the `_general` forms, for every
round-constant table. As lower bounds they supersede the window counts; the earlier theorems
are unchanged.

| Instance | Partial rounds (width) | Window term | Middle bound | Charged S-boxes | Trail exponents, whole bits / exact ratio |
|---|---|---|---|---|---|
| SP1 KoalaBear | 20 (16) | `20 / 16 = 1` | 3 | 33 → 35 | 957 / 989 → 1015 / 1049 |
| Pico KoalaBear | 20 (16) | `20 / 16 = 1` | 3 | 33 → 35 | 957 / 989 → 1015 / 1049 |
| SP1 and OpenVM BabyBear | 13 (16) | `13 / 16 = 0` | 0 | 32, unchanged | 896 / 906, unchanged |
| HorizenLabs BN254, width three | 56 (3) | `56 / 3 = 18` | 27 | 34 → 43 | 8534 / 8554 → 10793 / 10818 |
| Aztec and Noir BN254, width four | 56 (4) | `56 / 4 = 14` | 24 (6 per window of 14) | 34 → 44 | 8534 / 8554 → 11044 / 11070 |
| Starknet | 83 (3) | `83 / 3 = 27` | 41 | 43 → 57 | 10750 / 10750 → 14250 / 14250 |

The exponents bound one trail in the model with an additional independent uniform key per
round, not the permutation with its fixed constants, and not a differential. The whole-bit
exponents charge 29 (KoalaBear), 28 (BabyBear), 251 (BN254) and 250 (Starknet) bits per charged
S-box; the exact ratios use the uniformities 2 (KoalaBear, Starknet), 6 (BabyBear) and 4
(BN254).

The results, by file:

- SP1 KoalaBear, `Poseidon2/KoalaBearMiddle.lean` with `Certificates/KoalaBearRelations.lean`:
  `middle_bound` for `diag d + J` and `internal_middle_bound` for the code's `R⁻¹ (diag d + J)`,
  from a window-relation certificate (a chain of length 16, four relations, the 20 single rounds
  and 190 pairs refuted); `activity_middle`; `independent_key_probability_middle`,
  `independent_key_probability_middle_exact` and `independent_key_probability_middle_sharp`.
- Pico, `Poseidon2/PicoKoalaBearMiddle.lean` with `Certificates/PicoKoalaBearRelations.lean`: the
  same statements for Pico's diagonal, whose layer has no scale factor.
- BN254 width three, `Poseidon2/BN254MiddleSharp.lean` with `Certificates/BN254Automaton.lean`:
  `middle_bound` from a 57-state automaton with start potential 2,
  `isTrail_activity_middle_general` for every trail in the `IsTrail` model, `activity_middle`, and
  the three trail bounds.
- Aztec, `Poseidon2/AztecBN254Middle.lean` with `Certificates/AztecBN254Automaton.lean`:
  `middle_bound_window` for a window of 14 rounds from a 255-state automaton with start potential
  3, `middle_bound` for the 56 partial rounds from four windows, `isTrail_activity_middle_general`,
  `activity_middle`, and the three trail bounds.
- Starknet, `Poseidon/StarknetMiddle.lean` with `Poseidon/Certificates/StarknetAutomaton.lean`:
  `middle_bound` from an 84-state automaton with start potential 2 (S-box on coordinate 2),
  `isTrail_activity_middle_general`, `activity_middle`, and the three trail bounds.
- `Poseidon2/Plonky3MiddleBound.lean` states the width-sixteen results with any middle bound for
  `diag d + J`, and `Poseidon2/Checks/MiddleBound.lean` re-derives the earlier counts 33 and 34
  and exponents 989 and 8554 through the interface.

What is sharp, and where it is shown:

- Sharp in Lean. For each of the middle bounds 3 (SP1 and Pico, for `diag d + J` and for the
  code's layer: `KoalaBear.MiddleChecks.middle_bound_not_four`,
  `internal_middle_bound_not_four`, and the same in `PicoKoalaBear.MiddleChecks`), 27 (BN254:
  `BN254.MiddleSharpChecks.middle_bound_not_twenty_eight`), 41 (Starknet:
  `Starknet.MiddleChecks.middle_bound_not_forty_two`) and 6 for a window of 14 Aztec partial
  rounds (`AztecBN254.MiddleChecks.middle_bound_window_not_seven`), an explicit trail with that
  many active rounds shows that the next value is not a middle bound; for SP1's scaled layer
  `R⁻¹ (diag d + J)` this follows via `MiddleBound.smul_iff` from the trail for
  `diag d + J`, which is not itself a trail for that layer. The totals 43 (BN254)
  and 57 (Starknet) are attained by trails in the `IsTrail` model through the whole schedule
  (`activity_attained` in `BN254.MiddleSharpChecks` and in `Starknet.MiddleChecks`), so they
  are the least over all such trails, and no argument that uses only `IsTrail` proves more.
  Each new exact exponent plus one fails (`middle_sharp_exponent_succ_fails`), and each
  whole-bit exponent is the largest for its count (`whole_bit_exponent_le`).
- Sharp only by an argument outside Lean. BabyBear's middle term 0 cannot be raised: no theorem
  states that `MiddleBound … 13 1` fails, but three dimensions of differences stay inactive
  through all thirteen partial rounds (`finrank_partial_inactive`), and for SP1 and for OpenVM
  some distinct inputs incur no charged S-box in them (`exists_pair_partial_free`); the
  difference trace of such a pair is a trail that charges nothing there.
- Computed outside Lean. For Aztec, Lean proves 24 for the 56 partial rounds and 44 in all.
  It shows that 28 is not a middle bound for the 56 rounds, by a trail with 27 active rounds
  (`AztecBN254.MiddleChecks.middle_bound_not_twenty_eight`), and exhibits a trail in the
  `IsTrail` model through the whole schedule that charges 47
  (`AztecBN254.MiddleChecks.activity_attained`). A computation outside Lean, a
  meet-in-the-middle test of the forward spaces of the first 28 partial rounds against the
  backward spaces of the last 28 (603,881,476 pairs), finds no trail through the 56 rounds with
  26 or fewer active rounds. With these trails, the least middle count would be exactly 27, and
  the least total in the `IsTrail` model exactly `20 + 27 = 47`. Nothing in Lean claims either.
- Not determined. For the width-sixteen instances only the middle term is shown sharp: the full
  rounds are still charged 32, and the least total over the whole permutation is not determined
  here. None of the counts is claimed to be the least number of S-boxes that an actual input
  pair incurs; the witness trails are trails in the `IsTrail` model, not claimed to be realised
  by input pairs or keys.

The certificate and check modules peak at about 2.1 to 3.2 GB, the largest being
`Certificates/AztecBN254Automaton.lean`.

## Boundary of the certificate

These boundaries apply to every instance above. The certificate does not prove
that the selected round counts provide a claimed security level against every
attack. The partial-round counts, from windows or from the certificates of
[Counting more partial rounds](#counting-more-partial-rounds), are lower bounds on
charged activity in the `IsTrail` model, not claimed to be attained by input pairs.
They do not prove absence of subspace trails, algebraic attack resistance, sponge
indifferentiability, collision or preimage resistance, equivalence with the Rust,
C++, Python or Cairo code or with machine code, circuit or AIR equivalence, or zkVM
soundness. The inactive-dimension and criterion results concern only the differences
that avoid the partial-round S-box coordinate, not subspace trails in general. The
trail and differential exponents are upper bounds on probabilities averaged over an
additional independent uniform key per round; the differential bounds charge only
the first two full rounds, and none of these results establishes, for the
permutation with its fixed constants, the Poseidon designers' criterion that every
differential has probability at most `p^(-t)`. No linear-cryptanalysis bound is
proved. Checking a reference vector is narrower than proving universal
implementation equivalence. The immutable source, constants, model conventions,
and these boundaries are part of the certificate's meaning.

Every module is imported by `WideTrail` or, for the three memory-heavy check modules
(`Poseidon2/Checks/Plonky3.lean`, `KoalaBear.lean`, `BabyBear.lean`), by `WideTrailHeavy`.
`scripts/check_imports.py` finds 117 modules, all reachable from the two roots: the default
library `WideTrail` builds 113 of them (its root and the 112 modules it imports, the layers
`Propagation`, `Algebra`, `Differential`, `Hades`, `Poseidon2` and `Poseidon`), and
`WideTrailHeavy` adds the three memory-heavy check modules and its own root. Every module of the
default library peaks at about 3.4 GB or less. The complete declaration audit in
`scripts/AuditAxiomsHeavy.lean` covers both libraries (8395 project declarations at this
revision), `scripts/AuditAxioms.lean` covers the default library (6251), and both permit only
the existing standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Independent implementation checks

An out-of-tree Python model uses full binary-polynomial reduction and exhaustive
inverse lookup for AES, and integer matrix multiplication modulo the pinned
prime for Poseidon2. It shares no Lean field, equivalence, or counting primitives.
The formalization and these checks share an author; this is not an independent
expert review of the model. These checks cover AES and the BN254 width-three instance; each
later instance has the execution checks described in its own section.

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
