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

`Poseidon2/BN254Middle.lean` charges the 56 internal rounds as well. The internal
matrix leaves no nonzero difference off the S-box coordinate for three consecutive
rounds (`internal_inactive_trivial`), and two rounds are not enough
(`internal_inactive_two_nontrivial`). Each of the eighteen disjoint three-round
windows therefore applies the S-box to a nonzero difference, so every distinct
input pair incurs at least 34 active S-box applications (`activity_with_partial`).
This is a pigeonhole lower bound. It is not claimed to be attained.

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

Shared, from `Plonky3.lean`: the permutation is bijective for every constant table;
the external layer has branch number at least 8 whenever `2, 3, 5, 7, 11, 17` are
nonzero; and, for a nonzero scale and `2 ≠ 0`, the internal layer is invertible
exactly when `81917 = 11^2 · 677` is nonzero.

KoalaBear:

- Primality by Lucas certificates (`KoalaBearPrimality.lean`).
- `x^3` is a bijection with an explicit inverse exponent, and its differential
  uniformity is at most 2.
- No nonzero difference stays off the S-box coordinate through sixteen consecutive
  partial rounds (`internal_inactive_trivial`, a Krylov certificate checked by
  `decide`), and some difference does through fifteen
  (`Checks.inactive_fifteen_ne_bot`).
- Every distinct input pair incurs at least 33 active S-box applications: 32 in
  the full rounds and one from the twenty partial rounds (`activity`).
- The independently keyed trail bound has exponent 957 (`independent_key_probability`,
  `probability_exponent`).

BabyBear:

- Primality by a Lucas certificate (`BabyBearPrimality.lean`).
- `x^7` is a bijection with an explicit inverse exponent, and its differential
  uniformity is at most 6. The checks show `x^3` and `x^5` are not permutations of
  this field.
- Every distinct input pair incurs at least 32 active S-box applications, all
  counted in the full rounds (`activity`). The independently keyed trail bound has
  exponent 896.
- The thirteen partial rounds add nothing to this count. The differences that stay
  off the S-box coordinate through all thirteen form a space of dimension at least 3
  (`three_le_finrank_partial_inactive`), and there are input pairs whose difference
  reaches no S-box in any partial round (`exists_pair_partial_free`). This follows
  from having fewer partial rounds than the width. It is not an attack: such pairs
  still incur the 32 S-boxes of the full rounds. With the same internal layer, no
  nonzero difference would stay inactive through sixteen consecutive partial rounds
  (`Checks.inactive_sixteen`).

The same sample-space caveats as for BN254 apply to both exponents.

### Execution checks

No published known-answer vector exists for either SP1 permutation with its pinned
constants. The checks therefore use two weaker kinds of evidence:

- KoalaBear's model reproduces the upstream `p3-koala-bear` test vector
  (`src/poseidon2.rs:174-191`) with that test's own round constants
  (`Checks.upstream_kat`). Those constants come from a seeded random generator and
  were regenerated outside Lean, so this validates the layers, S-box and schedule,
  but not the pinned table.
- For both instances, the output for input zero with the pinned constants matches a
  value computed by an outside model of the code (`Checks.zero_permutation`,
  `Checks.permutation_zero`). These are regression values, not upstream vectors.

KoalaBear's diagonal is also checked against the gnark recursion chip
(`Checks.sp1Diag_eq_gnark`).

## Boundary of the certificate

These boundaries apply to every instance above. The certificate does not prove
that the selected round counts provide a claimed security level against every
attack. The internal-round count is a window argument giving a lower bound on
activity; it does not prove absence of subspace trails, algebraic attack resistance, sponge indifferentiability, collision or
preimage resistance, Rust machine-code equivalence, AIR equivalence, or zkVM
soundness. Checking a reference vector is narrower than proving universal Rust
implementation equivalence. The immutable source, constants, model conventions,
and these boundaries are part of the certificate's meaning.

All new modules are imported by `WideTrail`. The complete declaration audit in
`scripts/AuditAxioms.lean` covers them and permits only the existing standard
axioms: `propext`, `Classical.choice`, and `Quot.sound`.

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
