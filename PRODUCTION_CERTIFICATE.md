# Concrete obligations and the pinned Poseidon2 certificate

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

## Pinned production-sized parameter instance

The selected instance is the reference BN254 width-three Poseidon2 permutation,
not SP1's distinct BabyBear configuration. Its parameters are:

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

The independently keyed variant has individual-trail probability at most
`2^(-4016)`, since each charged S-box costs at least 251 bits in that sample
space. The theorem retains the original round-count arithmetic in its type;
`probability_exponent` proves that its exponent is 4016. This avoids conversion
expanding the enormous key space. This statement does not concern the
probability of a trail under the fixed public constants alone.

`Poseidon2/BN254Checks.lean` checks all 64 transitions of a supplied execution
trace and proves the pinned upstream `[0,1,2]` known-answer vector. A finite
trace is checked locally before induction connects it to the executable model.

`Poseidon2/BN254Execution.lean` provides a materialized three-coordinate runner.
Its refinement theorem proves equality with every intermediate specification
state for all inputs and round counts. This makes the executable comparison
practical without changing the mathematical permutation.

## Boundary of the certificate

The certificate does not prove that the selected round counts provide a claimed
security level against every attack. It does not prove absence of subspace
trails, algebraic attack resistance, sponge indifferentiability, collision or
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
