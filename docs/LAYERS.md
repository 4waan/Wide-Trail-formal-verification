[WideTrail](../README.md) › [Documentation](README.md) › The proof layers

# The proof layers

What each layer of the library proves, in the order in which the layers build on each other.
The file-by-file guide is [FILES.md](FILES.md); the mechanics of each layer are in the
`MECHANICS_*.md` files that each section links to.

The library has eight layers, each importable whole: `import WideTrail.Propagation`,
`import WideTrail.Algebra`, `import WideTrail.Differential`, `import WideTrail.Hades`,
`import WideTrail.Poseidon2`, `import WideTrail.Poseidon`, `import WideTrail.Linear` and
`import WideTrail.Rijndael`. The directory names say what kind of mathematics each layer
contains. Earlier revisions used numbered directories; the import paths use the names above.

## Propagation layer

`WideTrail/Propagation/` is the abstract propagation theory: an S-box layer, a shuffle and a
mixing layer, related only by the structural properties a wide-trail cipher needs (support
preservation, diffusion optimality, a branch number). It is parametric: the branch number, the
state size and the field are parameters, so one bound covers a family of designs, AES
included. Instantiated at the AES shape, it gives `aes_four_round`/`aes128_ten_round` as an
**implication**: *given* that MixColumns has branch number `5`, four rounds force `25` active
S-boxes and the ten rounds of AES-128 force `55`. The `hmix`/`hnd` hypotheses in
`Propagation/AES.lean` are exactly that "given".

The state is rectangular, `Fin rows × Fin cols`, not square, so the whole Rijndael family is
in range: `Propagation/Rijndael.lean` covers the 192- and 256-bit block sizes as well, and uses
them to test what the theory decides about a real design choice.

See [the propagation mechanics](../MECHANICS_PROPAGATION.md).

## Algebra layer

`WideTrail/Algebra/` discharges that hypothesis. It builds `GF(2⁸)` from scratch (Mathlib's
`GaloisField` is `noncomputable`, so it cannot be used for the enumeration needed here), proves
the general theorem "MDS matrix ⟹ optimal branch number", which Mathlib does not have, and
instantiates both at the real `4×4` AES `MixColumns` matrix. The output is
`Algebra/AESMix.lean`'s `aes_four_round_concrete`/`aes128_ten_round_concrete`: the same two
bounds, with no hypothesis left except that the S-box layer is a bricklayer of bijective
S-boxes, which holds for every invertible S-box, AES's included. The same layer holds the
linear algebra of the Poseidon2 layers over any field: Plonky3's `4×4` matrix, the
block-circulant external layer and its branch number, the internal layer `c (diag d + J)`, and
their transposes.

See [the algebra mechanics](../MECHANICS_ALGEBRA.md).

## Differential layer

`WideTrail/Differential/` turns the count into a probability.

- **Exact counts.** A differential's probability is kept as a `Nat` numerator over a fixed
  denominator, never a rational, so every statement stays exact and decidable on a small
  cipher.
- **From counts to AES exponents.** Three steps: a bricklayer's differential count factors
  over bundles, and the number of factors that are not free is exactly the Propagation layer's
  `weight`; the rounds multiply; and `4 · 2⁶ = 256` turns each active AES S-box into a factor
  of `2⁻⁶`. This gives `2⁻¹⁵⁰` over four rounds and `2⁻³³⁰` over the ten rounds of AES-128.
- **Independent round keys.** The multiplication step is the one that needs an assumption, and
  the Differential layer does not assume the product formula. It counts pairs of an input and a
  **round-key vector**, so independent round keys are visible in what is being counted, and
  then *proves* the product. This is not a matter of style: assuming the product formula at a
  fixed key is inconsistent for ten-round AES, and `Differential/Checks/Toy.lean` exhibits a
  cipher, a trail and a key where the key-averaged count is positive and the fixed-key count is
  zero.
- **Hulls.** The layer also proves, with no hypothesis, that a differential is a *sum* over
  trails, and exhibits a two-round differential worth twice its best trail. This is the hull
  effect, which qualifies every wide-trail figure in the literature.
- **Two-round differentials.** `Differential/Hull.lean` bounds the differential itself, the
  whole sum, in the same independent-key model: over two bricklayer rounds with bijective
  S-boxes of uniformity at most `u` and a first linear layer of branch number at least `B`,
  every differential with a nonzero input difference has key-averaged probability at most
  `(u / |K|)^(B - 1)` (`Scheduled.bricklayer_two_round_bound`). Only those two rounds are
  charged, and the bound concerns the keys averaged over: `Differential/Checks/Hull.lean` gives
  a toy cipher on which it fails with the keys fixed to zero.
- **Support preservation, proved.** The layer also turns one of the Propagation layer's
  hypotheses into a theorem. `PreserveSupport` was a claim about a function on differences,
  and a real S-box layer has no such function; what it guarantees is that any output
  difference it *can* produce has the same support as the input. The Differential layer proves
  that from injectivity alone. The Propagation layer's four-round theorems were generalised to
  use it, and the old function-shaped statements remain, unchanged, as corollaries.

See [the differential mechanics](../MECHANICS_DIFFERENTIAL.md).

## Hades layer

`WideTrail/Hades/` models full and partial S-box rounds, with fixed additions and
round-specific invertible linear maps, and counts active coordinates only where an S-box is
applied.

- **Full rounds.** For `r` full rounds, `m` partial rounds and `s` full rounds, its execution
  theorem gives `(r / 2 + s / 2) * B + r % 2 + s % 2` active S-boxes from the outer blocks
  (`outerRound_bound`). Whole-state MDS mixing supplies `B = t + 1`. The activity result
  applies to actual pairs of distinct inputs.
- **Probability.** `Counting.lean` and `Probability.lean` connect masked activity to exact
  differential trail counts in the explicitly independent-key model. The trail bounds keep the
  ratio `|K| / u` per charged S-box exact (`hades_probability_exact`,
  `hades_probability_with_middle_exact`).
- **Partial rounds, windows.** `Subspace.lean` charges the middle rounds too: when no nonzero
  difference stays off the S-box coordinates through `w` consecutive partial rounds with the
  internal linear map, the `m` middle rounds add `m / w` active S-boxes
  (`outer_middle_bound`), and the same term enters the probability bridge
  (`hades_probability_with_middle`). Fewer than `width / mask size` rounds always leave a
  nonzero inactive difference (`inactiveSpace_ne_bot`).
- **Exact dimensions.** `Dimension.lean` gives the exact dimensions of the inactive spaces:
  with one S-box coordinate, once no nonzero difference stays inactive through `width`
  consecutive partial rounds, each round removes exactly one dimension
  (`finrank_inactiveSpace_singleton`). For the Poseidon2 internal layer `c (diag d + J)` that
  happens exactly when the diagonal entries off the S-box coordinate are pairwise distinct
  (`inactiveSpace_diagPlusOnes_card_eq_bot_iff`).
- **Differentials.** `Hull.lean` bounds a key-averaged differential, not only a trail, over two
  full rounds (`hades_differential_bound`).
- **Partial rounds, certificates.** `MiddleBound.lean` takes any lower bound on the partial
  rounds as a hypothesis, `MiddleBound A mask m μ` (every trail through `m` consecutive partial
  rounds with linear map `A`, from a nonzero difference, charges at least `μ` S-boxes), and
  adds it to the outer count and to the trail bounds (`outer_middle_bound_of`,
  `hades_probability_with_middle_bound_exact`); the window argument is the case `μ = m / w`.
  Larger bounds come from finite certificates for a concrete matrix: window relations, linear
  relations between the S-box differences of consecutive rounds that refute every activity
  pattern with too few active rounds (`WindowRelation.lean`, `MiddleBound.of_relationCheck`),
  and forward-space automata with a potential (`Automaton.lean`,
  `MiddleBound.of_automatonCheck`). Boolean checkers on lists of natural numbers
  (`RelationCheck.lean`, `AutomatonCheck.lean`) let the kernel check a certificate by
  `decide +kernel` on light imports.
- **The model.** These are lower bounds in the `IsTrail` model, which records only supports,
  masks and linear maps.

See [the HADES mechanics](../MECHANICS_HADES.md) and [the implementation plan](../HADES_PLAN.md).

## Poseidon2 layer

`WideTrail/Poseidon2/` certifies six deployed Poseidon2 permutations. For each one, Lean
proves that the field is prime, that the S-box and the permutation are bijections, and that
every pair of distinct inputs charges at least this many S-boxes:

| Instance | From full rounds | From partial rounds | Total | Partial rounds charged by | Trail exponent |
|---|---|---|---|---|---|
| SP1 and Pico KoalaBear | 32 | 3 | 35 | window-relation certificate | 1049 |
| SP1 and OpenVM BabyBear | 32 | 0 | 32 | nothing: 13 rounds are fewer than the width 16 | 906 |
| HorizenLabs BN254, width 3 | 16 | 27 | 43 | forward-space automaton; 43 is attained in the `IsTrail` model | 10818 |
| Aztec and Noir BN254, width 4 | 20 | 24 | 44 | forward-space automaton, windows of fourteen | 11070 |

The earlier window counts (33, 34 and 34) remain theorems; see
[Counting more partial rounds](../PRODUCTION_CERTIFICATE.md#counting-more-partial-rounds).

- **HorizenLabs BN254, width three.** The pinned reference instance: field primality, the
  fifth-power S-box, both linear inverses, external MDS mixing and permutation bijectivity. By
  windows, at least 34 charged S-boxes per distinct input pair, 16 from the outer rounds and 18
  from the partial rounds. With the automaton certificate, every trail through the 56 partial
  rounds charges at least 27, so every trail in the `IsTrail` model through its 64 rounds, and
  every distinct input pair, incurs at least 43 (exponent 10818, or 10793 with whole bits), a
  total that some trail in the `IsTrail` model attains. Its checked execution traces match the
  pinned upstream known-answer vector and the vector of SP1's gnark test for the same
  permutation, which SP1 uses for its outer recursion and wrap stages.
- **SP1, width sixteen.** The two permutations SP1 uses for its main proof system, through one
  generic model of the Plonky3 code: KoalaBear (SP1 6.10.0, `x^3`, twenty partial rounds) and
  BabyBear (SP1 5.2.4, `x^7`, thirteen partial rounds). By windows, KoalaBear charges at least
  33 S-boxes per distinct input pair and BabyBear at least 32. With window-relation
  certificates, every trail through the twenty partial rounds of SP1's and Pico's KoalaBear
  permutations charges at least 3 S-boxes, so every distinct input pair incurs at least 35
  (trail exponent 1049, or 1015 with whole bits per S-box). BabyBear's thirteen partial
  rounds, fewer than its width, add nothing. The models of both instances reproduce the
  known-answer vectors of the upstream `p3-koala-bear` and `p3-baby-bear` crates, with those
  tests' own round constants.
- **Pico and OpenVM.** The width-sixteen model takes the internal diagonal and its scale as
  parameters, so the same proofs also certify Pico v3.2.0's KoalaBear permutation (at least 33
  charged S-boxes by windows, trail exponent 989, or 957 with whole bits per S-box; 35 with the
  certificate) and OpenVM v2.1.0's BabyBear permutation (at least 32, exponent 906, or 896 with
  whole bits). Each of these reproduces a known-answer vector from Plonky3's own tests that
  uses the deployed round constants.
- **Aztec and Noir, width four.** The BN254 permutation of Aztec's barretenberg (aztec-packages
  v1.0.0 and v6.1.0) and of Noir v1.0.0: HorizenLabs' `4×4` matrix as the external layer, MDS
  over BN254 with branch number exactly 5, the internal layer `diag(d) + J`, and `4 + 56 + 4`
  rounds. Every distinct input pair incurs at least 34 charged S-boxes by windows of four
  partial rounds, and at least 44 with a certificate for windows of fourteen; with the exact
  ratio the trail exponents are 8554 for 34 and 11070 for 44, and the two-round differential
  exponent is 1006. The model reproduces the published known-answer vectors of barretenberg,
  bb.js and Noir, seven distinct inputs.
- **What the exponents mean.** For each instance the independent-key trail bound is stated as
  an exact ratio. With the window counts this gives the exponents 989 (KoalaBear), 906
  (BabyBear) and 8554 (BN254), each the largest this arithmetic allows. A key-averaged
  differential bound charges the first two full rounds. All of these concern one trail, or the
  differential averaged over an additional independent uniform key per round, not the
  permutation with its fixed constants.

See [the concrete certificates and their scope](../PRODUCTION_CERTIFICATE.md).

## Poseidon layer

`WideTrail/Poseidon/` certifies the original Poseidon, the HADES design, as Starknet deploys
it: the STARK field `p = 2^251 + 17 · 2^192 + 1`, with primality by Lucas certificates, width
three, `x^3`, `4 + 83 + 4` rounds, one matrix `M = [[3, 1, 1], [1, -1, 1], [1, 1, -2]]` in
every round, no linear layer before the first round, and the partial-round S-box on
coordinate 2.

- **Proved with no remaining premise.** Bijectivity; `M` is MDS, with branch number exactly 4,
  and equals `diag(2, -2, -3) + J`; at least 16 charged S-boxes per distinct input pair from the
  full rounds and 43 with windows of three partial rounds; and, from a forward-space automaton
  certificate for the 83 partial rounds, at least 57, a total that some trail in the `IsTrail`
  model attains.
- **Exponents.** The trail exponents are 4000, 10750 and 14250; keeping the ratio `p / 2` exact
  gains nothing, since `p` is barely above `2^251`. The two-round differential exponent is
  750. As for Poseidon2, the probability statements concern one trail, or the differential
  averaged over an additional independent uniform key per round, not the permutation with its
  fixed constants.
- **The compressed schedule.** The compressed schedule of 107 constants that most
  implementations run is proved to compute the same permutation for every input, and to give
  the same state when the same additional key is added to both schedules.
- **Known-answer vectors.** The model reproduces the three permutation-level known-answer
  vectors that the sources publish (pathfinder and CryptoExperts, lambdaworks and
  starknet-types-core, the Cairo corelib).

See [the Starknet section of the certificate](../PRODUCTION_CERTIFICATE.md#starknets-poseidon-hades-instance).

## Linear layer

`WideTrail/Linear/` is the correlation side.

- **Walsh values.** A correlation is kept as its numerator, the Walsh value
  `walsh ψ P Q F u v = ∑ₓ ψ (⟨v, F x⟩ - ⟨u, x⟩)`, for a pairing `⟨u, x⟩` of masks with states
  and an additive character `ψ`; in the binary case it is an integer, as a differential count
  is a natural number.
- **Pairings.** The pairing is part of every statement: AES is treated under the trace pairing
  `⟨u, x⟩ = ∑ᵢ Tr(uᵢ xᵢ)` of `GF(2⁸)`, under which a field matrix moves masks through its field
  transpose, and not under the bit pairing.
- **Trails.** Masks are propagated forward through the inverse of the adjoint, so a sequence of
  masks with a nonzero correlation is a `WideTrailSpec.IsTrail`, or a `Hades.IsTrail`, of the
  forward mask map, and the activity theorems above apply to it unchanged.
- **Keys.** A trail's correlation involves no key: for every key vector the cipher's Walsh
  value is a sum over trails with key-dependent phases (`walsh_run_eq_sum_trails`), and the key
  enters each summand only through its phase (a sign `±1` in the binary case). A trail bound
  therefore bounds one summand of the fixed-key correlation, the same in magnitude for every
  key; it is not a bound on the cipher's correlation for a fixed key.
- **Hulls.** The hull, the squared correlation averaged over an additional independent uniform
  key per round, is the sum of the squared trail correlations (Nyberg's identity,
  `elpCount_succ_eq_sum_trails`) and is bounded over two rounds from the branch number of the
  backward map (`elpCount_two_round_bound`).
- **AES.** The S-box obligation is discharged: under the trace pairing every Walsh value of the
  S-box at a nonzero input mask is at most `32` in absolute value, so every such correlation is
  at most `2⁻³`, and `32` is attained (`AES.sbox_isLinearityBound`,
  `AES.sbox_isLinearityBound_iff`). The `255 · 256` Walsh values with a nonzero output mask are
  reduced to one spectrum of 256 values, which the kernel checks on natural numbers; at the
  zero output mask and a nonzero input mask the value is `0`. With the branch number `5`, every
  4-, 10-, 12- and 14-round linear trail with a nonzero input mask has a trail correlation of
  at most `2⁻⁷⁵`, `2⁻¹⁶⁵`, `2⁻²²⁵` and `2⁻²⁴⁰` in absolute value (at least 25, 55, 75 and 80
  active S-boxes for every such trail with a nonzero correlation), and the expected linear
  probability over two rounds, and over any `R ≥ 2` rounds, is at most `2⁻²⁴` for every nonzero
  input mask in the independent-key model. The bit pairing is not treated, so the designers'
  four-round bound for bit masks is not proved.
- **Poseidon and Poseidon2.** Every linear trail with a nonzero input mask and a nonzero
  correlation (for Poseidon2, a trail of the rounds after the initial external layer) charges
  at least the same number of S-boxes as the differential lower bounds, by windows and by
  certificates: KoalaBear 33 and 35, BabyBear 32, HorizenLabs BN254 34 and 43, Aztec and Noir
  34 and 44, Starknet 43 and 57. This holds for every separating pairing and character;
  `Linear/Field.lean` proves the standard character separating. Their trail bounds take the
  S-box correlation bound as a hypothesis, since no bound on a Walsh value of `x ↦ x^d` over a
  prime field (such as the Weil bound) is proved.

See [the linear mechanics](../MECHANICS_LINEAR.md).

## Rijndael layer

`WideTrail/Rijndael/` discharges the `MixColumns` hypotheses of the Rijndael bounds of
`Propagation/Rijndael.lean`, at every block width.

- **The map.** `mixColumns cols` applies the AES matrix `circ(02, 03, 01, 01)` over `GF(2⁸)`
  to each column of a `4 × cols` state; at `cols = 4` it is `aesMixColumns`.
- **Branch numbers.** Every column active on either side of the map carries at least `5`
  active bytes across input and output (`Rijndael.mixColumns_isColBranchBound`), and
  `MixColumns` after ShiftRows has branch number at least `5` for every offset vector
  (`Rijndael.lin_isBranchBound`).
- **Activity bounds.** With this map, every differential trail (`IsTrail`) with a nonzero input
  pattern has at least `25` active S-boxes in any four consecutive rounds, at least `75` in the
  12 rounds of Rijndael-192 (`Nb = 6`, offsets `0, 1, 2, 3`) and at least `80` in the 14 rounds
  of Rijndael-256 (`Nb = 8`, offsets `0, 1, 3, 4`), with no branch-number or invertibility
  hypothesis (`Rijndael.rijndael192_twelve_round_concrete`,
  `Rijndael.rijndael256_fourteen_round_concrete`; `rijndael192_rounds_concrete` and
  `rijndael256_rounds_concrete` for any number of rounds). The `_trail` corollaries state the
  bounds `25`, `80` and `75` for the functional trail of `rijndaelSpec` with any
  support-preserving S-box layer.
- **ShiftRows offsets.** The diffusion-optimality criterion admits 1680 ShiftRows offset
  vectors on the 256-bit state (`card_diffusionOptimal_offsets_256`), so it is not what selects
  Rijndael-256's offsets `0, 1, 3, 4` (see [the Propagation layer](#propagation-layer)).
- **Scope.** These are lower bounds in a trail model in which every round includes
  `MixColumns`; the final round of the cipher, which omits it, is not modelled. They are not
  claimed to be attained, and nothing here concerns probabilities, the S-box, the key
  schedule, linear trails or differentials. Only activity counts are stated for these block
  sizes. Import the layer with `import WideTrail.Rijndael`.

## Axiom audit and further reading

Named theorem footprints are pinned by `#print axioms`. The complete module audit in
`scripts/AuditAxiomsHeavy.lean` checks every project declaration, including names in the root
namespace, and prints how many it checked: 9254 at commit 46f852a, before the Rijndael layer
was added. `scripts/AuditAxioms.lean` does the same for the declarations of the default
library: 7097 at that commit. Both allow nothing beyond the standard
`propext, Classical.choice, Quot.sound` baseline: no `sorry`, no `native_decide`, no
`bv_decide` fallback axiom, anywhere. See
[`WideTrail/Algebra/MDS_HYPOTHESIS_BUILD.md`](../WideTrail/Algebra/MDS_HYPOTHESIS_BUILD.md) for
the build log of the Algebra layer (what was tried, what failed, why),
[`MECHANICS_ALGEBRA.md`](../MECHANICS_ALGEBRA.md) for how the algebra works,
[`MECHANICS_PROPAGATION.md`](../MECHANICS_PROPAGATION.md) for the support argument,
[`MECHANICS_DIFFERENTIAL.md`](../MECHANICS_DIFFERENTIAL.md) for the Differential layer, and
[`MECHANICS_LINEAR.md`](../MECHANICS_LINEAR.md) for the Linear layer.

Next: the mechanics document of a layer, or
[PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md) for the deployed instances.
