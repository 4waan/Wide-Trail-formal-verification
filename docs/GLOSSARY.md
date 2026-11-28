[WideTrail](../README.md) › [Documentation](README.md) › Glossary

# Glossary

The terms these documents use, in the sense this library gives them. Each entry links to the
Lean file or the mechanics section that defines it. Where an entry names a Lean definition,
the definition is the authority.

## Active S-box

A position whose difference is nonzero. `activePattern s` is the set of positions where `s`
is nonzero, and `weight s` is its size
([`Propagation/Activity.lean`](../WideTrail/Propagation/Activity.lean)). A bijective S-box sends
a zero difference to zero and a nonzero difference to a nonzero one, so only the pattern
matters ([the support argument](../MECHANICS_PROPAGATION.md#the-move-that-makes-the-whole-thing-work-throw-the-values-away)).
In a HADES design the count that matters is the [charged S-box](#charged-s-box).

## Axioms: `propext`, `Classical.choice`, `Quot.sound`

The three standard axioms of Lean and Mathlib: propositional extensionality, the axiom of
choice, and the soundness of quotients. Every declaration of the library depends on these at
most. `scripts/AuditAxioms.lean` and `scripts/AuditAxiomsHeavy.lean` check this for every
declaration, and fail on any other axiom, such as `sorryAx` (from `sorry`) or
`Lean.ofReduceBool` (from `native_decide`). See [BUILDING.md](BUILDING.md#continuous-integration).

## Branch number

The branch number of a linear map `L` is the least number of active positions in `a` and `L a`
together, over every nonzero `a`. The library states it as a predicate,
`isBranchBound col L B`: every nonzero `a` has at least `B` active parts across `a` and `L a`
([`Propagation/Activity.lean`](../WideTrail/Propagation/Activity.lean)). Positions may be
grouped into parts by `col` (the paper's α-sets), and then active parts are counted; with
`col = id`, every position is its own part. As a predicate it is a lower bound, not a minimum:
a theorem needs only "you cannot get below `B`"
([what a branch number is](../MECHANICS_PROPAGATION.md#what-a-branch-number-is-once-you-stop-calling-it-a-minimum)).
The **linear branch number** is defined through correlations (`IsLinBranchBound`,
[`Linear/Masks.lean`](../WideTrail/Linear/Masks.lean)). For a separating
[pairing](#pairing-trace-pairing-and-bit-pairing) it equals the differential branch number of
the map's adjoint (`isLinBranchBound_iff`).

## Bricklayer

A layer that applies an S-box to each [bundle](#support-and-bundle) independently:
`bricklayer s x i = s i (x i)`
([`Differential/Bricklayer.lean`](../WideTrail/Differential/Bricklayer.lean)). Its
differential count factors over the bundles. A bricklayer of bijective S-boxes preserves
supports.

## Charged S-box

In a HADES design, an S-box application whose input difference is nonzero. `sboxWeight mask a`
counts the nonzero words of `a` inside the round's S-box mask only, and `scheduledWeight` adds
it up over rounds ([`Hades/Masked.lean`](../WideTrail/Hades/Masked.lean),
[`Hades/Schedule.lean`](../WideTrail/Hades/Schedule.lean)). A full round charges the whole
support; a partial round may charge nothing although the state difference is nonzero
([HADES mechanics](../MECHANICS_HADES.md#how-the-hades-activity-proof-works)).

## Correlation and Walsh value

For an input mask `u` and an output mask `v`, the Walsh value of `F` is
`walsh ψ P Q F u v = ∑ₓ ψ (⟨v, F x⟩ - ⟨u, x⟩)`, for a [pairing](#pairing-trace-pairing-and-bit-pairing)
of masks with states and an additive character `ψ`. The correlation is the Walsh value divided
by the size of the state space. The library keeps the numerator and never divides
([`Linear/Character.lean`](../WideTrail/Linear/Character.lean);
[correlation without division](../MECHANICS_LINEAR.md#1-correlation-without-division)). In the
binary case the Walsh value is an integer.

## Differential and differential trail

A differential of `F` is a pair `(a, b)` of an input and an output difference. `diffCount F a b`
counts the inputs `x` with `F (x + a) - F x = b`, and a bound such as "probability at most
`2⁻ᵈ`" is written `diffCount * 2 ^ d ≤ |X|`
([`Differential/Counts.lean`](../WideTrail/Differential/Counts.lean);
[probability without division](../MECHANICS_DIFFERENTIAL.md#1-probability-without-division)).
A differential trail fixes the difference between every two rounds. A differential is the sum
of all trails with its input and output difference (see [hull](#hull)).

## Differential uniformity

`IsDiffUniform F u`: for every nonzero input difference `a` and every output difference `b`,
`diffCount F a b ≤ u` ([`Differential/Counts.lean`](../WideTrail/Differential/Counts.lean)).
The AES S-box has uniformity 4, attained. For the deployed instances: `x^3` over KoalaBear and
over the STARK field has uniformity 2, attained; `x^7` over BabyBear has uniformity 6, attained
(`sbox_not_uniform_five`); `x^5` over BN254 has uniformity at most 4
(`Poseidon2.BN254.sbox_uniform`), and that 4 is attained is not proved.

## Diffusion optimal

Definition 5 of the paper: a shuffle `p` is diffusion optimal for a column partition when two
distinct positions in the same column always land in different columns (`DiffusionOptimal`,
[`Propagation/Dispersion.lean`](../WideTrail/Propagation/Dispersion.lean)). For ShiftRows on a
`rows × cols` state it holds exactly when the offset vector is injective
([the closed form](../MECHANICS_PROPAGATION.md#definition-5-has-a-closed-form-and-finding-it-is-what-widens-the-state)).

## Exact ratio and whole bits

Two ways to turn a count of `A` charged S-boxes of uniformity `u` over a field of size `|K|`
into a probability exponent. With **whole bits**, each S-box is charged `d` bits, the largest
`d` with `u · 2^d ≤ |K|`; this loses up to one bit per S-box. With the **exact ratio**, the
bound `keyCount · |K|^A ≤ u^A · N`, where `N` is the number of all key vectors, keeps `|K| / u`
per S-box, and the exponent is the largest
`E` with `2^E · u^A ≤ |K|^A`. The checks show that `E + 1` fails, so `E` is the largest exponent
this arithmetic gives; it is not claimed to be attained
([exact ratios](../MECHANICS_HADES.md#exact-ratios)).

## Expected linear probability (ELP)

The squared correlation of a pair of masks, averaged over an additional independent uniform
key per round. `elpCount` is its numerator, a natural number
([`Linear/Hull.lean`](../WideTrail/Linear/Hull.lean)). By Nyberg's identity it equals the sum of
the squared correlations of all trails between the two masks
([the hull](../MECHANICS_LINEAR.md#7-the-hull-in-the-independent-key-model)).

## External and internal layer

The two linear layers of Poseidon2. The external layer is the linear layer of the full rounds,
and is also applied once before the first round. The internal layer is the linear layer of the
partial rounds. At width sixteen the external layer is `circ(2 M4, M4, M4, M4)` with
`M4 = circ(2, 3, 1, 1)`, of branch number 8, and the internal layer is `c (diag d + J)`, where
`J` is the all-ones matrix ([`Algebra/BlockCirculant.lean`](../WideTrail/Algebra/BlockCirculant.lean),
[`Algebra/DiagPlusOnes.lean`](../WideTrail/Algebra/DiagPlusOnes.lean)). Starknet's Poseidon
uses one matrix `M` in every round, and no linear layer before the first round.

## Forward-space automaton

A finite certificate for a [middle bound](#middle-bound). Each state is a set of differences
with a potential. The potential drops by at least one at every inactive round and grows by at
most one at every active round, so a valid automaton for `m` rounds gives the bound
`(m + 1 - pot start) / 2` (`MiddleBound.of_automaton`,
[`Hades/Automaton.lean`](../WideTrail/Hades/Automaton.lean)). The kernel checks it with the Boolean
checker of [`Hades/AutomatonCheck.lean`](../WideTrail/Hades/AutomatonCheck.lean)
([forward-space automata](../MECHANICS_HADES.md#forward-space-automata)).

## Full round and partial round

In a HADES schedule, a full round applies the S-box to every coordinate, and a partial round
applies it only to the coordinates of its mask (one coordinate in every instance here).
`hadesSchedule r m s mask` has `r` full rounds, then `m` partial rounds, then `s` full rounds
([`Hades/Schedule.lean`](../WideTrail/Hades/Schedule.lean)).

## General forms (`_general`)

A theorem whose name ends in `_general` holds for every round-constant table. The theorem
without the suffix is its case for the pinned table. The proofs of these statements do not
use the values of the constants ([PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md)).

## HADES

The design strategy of Grassi, Luftenegger, Rechberger, Rotaru and Schofnegger (EUROCRYPT
2020): full rounds at the start and at the end, partial rounds in the middle. Poseidon and
Poseidon2 follow it. The Hades layer models it with fixed round additions and round-specific
invertible linear maps ([HADES_PLAN.md](../HADES_PLAN.md),
[HADES mechanics](../MECHANICS_HADES.md)).

## Hull

The sum over all trails with the same input and output, for a differential or for a pair of
linear masks. A trail bound bounds one summand. The library bounds the whole sum over two
rounds, averaged over an additional independent uniform key per round
([`Differential/Hull.lean`](../WideTrail/Differential/Hull.lean),
[`Hades/Hull.lean`](../WideTrail/Hades/Hull.lean),
[`Linear/Hull.lean`](../WideTrail/Linear/Hull.lean)). Nothing is said about a fixed key.

## Inactive space and window

A difference is inactive in a round when it vanishes on every S-box coordinate of that round.
`inactiveSpace L mask r` is the subspace of differences that stay inactive through `r`
consecutive rounds with linear map `L`
([`Hades/Subspace.lean`](../WideTrail/Hades/Subspace.lean)). If it is `⊥` for a window of `w`
rounds, every window of `w` partial rounds activates an S-box, and `m` partial rounds add
`m / w`. With one S-box coordinate a window is useful only once it is at least the width
([partial rounds](../MECHANICS_HADES.md#partial-rounds)).

## Independent-key model

The model of every probability statement here. The object counted is a pair of an input and a
vector of round keys, one additional independent uniform key per round, so the product formula
over rounds is a theorem, not an assumption (`trailKeyCount`,
[`Differential/Markov.lean`](../WideTrail/Differential/Markov.lean)). Fixed round constants are
not independent keys: a bound in this model is not a bound for the permutation with its fixed
constants, or for any one key
([where the assumption lives](../MECHANICS_DIFFERENTIAL.md#4-multiplying-rounds-and-where-the-assumption-lives)).

## `IsTrail` model

A sequence of differences in which each step is the linear layer applied to a pattern with
the same support (and, for HADES, equal to the previous difference off the S-box mask)
(`WideTrailSpec.IsTrail`, [`Propagation/Cipher.lean`](../WideTrail/Propagation/Cipher.lean);
`Hades.IsTrail`, [`Hades/Probability.lean`](../WideTrail/Hades/Probability.lean)). It records
only supports, masks and linear maps, so a bound in this model holds for every S-box and every
round-constant table. The difference trace of every pair of inputs is such a trail. Witness
trails in this model are not claimed to be realised by input pairs or keys.

## Kernel-checked

Lean's kernel, a small trusted program, checks every proof term. `decide` proves a decidable
proposition by evaluating its decision procedure, which the kernel re-checks; `decide +kernel`
has the kernel do that evaluation directly. The library uses no `native_decide`, which would
trust compiled code instead and appears as the axiom `Lean.ofReduceBool`.

## Known-answer vector

An input and the output that an upstream source asserts for it, such as a test in the
deployed code. The library proves each vector for its model, by `decide` on a
[materialised runner](#materialised-runner). A vector checks one input: it shows that the model
computes the output the source asserts, not that model and code agree on every input
([PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md#boundary-of-the-certificate)).

## Lucas certificate

A proof that a number `p` is prime from a witness and the factorisation of `p - 1`. The
kernel checks the factorisations and the modular exponentiations; the program that found them
is outside the trust boundary. The BN254 and STARK fields are proved prime this way
([`Poseidon2/BN254Primality.lean`](../WideTrail/Poseidon2/BN254Primality.lean),
[`Poseidon/StarkPrimality.lean`](../WideTrail/Poseidon/StarkPrimality.lean)).

## Mask

A linear mask: a vector `u` that is read against a state `x` through a
[pairing](#pairing-trace-pairing-and-bit-pairing), `⟨u, x⟩`. A linear trail fixes a mask
between every two rounds. A mask is active at a position where it is nonzero, so the activity
counts apply to masks as to differences
([masks move forward](../MECHANICS_LINEAR.md#3-masks-move-forward)).

## Materialised runner

A second definition of a permutation, written after the deployed code's loop with every
coordinate a named field, and proved equal to the specification for every input. `decide`
on the runner then proves statements about the model, such as known-answer vectors
([`Poseidon2/Plonky3Execution.lean`](../WideTrail/Poseidon2/Plonky3Execution.lean)).

## MDS

A matrix is MDS when every square submatrix is nonsingular (`IsMDS`,
[`Algebra/MDS.lean`](../WideTrail/Algebra/MDS.lean)). An MDS `n × n` matrix has the optimal
branch number `n + 1` ([why MDS implies the branch number](../MECHANICS_ALGEBRA.md#2-why-mds-implies-the-branch-number-bound-mechanically)).

## Middle bound

`MiddleBound A mask m μ`: every trail in the [`IsTrail` model](#istrail-model) through `m`
consecutive rounds with linear map `A` and that mask, from a nonzero difference, charges at
least `μ` S-boxes ([`Hades/MiddleBound.lean`](../WideTrail/Hades/MiddleBound.lean)). It does not
depend on the S-boxes or the round constants. The window argument gives `μ = m / w`;
[window relations](#window-relation) and [forward-space automata](#forward-space-automaton)
give larger values ([the interface](../MECHANICS_HADES.md#the-interface)).

## Montgomery factor

Plonky3 stores a field element `x` as its Montgomery representative `x · R mod p`, with
`R = 2^32`. Read at the field level, the internal layer of SP1's two width-sixteen instances
carries the factor `R⁻¹`: `x_i ↦ R⁻¹ (d_i x_i + ∑_j x_j)`. The internal layers of Pico and
OpenVM have scale 1. The Montgomery representatives themselves are not modelled
([SP1 width-sixteen instances](../PRODUCTION_CERTIFICATE.md#sp1-width-sixteen-instances)).

## Negative control

A deliberately changed model, such as a transposed matrix, a shifted diagonal or a missing
initial layer, that is proved to fail a known-answer vector. It shows that the vector detects
that change ([PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md)).

## Pairing: trace pairing and bit pairing

How a linear mask is read against a state. On `GF(2⁸)`, the **bit pairing** is the parity of
`u ∧ x`, and the **trace pairing** is `⟨u, x⟩ = Tr(u · x)`. They move masks through a linear
layer differently, so every linear statement names its pairing. AES is treated under the
trace pairing only. The prime-field instances use `⟨u, x⟩ = u * x`, whose sum over a state is
the dot product ([the pairing is part of the statement](../MECHANICS_LINEAR.md#2-the-pairing-is-part-of-the-statement)).

## S-box

The nonlinear map applied to one position of the state: the AES byte substitution on `GF(2⁸)`
([`Algebra/AESSbox.lean`](../WideTrail/Algebra/AESSbox.lean)), or a power map `x ↦ x^d` on a
prime field in Poseidon and Poseidon2 (`x^3`, `x^5` and `x^7` here;
[`Algebra/PowerSbox.lean`](../WideTrail/Algebra/PowerSbox.lean)). Every S-box here is a
bijection. An S-box is active when its input difference, or its mask, is nonzero.

## Support and bundle

A bundle is a position of the state on which one S-box acts: a byte in AES, a field element in
Poseidon and Poseidon2. The support of a difference is the set of bundles where it is nonzero,
`activePattern` ([`Propagation/Activity.lean`](../WideTrail/Propagation/Activity.lean)). A
layer preserves supports (`PreserveSupport`) when every output difference it can produce has
the support of its input difference, as a [bricklayer](#bricklayer) of bijective S-boxes does.

## Trail exponent

For a count of `A` charged S-boxes of differential uniformity `u` over a field of size `|K|`,
the largest `e` with `2^e · u^A ≤ |K|^A`: every trail with a nonzero input difference has
probability at most `2^-e` (one trail, independent uniform round keys). It is the
[exact-ratio](#exact-ratio-and-whole-bits) exponent. It bounds one trail, not a differential
and not the permutation with its fixed constants, so it can exceed the state size.

## Window relation

A finite certificate for a [middle bound](#middle-bound): a linear relation between the S-box
input and output differences of `D + 1` consecutive partial rounds (`IsTrail.window_relation`,
[`Hades/WindowRelation.lean`](../WideTrail/Hades/WindowRelation.lean)). If combinations of the
relations refute every nonempty pattern of fewer than `k` active rounds, every trail charges at
least `k`. The kernel checks it with the Boolean checker of
[`Hades/RelationCheck.lean`](../WideTrail/Hades/RelationCheck.lean)
([window relations](../MECHANICS_HADES.md#window-relations)).

Next: [HOW_IT_WORKS.md](HOW_IT_WORKS.md).
