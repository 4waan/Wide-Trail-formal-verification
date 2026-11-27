# Mechanics of Linear layer

How `WideTrail/Linear/` works. The differential layer turns a number of active S-boxes into a
bound on a probability; this layer turns the same number into a bound on a correlation. Most of
the machinery is reused unchanged. Two things are new: a choice the differential side never had
to make, which pairing of masks with states a statement is about, and a different answer to the
question of where the key goes.

## 1. Correlation without division

A linear approximation of `F` pairs an input mask `u` with an output mask `v` and asks how well
`x ↦ ⟨u, x⟩` predicts `x ↦ ⟨v, F x⟩`. Three ingredients fix what that means (`Character.lean`):

```
P : Pairing X G               -- a bi-additive ⟨u, x⟩ of masks with states, valued in G
Q : Pairing Y G               -- the pairing on the output side, ⟨v, y⟩ for F : X → Y
ψ : AddChar G R               -- an additive character into a commutative ring R
walsh ψ P Q F u v = ∑ₓ ψ (⟨v, F x⟩ - ⟨u, x⟩)
```

The correlation is `walsh / |X|`. As `Differential/Counts.lean` keeps the numerator `diffCount`
and never divides, everything here keeps the numerator `walsh`. In the binary case
(`Binary.lean`) the pairing is valued in `ZMod 2` and `ψ` is the sign `sign₂ t = (-1)ᵗ` into
`ℤ`, so a Walsh value is an integer, `∑ₓ (-1) ^ (⟨u, x⟩ + ⟨v, F x⟩)` (`walsh_sign₂_apply`), and
a claim of the form `|corr| ≤ c / |X|` is

```
(walsh sign₂ P P F u v).natAbs ≤ c
```

which is exact and, on a small enough state, decidable: `IsLinearityBound P F c`, every Walsh
value at a nonzero input mask at most `c` in absolute value, has a `Decidable` instance.

Ten identities, labelled (W1) to (W10), do the work. Five hold for every pairing and every
character. A key added before `F` multiplies the Walsh value by `ψ ⟨u, k⟩` (W1,
`walsh_addKey`); a constant added after `F` multiplies it by `ψ ⟨v, c⟩` (W2, `walsh_postAdd`);
a map `L` after `F` moves the output mask through an adjoint of `L` (W3, `walsh_comp_adjoint`);
a bricklayer's Walsh value is the product of its S-boxes' (W4, `walsh_bricklayer`); and under a
trace form, inversion has one component function up to scaling,
`walsh (·⁻¹) a β = walsh (·⁻¹) (a * β) 1` for `β ≠ 0` (W10, `walsh_inv_mul`).

The other five need the pairing to be *separating* for `ψ` (`Pairing.Separating`: for `u ≠ 0`
the character `x ↦ ψ ⟨u, x⟩` is nontrivial, and the same on the state side) and `R` to be a
domain. Orthogonality (W5) cancels a factor `1 - ψ ⟨u₀, x⟩`, and the multiplication of
correlation matrices (W6, `walsh_comp`), the Walsh value `|X| · [u = Lt v]` of a map with an
adjoint (W7, `walsh_of_adjoint`), the zero masks (W8) and Parseval (W9) are built on it.
`Checks/Character.lean` shows the hypothesis is used: under the zero pairing every Walsh value
of the 3-bit χ map is `8`, and (W6) reads `8 · 8 = 64` against `8 · 8 · 8 = 512`
(`toy_comp_fails_zeroPairing`).

(W8) is the linear twin of the support argument of the differential layer. A nonzero input mask
has Walsh value `0` with the zero output mask, for every map; the zero input mask has Walsh
value `0` with a nonzero output mask, for a bijection. Through a bricklayer of bijections a
nonzero Walsh value therefore forces the input and output masks to be active in the same
bundles (`activePattern_eq_of_walsh_ne_zero`, the twin of
`activePattern_eq_of_diffCount_ne_zero`). The bundle bound is the twin of
`diffCount_bricklayer_le`:

```
|walsh (bricklayer s) u v| ≤ c ^ weight u * |K| ^ (|Idx| - weight u)      -- natAbs_walsh_bricklayer_le
```

An active bundle costs a factor of at most `c`, an inactive one at most `|K|`.

## 2. The pairing is part of the statement

A differential is a pair of differences, and the difference of two bytes is a byte: there is
nothing to choose. A mask is read through a pairing, and a type does not come with one. On
`GF(2⁸)` two are natural:

* the **bit pairing**, the parity of `u ∧ x`, that is the dot product of the eight bits
  (`bitPairing`; on bytes, `bytePairing` in `Checks/Conventions.lean`);
* a **trace-form pairing** `⟨u, x⟩ = ℓ (u · x)` (`Pairing.traceForm`), here with
  `ℓ = GF256.trace`, the functional with bit mask `0xA0`, which equals the absolute trace
  `z + z² + z⁴ + ⋯ + z¹²⁸` on every byte (`GF256.trace_eq_fieldTrace`).

They disagree about which map carries masks through a linear layer. Under every trace form,
multiplication by a constant is an adjoint of itself (`isAdjoint_mul_left`), and the transpose
of a matrix over the field is an adjoint of the matrix (`isAdjoint_mulVec`; column by column,
`isAdjoint_colMatrix`); when the trace form is separating they are the only adjoints
(`IsAdjoint.unique`). Under the bit pairing they need not be. `Checks/Conventions.lean` computes
it for `x ↦ 0x02 · x`: `⟨0x01, 0x02 · 0x02⟩ = 0` while `⟨0x02 · 0x01, 0x02⟩ = 1`
(`bytePairing_counterexample`); every bit adjoint maps `0x01` to `0x80`
(`byte_adjoint_two_apply_one`), while every adjoint under the trace form with mask `0xA0` maps
`0x01` to `0x02` (`trA0_adjoint_two_apply_one`); and the field transpose of the `MixColumns`
matrix is not a bit adjoint of it (`not_isAdjoint_byte_aesMatrix`).

So the pairing is chosen per instance, and every statement names it. AES is treated under the
trace pairing `GF256.tracePairing`, `⟨u, x⟩ = Tr(u · x)`, and its bundle sum `∑ᵢ Tr(uᵢ xᵢ)`,
because under it a `GF(2⁸)` matrix moves masks through its field transpose. The prime-field
instances use the multiplication pairing `⟨u, x⟩ = u * x` (`mulPairing`, the trace form of the
identity), whose bundle sum is the dot product. Nothing makes either pairing *the* pairing of
its type.

**The `GF(2⁸)` bit-pairing caveat.** The AES designers state their bounds for bit masks. The two
pairings differ by a relabelling of masks, byte by byte: `Tr(c · z)` is the parity of
`phi c ∧ z` (`GF256.trace_mul_eq_par8`), so, by the generic `walsh_maskRelabel`, a trace-pairing
Walsh value would be a bit-pairing Walsh value at relabelled masks, and, once `phi` is a
bijection, `IsAdjoint.maskRelabel` would move adjoints the same way. This `GF(2⁸)` instance is
not constructed in Lean: no lemma connects `GF256.trace_mul_eq_par8` to the bit pairing
`bytePairing` of `Checks/Conventions.lean`. `GF256.phi` is not proved to be a bijection either,
so no bit-pairing statement is derived: the bit-pairing linear approximation table of the S-box
is not computed, and the designers' four-round bound for bit masks is not proved.

The same caveat qualifies one sentence of `Algebra/Transpose.lean`. That file takes the linear
branch number of `x ↦ A x` to be the differential branch number of `Aᵀ`, as a definition, on the
ground that "the nonzero correlations are exactly the pairs `(Aᵀ v, v)`". `Masks.lean` now proves
the general form of that sentence: for a separating pairing into a domain in which `|X| ≠ 0`, `B`
is a linear branch-number lower bound of a map, defined through correlations
(`IsLinBranchBound`), exactly when it is a differential branch-number lower bound of the map's
adjoint (`isLinBranchBound_iff`, by (W7)). Over `F_p`, with the dot product and any separating
character, the adjoint of `x ↦ A x` is `x ↦ Aᵀ x`, and the sentence holds as written
(`Hades.isLinBranchBound_iff_maskLin`; `Hades.isLinBranchBound_iff_maskLin_std` for
`ZMod.stdAddChar`). Under bit masks on `GF(2⁸)` the nonzero correlations of `x ↦ A x` need not
be the pairs `(Aᵀ v, v)`: the bit adjoint of a field matrix need not be its field transpose, and
for the `MixColumns` matrix it is not (`not_isAdjoint_byte_aesMatrix`). With `Φ` the relabelling
`phi` applied byte by byte, the bit adjoint would be `Φ ∘ Aᵀ ∘ Φ⁻¹`. Because `Φ` acts byte by
byte and fixes `0` (`Tr(0) = 0`), the branch number would carry over, but that needs `phi` to be
a bijection, which is not proved, so nothing is claimed for bit masks. `Algebra/Transpose.lean` is unchanged and proves nothing about correlations. Two
sentences of its docstring predate this layer and are now out of date: "Correlations are not
formalised in this library", and, under "What is not claimed", that how masks propagate through
whole rounds and the identification of the linear branch number with the differential branch
number of the transpose "are not formalised".

## 3. Masks move forward

Write `Lt` for an adjoint of a linear layer `L`: `⟨v, L y⟩ = ⟨Lt v, y⟩` (`IsAdjoint`). By (W3),
an output mask `v` of `L` is the mask `Lt v` at its input, so masks naturally run backwards. The
library indexes a linear trail from the input instead, as it indexes a differential trail:
`T 0` is the input mask of round `0`, the mask at the output of round `n`'s S-box layer is
`b = lamT (T (n + 1))`, and the next mask is obtained **forward, through the inverse of the
adjoint**, `T (n + 1) = lamT⁻¹ b` (`Masks.lean`). Forward propagation keeps the pairing
invariant, `⟨Lt⁻¹ w, L y⟩ = ⟨w, y⟩` (`IsAdjoint.dot_symm_apply`): masks move contragrediently to
states.

The reason is the shape of a round. A `WideTrailSpec` has the linear layer
`lin = mix ∘ transpose disp`: a bundle permutation, then a column-wise mixing. For AES,
`L = MixColumns ∘ ShiftRows`, and its trace adjoint is `aesLinT = ShiftRows⁻¹ ∘ mixColumnsT`
(`AES.aesLin_isAdjoint`; the only one, `AES.aesLinT_unique`): the mixing comes first and the
permutation second, the wrong way round for a `WideTrailSpec`. Its inverse has the right shape,

```
aesMaskSpec.lin = mixColumnsInvT ∘ ShiftRows      -- mixColumnsInvT: circ(0e, 09, 0d, 0b) per column
```

with the same `ShiftRows` as the state specification (`AES.aesMaskSpec_disp`,
`AES.aesLinSpec_disp`) and `circ(0e, 09, 0d, 0b) = (M⁻¹)ᵀ` for the `MixColumns` matrix `M`
(`AES.aesInvMatrixT_eq`; the products of `Mᵀ` and `circ(0e, 09, 0d, 0b)` in both orders are
checked to be `1` by the kernel). So `aesSpec` builds a specification `AES.aesMaskSpec` for the
forward mask map, and the four-round theorems of the propagation layer apply to masks
unchanged. Its branch hypothesis comes from `isMDS_transpose_iff`: `Mᵀ` is MDS, and a column and
its image under `circ(0e, 09, 0d, 0b)` are related by `Mᵀ`, so every active column carries at
least `5` active bytes (`AES.mixColumnsInvT_isColBranchBound`). `Checks/AESCipher.lean` confirms
that the forward mask map is not the state map: one active byte becomes the column
`(0e, 0b, 0d, 09)`, against `(02, 01, 01, 03)` (`maskSpec_lin_ne`).

Nothing is lost by the choice. The backward reading is equivalent: `T` is a trail of the forward
specification exactly when, at every round, the S-box output mask `lamT (T (n + 1))` has the
support of `T n` (`isTrail_iff_backward`; `AES.maskTrail_iff_backward`). Branch numbers do not
distinguish a bijection from its inverse (`isBranchBound_symm_iff`): the code `{(x, e x)}` is
`{(e⁻¹ y, y)}` with the halves exchanged.

The bridge is the twin of `isTrail_of_trailKeyCount_ne_zero`. If every S-box is bijective, the
bundle pairing is separating and `lamT` undoes `S.lin`, a trail with a nonzero correlation is an
`S.IsTrail` (`isTrail_of_trailCorr_ne_zero`): at round `n` the S-box output mask has the support
of `T n` by (W8), and `T (n + 1) = S.lin b` because `lamT` is a bijection of a finite type. The
activity lower bound `A = r / 4 · B² + (if 2 ≤ r % 4 then B else 0)` of `IsTrail.bound_rounds`
then applies to it.

The linear branch number comes out of (W7). Daemen and Rijmen define it through correlations:
`IsLinBranchBound ψ P L B` says that every pair of masks `(u, v) ≠ (0, 0)` at which `L` has a
nonzero Walsh value has at least `B` active bundles across `u` and `v`. A map with an adjoint
has its nonzero Walsh values exactly at the pairs `(Lt v, v)`, so this is the differential
branch-number bound of `Lt` (`isLinBranchBound_iff`). For AES, `MixColumns` and
`MixColumns ∘ ShiftRows` have linear branch number at least `5`
(`AES.aesMixColumns_isLinBranchBound`, `AES.aesLin_isLinBranchBound`), and the bound cannot be
raised to `6`: the backward map sends one active byte to four
(`aesLin_not_isLinBranchBound_six`).

## 4. Trails, and exactly how the key enters

The keyed cipher is `Scheduled.run lam γ r k` (`Differential/Hull.lean`): round `n` maps `x` to
`lam n (γ n (x + k n))`, with `lam n` an additive bijection, `γ n` any map, and fixed round
constants inside `γ n`. By (W1) and (W3), one keyed round has

```
walsh (x ↦ L (F (x + k))) u v = ψ ⟨u, k⟩ · walsh F u (Lt v)        -- walsh_keyedRound
```

The key multiplies the Walsh value by a phase and does nothing else. A trail `T` therefore
carries two separate quantities (`Trail.lean`):

```
trailCorr  ψ P lamT γ r T = ∏_{n < r} walsh (γ n) (T n) (lamT n (T (n + 1)))   -- no key
trailPhase ψ P r k T      = ∏_{n < r} ψ ⟨T n, k n⟩                         -- ±1 if binary
```

Applying (W6) at the first round and peeling rounds off by induction gives the **fixed-key
expansion** (`walsh_run_eq_sum_trails`): for a separating pairing into a domain, adjoints
`lamT n` of the linear layers, and every key vector `k`,

```
|X| ^ r · walsh (run lam γ (r + 1) k) u v = ∑_d trailPhase k T_d · trailCorr T_d
```

over the trails `T_d = Scheduled.throughTrail u d v` from `u` to `v`, one for each choice `d`
of the `r` intermediate masks.

This is where the linear side differs from the differential side. Section 4 of
[the differential mechanics](MECHANICS_DIFFERENTIAL.md) shows that a fixed-key product formula
for trail probabilities is inconsistent, and counts over key vectors so that the product becomes
a theorem. Here the trail needs no model: the expansion is exact for every key vector,
independent, scheduled or zero. The key enters each summand only through its phase
`trailPhase k T_d`, the character `ψ` of the linear form `∑ₙ ⟨T_d n, k n⟩` (a sign `±1` in the
binary case); in the binary case the magnitude `|trailCorr T_d|` of the summand is the same under
every key (`natAbs_trailPhase_mul`). Fixed round constants belong to `γ`, so with
the zero key the left side is the Walsh value of the rounds with their constants and no key. In
a HADES round the constant is added before the S-boxes, so by (W1) it contributes a phase
(`Hades.walsh_roundGamma`), and with the zero key the expansion is one of the Walsh value of
the permutation with its fixed constants (`Hades.walsh_execute_eq_sum_linCorr`).

What the key does decide is how the summands combine. The fixed-key correlation is a sum over
all trails from `u` to `v` with key-dependent phases, and the summands can reinforce or cancel.
`Checks/Toy.lean` shows it on a sixty-four-state toy: at one pair of masks the Walsh value is
`16`, `-16` or `0` depending on the second round key (`toy_sign`). So **a trail bound bounds one summand of the
fixed-key correlation, the same in magnitude for every key; it is not a bound on the cipher's
correlation for a fixed key.** Bounding the sum is the job of the hull (section 7), and only in
the independent-key model.

With a linearity bound `c` for every S-box, the bundle bound multiplies over the rounds
(`natAbs_trailCorr_le`, the twin of `trailKeyCount_bricklayer_le`):

```
|trailCorr| ≤ c ^ W · |K| ^ (r · |Idx| - W),          W = patternWeight T r
```

and the arithmetic of section 5 of the differential mechanics follows: the exact ratio
`|trailCorr| · |K| ^ W ≤ c ^ W · |X| ^ r` (`natAbs_trailCorr_mul_card_pow_le`), the same for
any `A ≤ W` with no relation between `c` and `|K|` assumed
(`natAbs_trailCorr_mul_card_pow_le_of_le`), and `|trailCorr| · 2 ^ (d · W) ≤ |X| ^ r` when
`c · 2 ^ d ≤ |K|` (`natAbs_trailCorr_mul_pow_le`). With the bridge, `W` is replaced by the
activity lower bound `A` of the specification, for every trail with a nonzero input mask
(`trailCorr_le_of_spec`, `trailCorr_ratio_le_of_spec`, the twins of `trailKeyCount_le_of_spec`).
A trail with a zero correlation satisfies these bounds trivially; the activity count is only
claimed for trails with a nonzero correlation.

## 5. The AES S-box: one spectrum instead of a table

Under the trace pairing, every Walsh value of the AES S-box at a nonzero output mask is at most
`32` in absolute value (`AES.sbox_walsh_le`), and so is every Walsh value at a nonzero input
mask (`AES.sbox_isLinearityBound`; at the zero output mask the value is `0`, by (W8)). Every such
correlation is at most `2⁻³` in absolute value. The `255 · 256` values with a nonzero output mask
are sums of 256 signs each, about 16.7 million terms, and the proof never evaluates them
(`AESSbox.lean`). The S-box is `S x = A (x⁻¹) + 0x63` with `A` additive, and the identities of
section 1 reduce every value with `b ≠ 0` to one of 256:

1. `AES.affAdj`, given by the images `1e 6e 88 5f b8 6b d0 ef` of the basis bytes
   `2⁰, …, 2⁷`, is a trace adjoint of `A` (`AES.affine_isAdjoint`), checked by the kernel on
   the `8 · 8` basis pairs and extended by additivity in each argument; `affAdj b ≠ 0` for
   `b ≠ 0` (`AES.affAdj_eq_zero`).
2. (W2) and (W3): `W_S(a, b) = sign₂ (Tr(b · 0x63)) · W_inv(a, affAdj b)` (`AES.walsh_sbox_eq`).
3. (W10): `W_inv(a, β) = W_inv(a · β, 1)` for `β ≠ 0`.
4. `W_inv(c, 1) = ∑_z (-1) ^ (Tr(z⁻¹) + Tr(c · z)) = 256 - 2 · mism (phi c) 256`
   (`AES.walsh_inv_one_eq_spectrum`). Here `mism w 256` counts the bytes `z` at which the parity
   of `w ∧ z` differs from bit `z` of the 256-bit table `gTab` of `Tr(z⁻¹)`, and `phi c` is the
   bit mask of `z ↦ Tr(c · z)`.
5. `|256 - 2 · mism w 256| ≤ 32` for every `w < 256` (`Linear.AESSpectrum.spectrum_bound`).

Step 5 is the kernel computation: `256 · 256 = 65,536` terms, in four chunks of 64 masks
(`chunk₀` to `chunk₃`, each by `decide +kernel`), in `AESSpectrum.lean`, a module with no
imports that works on natural numbers only. Two 256-case checks in `GF256Trace.lean` tie it to
the field: `GF256.trace z⁻¹` is bit `z` of `gTab` (`GF256.trace_inv_eq_g`, with `0⁻¹ = 0`), and
`GF256.trace z` equals `z + z² + ⋯ + z¹²⁸` (`GF256.trace_eq_fieldTrace`). The latter is checked on
an explicit squaring chain, seven multiplications per byte, because `GF256` keeps Lean's default
power, which would evaluate `z ^ 128` by repeated multiplication. By its definition
`W_inv(c, 1)` is a binary Kloosterman sum with the term `z = 0` included; no property of
Kloosterman sums is used.

The bound is attained: `W_S(0x55, 0x01) = -32` (`AES.sbox_walsh_attained`; the mask is
`phi (0x55 · affAdj 0x01) = 0xac`, and `mism 0xac 256 = 112`), so `32` is the least linearity
bound under this pairing (`AES.sbox_isLinearityBound_iff`). `Checks/AES.lean` recomputes the
witness directly from the definition of `walsh`, a sum of 256 signs, without the reduction
(`sbox_walsh_witness_direct`), and the spectrum check fails with `28` in place of `32`, at
`w = 0x0c` (`Linear.AESSpectrum.specLe_28_false`).

`32 · 2³ ≤ 256 < 32 · 2⁴`, so the bound clears a factor `2³` per active S-box, and no linearity
bound of the S-box clears `2⁴`: one with `c · 2 ^ d ≤ 256` exists exactly when `d ≤ 3`
(`sbox_clears_iff` in `Checks/AESCipher.lean`). The differential side charges `2⁻⁶` per active
S-box on a probability; the linear side charges `2⁻³` on a correlation, that is `2⁻⁶` on its
square.

## 6. AES trails

The rounds are those of `Differential/AESProb.lean`: round `n` maps `x` to
`MixColumns (ShiftRows (SubBytes (x + k n)))` with the real S-box and the real `MixColumns`
matrix. With the S-box bound `32`, `32 · 2³ ≤ 256`, and the specification `AES.aesMaskSpec` of
section 3 (branch number `5`, four-round bound `25`), `trailCorr_le_of_spec` gives, for every
round count `r` and every trail with a nonzero input mask (`AES.rounds_correlation`),

```
|trailCorr| · 2 ^ (3 · A) ≤ |X| ^ r,       A = r / 4 · 25 + (if 2 ≤ r % 4 then 5 else 0)
```

| Rounds | Active S-boxes, at least | Trail correlation, at most in absolute value | Theorem |
|---|---|---|---|
| 4 | 25 | `2⁻⁷⁵` | `AES.four_round_correlation` |
| 10 | 55 | `2⁻¹⁶⁵` | `AES.ten_round_correlation` |
| 12 | 75 | `2⁻²²⁵` | `AES.twelve_round_correlation` |
| 14 | 80 | `2⁻²⁴⁰` | `AES.fourteen_round_correlation` |

The active S-box counts are the activity lower bounds of `IsTrail.bound_rounds`, for every trail
with a nonzero input mask and a nonzero correlation (`AES.isTrail_of_corr_ne_zero`); neither
they nor the correlation bounds are claimed to be attained. The trail correlation is
`trailCorr / |X| ^ r`, one summand of the fixed-key expansion `AES.walsh_run_expansion`, and
`AES.four_round_contribution` restates the four-round bound for the summand
`trailPhase k T · trailCorr T` under any key vector. The four-round row is the bound the
designers state for four-round linear trails (no correlation above `2⁻⁷⁵`, Rijndael proposal
§8.2.2), here under the trace pairing and for the rounds modelled: every round includes
`MixColumns`, and there is no final round without it and no final whitening key. For bit masks
it is not proved (section 2).

`Checks/AESCipher.lean` shows where the numbers stop. No linearity bound of the S-box gives
`d = 4`, so the exponents `75, 165, 225, 240` cannot be raised to `100, 220, 300, 320` this way.
The non-MDS matrix `circ(0, 1, 1, 1)` sends one active byte to three and fails the branch
hypotheses (`binMixColumns_not_isColBranchBound`, `binMixColumns_not_isBranchBound`). The branch
bound `5` cannot be raised to `6` (`aesLinT_not_isBranchBound_six`). The zero trail has
correlation `|X| ^ r`, so the hypothesis `T 0 ≠ 0` is needed
(`four_round_correlation_needs_h0`).

## 7. The hull in the independent-key model

In the binary case the fixed-key correlation is a signed sum over trails (section 4), and one key
can line the signs up. Squaring and averaging over keys removes the signs. `Hull.lean` counts, in
the binary case,

```
elpCount P lam γ r u v = ∑_{k : Fin r → X} |walsh (run lam γ r k) u v| ^ 2       -- a natural number
```

which, divided by `|X| ^ r · |X| ^ 2`, is the expected linear probability of `(u, v)`: the
squared correlation averaged over an additional independent uniform key per round. Fixed round
constants stay in `γ`; only the additional keys are averaged over.

The mechanism is one identity. For `r ≥ 1` the first key multiplies the Walsh value at the
input mask `c` by `(-1) ^ ⟨c, k 0⟩`, and for a separating pairing into `ZMod 2`

```
∑_k (∑_c f c · (-1) ^ ⟨c, k⟩) ^ 2 = |X| · ∑_c f c ^ 2                  -- sum_sq_sum_sign
```

The cross term at `(c, c')` is a sum of `(-1) ^ ⟨c + c', k⟩`, which is `|X|` if `c + c' = 0` and
`0` otherwise, and a separating pairing into `ZMod 2` forces `x + x = 0`
(`Pairing.Separating.add_self_eq_zero`), so `c + c' = 0` exactly when `c = c'`. From it come
Markov composition, `elpCount (r₁ + r₂) u w · |X| ^ 2 = ∑_v elpCount r₁ u v · elpCount' r₂ v w`
with `elpCount'` the count of the last `r₂` rounds (`elpCount_add`), with no hypothesis on the
maps, and **Nyberg's identity** (`elpCount_succ_eq_sum_trails`)

```
elpCount (r + 1) u v · |X| ^ (2 r) = |X| ^ (r + 1) · ∑_d trailCorr (throughTrail u d v) ^ 2
```

Normalised, it says that the expected linear probability is the sum of the squared trail
correlations of all trails from `u` to `v`: the signs of the fixed-key expansion average out.
The columns of the count sum to `|X| ^ (r + 2)` for every map, the rows do when the maps are
injective (`sum_elpCount_left`, `sum_elpCount_right`), and a nonzero input mask never reaches
the zero output mask (`elpCount_zero_right`).

The two-round bound mirrors section 7 of the differential mechanics. With adjoints `lamT n` and
`β = lamT 1 v` (`elpCount_two`),

```
elpCount 2 u v = ∑_c walsh (γ 0) u (lamT 0 c) ^ 2 · walsh (γ 1) c β ^ 2
```

and for bricklayer rounds both factors are products over bundles. By (W8) a nonzero term needs
`lamT 0 c` to have the support of `u` and `c` the support of `β`, so `(c, lamT 0 c)` is a nonzero
codeword of the backward map `lamT 0` (`Scheduled.codeword`), of weight at least `B`, on the
`weight u + weight β` positions of those two supports. `Scheduled.sum_prod_le_of_weight` of
`Differential/Hull.lean` is used unchanged, with the per-position bound `c²` (the squared
linearity bound) and the per-position sum `|K|²` (Parseval, (W9); the row sums are where
bijective S-boxes are needed). For `u ≠ 0` and every `v` (`elpCount_two_round_bound`):

```
elpCount 2 u v · |K| ^ (2 (B - 1)) ≤ c ^ (2 (B - 1)) · |Idx → K| ^ 4
```

that is, an expected linear probability of at most `(c / |K|) ^ (2 (B - 1))`. In a longer
schedule the other rounds are charged nothing (`elpCount_window_bound`,
`elpCount_bound_of_two_rounds`). A nonzero mask never reaches the zero mask
(`elpCount_zero_right`), so the window starts from a nonzero mask; the `j` rounds before it must
have injective maps, so that their rows sum to `|X| ^ (j + 2)` (`sum_elpCount_right`); the `m`
rounds after it need no hypothesis, since their columns sum to `|X| ^ (m + 2)` for every map
(`sum_elpCount_left`).

For AES, `c = 32`, `|K| = 256` and the branch number `5` of the backward map `aesLinT` give
`(32 / 256) ^ 8 = 2⁻²⁴`: for every nonzero input mask and every output mask, the expected linear
probability over two rounds, and over any `R ≥ 2` rounds, is at most `2⁻²⁴`
(`AES.two_round_elp`, `AES.rounds_elp`). This is coarse. Keliher and Sui give the exact maximum
two-round expected linear probability of AES as `109,953,193 / 2⁵⁴ ≈ 1.638 · 2⁻²⁸` (IACR ePrint
2005/321); that value is cited as context only and is not proved here.

The averaging is load-bearing. On the sixty-four-state toy of `Checks/Toy.lean` (two bundles of
three bits, the χ map with linearity bound `4`, and a linear layer whose adjoint has branch
number at least `3`), the bound allows `2²⁰` of a possible `2²⁴` and is attained
(`toy_two_round_bound`, `toy_elp_attained`); it fails with `B = 4`
(`toy_bound_fails_branch_four`), with `c = 2` (`toy_bound_fails_linearity_two`, in
`Checks/ToySpec.lean`), and with a non-injective S-box, where the count is `1114112 > 2²⁰`
(`toy_nonbijective_exceeds`). Under one fixed key the squared Walsh value at one pair of masks is
`1024`, four times the average `256` that the bound allows per key vector (`toy_fixed_exceeds`). `Checks/ToyNat.lean` recomputes the
bound at all `63 · 64` mask pairs on natural numbers, as a numerical cross-check written
independently of the library's definitions.

## 8. HADES rounds over prime fields

`Linear/Hades.lean` carries masks through the rounds of `WideTrail.Hades`,
`x ↦ L (S_mask (x + c))`, over any field `K`, under the pairing `⟨u, x⟩ = ℓ (u ⬝ᵥ x)` for an
additive `ℓ : K →+ G` (`(Pairing.traceForm ℓ).pi`; for `ZMod p` the intended `ℓ` is the
identity). The transpose of `L` is an adjoint, and masks move forward through
`maskLin L = (Lᵀ)⁻¹` (`Hades.maskLin_dotProduct`). `Hades.maskSchedule rounds` replaces each
round's linear layer by its forward mask map and keeps its mask, S-boxes and constant. The Walsh
value of a masked S-box layer is the product of the S-boxes' Walsh values on the mask and of
`|K| · [aᵢ = bᵢ]` off it (`Hades.walsh_masked`), so a mask passes unchanged where no S-box is
applied, and the bridge
`Hades.isTrail_of_linCorr_ne_zero` makes a trail with a nonzero correlation `Hades.linCorr` a
`Hades.IsTrail` of the mask schedule. Every activity theorem of the HADES layer then applies,
with the branch numbers and middle bounds of the forward mask maps
(`Hades.hades_linear_outer_activity`, `Hades.hades_linear_activity`).

Those are not the maps the differential certificates were proved for, and two transfers close
the gap. The branch numbers of `maskLin L` are those of the transpose
(`Hades.isBranchBound_maskLin_iff`), and for a layer `x ↦ M x` with `M` an MDS matrix of size
`t`, `maskLin L` has branch number at least `t + 1` (`Hades.isBranchBound_maskLin_of_isMDS`,
through `isMDS_transpose_iff`). A symmetric layer, such as the internal layer `c (diag d + J)`,
moves masks by its inverse (`Hades.maskLin_eq_symm_of_selfAdjoint`), and **a middle bound for
`L` is a middle bound for `L⁻¹`**, for the same rounds and the same count
(`Hades.MiddleBound.symm`): a trail through `m` rounds of `L⁻¹`, read backwards and shifted by
`L`, is a trail through `m` rounds of `L` with the same charged weight. The inactive-space
windows transfer the same way (`Hades.inactiveSpace_symm_eq_bot_iff`). So the window, relation
and automaton certificates of the differential side apply to masks, and every pinned instance
has the same lower bounds for masks (`Linear/Poseidon2.lean`, `Linear/Poseidon.lean`). For every
table of round constants, every linear trail of the rounds that follow the initial external
layer (Starknet has none) with a nonzero input mask and a nonzero correlation charges at least:

| Instance | Rounds | Count | With the certificate | External layer: linear branch number at least |
|---|---|---|---|---|
| SP1 and Pico KoalaBear | 28 | 33 | 35 | 8 |
| SP1 and OpenVM BabyBear | 21 | 32 | — | 8 |
| HorizenLabs BN254, width three | 64 | 34 | 43 | 4 |
| Aztec and Noir BN254, width four | 64 | 34 | 44 | 5 |
| Starknet | 91 | 43 | 57 | 4 (the one layer `M`) |

The theorems are `linear_activity_general` and `linear_activity_middle_general` in each
instance's namespace (`linear_activity_middle` for the pinned rounds; `linear_activity_general`
and `linear_activity` for BabyBear and OpenVM), and `external_isLinBranchBound`
(`mds_isLinBranchBound` for Starknet). The counts are lower bounds in the `IsTrail` model and are
not claimed to be attained. With the pinned constants and no key, the permutation's Walsh value,
times `|F ^ t| ^ (R - 1)`, is the sum of the trail correlations `linCorr` over all trails of its
`R` rounds (the column Rounds above), from `maskLin external u` where there is an initial layer
(`walsh_permutation_eq_sum_linCorr`); equivalently, the permutation's correlation is the sum of
the correlations of its trails.

**Why the S-box correlation bound is a hypothesis.** The trail bounds of these instances read
`abv (linCorr) · p ^ A ≤ C ^ A · |F ^ t| ^ R` (`linear_bound_middle_general`;
`linear_bound_general` for BabyBear and OpenVM), where `C` bounds every Walsh value of
`x ↦ x ^ d` at a nonzero input mask, and `C` is a hypothesis. Over `ZMod p` the natural
character is `ZMod.stdAddChar`, `j ↦ exp (2πi j / p)`, so a Walsh value is a complex character
sum. The fields have about `2³¹` to `2²⁵⁴` elements, so no kernel enumeration of the kind used
for the AES S-box is possible, and the standard bound, the Weil bound `(d - 1) √p`, rests on the
Riemann hypothesis for curves over finite fields, which is not proved in this library. So no
linear exponent is stated for any of these instances: only the activity counts are
unconditional.

The generic files stay light. `Linear/Hades.lean`, `Linear/Poseidon2.lean` and
`Linear/Poseidon.lean` work with any character `ψ : AddChar G R` into a domain for which the
pairing is separating, and with any absolute value `abv` on `R` that is `1` on the values of
`ψ`. `Linear/Field.lean` supplies the prime-field choices: `ZMod.stdAddChar` is separating for
the multiplication pairing (`Linear.mulPairing_separating`), its values have norm `1`
(`Linear.norm_stdAddChar`), and the HADES results are restated for it in norm form
(`Hades.hades_linear_bound_norm`, `Hades.isLinBranchBound_iff_maskLin_std`). Those facts need
`Mathlib.Analysis`, about 3.4 GB of memory to load, so `Field.lean` is the only module that
imports it, and it belongs to the library `WideTrailHeavy`: no module of the default library
imports it. Every instance field is `ZMod p`
for a proved prime `p`, so `Linear.mulPairing_separating` discharges the separation hypothesis
of the instance theorems; they are not restated with that character.

## 9. What is and is not claimed

Proved, with no remaining premise beyond those stated:

* the identities (W1) to (W10), each with the hypotheses named in section 1, and the binary
  case: integer Walsh values, Parseval and the bundle bound;
* the identification of the linear branch number with the differential branch number of the
  adjoint, for a separating pairing into a domain in which `|X| ≠ 0`;
* the fixed-key expansion for every key vector, the bridge from a nonzero trail correlation to
  `IsTrail`, and the trail bounds for a wide-trail specification and a linearity bound `c`;
* Markov composition, Nyberg's identity and the two-round hull bound in the independent-key
  model;
* for AES under the trace pairing: the S-box linearity bound `32`, attained; trail correlations
  of at most `2⁻⁷⁵`, `2⁻¹⁶⁵`, `2⁻²²⁵` and `2⁻²⁴⁰` over 4, 10, 12 and 14 rounds; the hull bound
  `2⁻²⁴` over any `R ≥ 2` rounds;
* for HADES rounds and the pinned Poseidon and Poseidon2 instances: the linear activity lower
  bounds of section 8, for every separating character into a domain, and, when the size of the
  state space is nonzero in the character's ring, the linear branch numbers of the external
  layers.

Not claimed:

* A trail bound bounds one trail: one summand of the fixed-key correlation, the same in
  magnitude for every key. It is not a bound on the cipher's correlation for a fixed key, a
  scheduled key or fixed round constants, which is a sum over all trails with key-dependent
  phases (signs `±1` in the binary case).
* Activity counts are lower bounds, from `IsTrail.bound_rounds` or the HADES activity theorems;
  they are not claimed to be attained. No statement is made about trails with a zero
  correlation.
* The hull bounds average over an additional independent uniform key per round. Nothing is said
  about the AES key schedule. Only two rounds are charged, and `2⁻²⁴` is not close to the exact
  two-round maximum.
* The AES rounds are those of `Differential/AESProb.lean`: every round has `MixColumns`, and
  there is no final round without it and no final whitening key. Rijndael with a 256-bit block
  is not treated.
* The bit pairing is not treated: the bit-pairing linear approximation table of the AES S-box is
  not computed, no bit-pairing bound is derived, and the designers' four-round bound for bit
  masks is not proved.
* Over prime fields no S-box correlation bound is proved (the Weil bound is not proved), so the
  trail bounds of the Poseidon and Poseidon2 instances take it as a hypothesis and no linear
  exponent is stated for them. Linear hulls over prime fields are not treated.
* Nothing here is a statement about the data or time complexity of a linear attack, or about the
  security of any cipher.
