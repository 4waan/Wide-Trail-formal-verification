/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Character
import WideTrail.Linear.Binary
import WideTrail.Linear.Masks
import WideTrail.Linear.Trail
import WideTrail.Linear.Hull
import WideTrail.Linear.Checks.Character
import WideTrail.Linear.Checks.Conventions
import WideTrail.Linear.Checks.Axioms
import WideTrail.Linear.Checks.ToyOne
import WideTrail.Linear.Checks.Toy
import WideTrail.Linear.Checks.ToyNat
import WideTrail.Linear.Checks.ToySpec
import WideTrail.Linear.Checks.TrailAxioms
import WideTrail.Linear.AESSpectrum
import WideTrail.Linear.GF256Trace
import WideTrail.Linear.AESSbox
import WideTrail.Linear.Checks.AES
import WideTrail.Linear.Checks.AESAxioms
import WideTrail.Linear.AES
import WideTrail.Linear.Checks.AESCipher
import WideTrail.Linear.Checks.AESCipherAxioms
import WideTrail.Linear.Hades
import WideTrail.Linear.Poseidon2
import WideTrail.Linear.Poseidon
import WideTrail.Linear.Checks.Hades
import WideTrail.Linear.Checks.HadesAxioms

/-!
# Linear cryptanalysis: correlations, masks, trails and hulls

The correlation side of the wide-trail strategy, built from exact character sums:

* `Character`: pairings of masks with states, additive characters, the Walsh value
  `walsh ψ P Q F u v = ∑ₓ ψ (⟨v, F x⟩ - ⟨u, x⟩)`, adjoints, and the identities (W1)-(W10): keys
  and constants contribute phases, linear layers move masks through adjoints, bricklayer maps
  factor over bundles, orthogonality, multiplication of correlation matrices, the Walsh values of
  a map with an adjoint, zero masks, Parseval, and the scaling symmetry of inversion. The
  identities that need a separating pairing and a domain are marked as such;
* `Binary`: the sign character of `ZMod 2`, the bit pairing of `Idx → ZMod 2`, integer Parseval,
  linearity bounds and the bound on a bricklayer's Walsh values by its active bundles;
* `Masks`: the adjoint calculus, adjoints of bundle transpositions and of matrices under a
  trace-form pairing, branch numbers of a bijection and its inverse, the linear branch number of
  a map as the differential branch number of its adjoint (for a separating pairing), and the
  forward/backward readings of a mask trail. Masks are propagated forward through the inverse of
  an adjoint;
* `Trail`: the correlation `trailCorr` and the key phase `trailPhase` of a linear trail through
  the keyed rounds of `Scheduled.run`; the fixed-key expansion of the cipher's Walsh value as a
  signed sum over trails, for every key vector; the bridge from a nonzero trail correlation to
  `WideTrailSpec.IsTrail`; and, in the binary case, the bounds `|trailCorr| · 2 ^ (d · A) ≤
  |X| ^ r` and `|trailCorr| · |K| ^ A ≤ c ^ A · |X| ^ r` for the activity lower bound `A` of a
  wide-trail specification;
* `Hull`: the key-averaged squared correlation `elpCount` in the independent-key model; key
  averaging, Markov composition (including a second block of zero rounds), Nyberg's identity,
  row and column sums, and the two-round bound `(c / |K|) ^ (2 (B - 1))` for a backward map of
  branch number at least `B`, with its extension to a whole schedule;
* `Checks.Character`: (W1), (W6) and (W9) recomputed by the kernel on a 3-bit map, with negative
  controls for injectivity (Parseval rows) and separation ((W6) under the zero pairing);
* `Checks.Conventions`: on `GF(2⁸)`, every bit-pairing adjoint of `x ↦ 0x02 · x` maps `0x01` to
  `0x80`. Under every trace-form pairing, multiplication by `0x02` is an adjoint of itself and
  the field transpose of the `MixColumns` matrix is an adjoint of it; under the separating trace
  form with mask `0xA0`, every adjoint of `x ↦ 0x02 · x` maps `0x01` to `0x02`;
* `Checks.Axioms`: pinned axiom footprints;
* `Checks.ToyOne`: on a one-bundle 3-bit toy, the fixed-key expansion and Nyberg's identity
  instantiated and compared with the kernel's direct evaluation (the count `512` over `64` key
  pairs), and Nyberg's identity failing under a non-separating pairing;
* `Checks.Toy`: on a two-bundle toy with sixty-four states, the two-round hull bound and the trail
  bound instantiated and attained; the bound failing without bijective S-boxes or with a larger
  branch number; a fixed key whose squared correlation is four times the key-averaged bound;
* `Checks.ToyNat`: the toy's hull bound at all `63 · 64` mask pairs, recomputed on natural
  numbers as a numerical cross-check;
* `Checks.ToySpec`: the two-bundle toy as a wide-trail specification (columns of one bundle,
  branch number `1`), with the bridge, the specification-level trail bounds and the schedule hull
  bound instantiated; the bridge failing without bijective S-boxes, as a typed statement about
  `IsTrail`; the two-round bound failing at the zero masks and with a smaller linearity bound;
  and the fixed-key expansion failing under a non-separating pairing;
* `Checks.TrailAxioms`: pinned axiom footprints for the trail and hull results;
* `AESSpectrum`: on natural numbers, with no imports: for the truth table `gTab` of
  `z ↦ Tr(z⁻¹)` on `GF(2⁸)`, `|256 - 2 · mism w 256| ≤ 32` for every mask `w < 256`, checked by
  the kernel in four chunks; the value `32` is attained, and the check fails with `28`;
* `GF256Trace`: the trace of `GF(2⁸)` as the functional with mask `0xA0`, equal on every byte to
  the absolute trace `z + z² + ⋯ + z¹²⁸`; the table of `z ↦ trace z⁻¹`; the mask `phi c` of
  `z ↦ trace (c * z)`;
* `AESSbox`: the trace pairing of `GF(2⁸)` (separating), a trace adjoint of the linear part of the
  S-box's affine map, the reduction of every Walsh value of the AES S-box at a nonzero output
  mask to the spectrum of `AESSpectrum`, and the linearity bound `32` of the S-box under the trace
  pairing (`AES.sbox_isLinearityBound`, so every such correlation is at most `2⁻³` in absolute
  value), attained at `(0x55, 0x01)`, so that `32` is the least linearity bound under this
  pairing;
* `Checks.AES`: the witness `-32` evaluated directly from the definition; the bound failing at
  `31`, without the hypothesis `b ≠ 0`, and on the spectrum at `28`; `32 · 2³ ≤ 256 < 32 · 2⁴`;
  the affine map not being a trace adjoint of itself; and `GF256.trace` equal to the functional
  `trA0` of `Checks.Conventions`;
* `Checks.AESAxioms`: pinned axiom footprints for the AES S-box results;
* `AES`: AES under the trace pairing. The field transpose `mixColumnsT` of `MixColumns` and
  `aesLinT = ShiftRows⁻¹ ∘ mixColumnsT` are trace adjoints of `MixColumns` and of
  `aesLin = MixColumns ∘ ShiftRows`. Masks are propagated forward by the specification
  `aesMaskSpec` (from `aesSpec`), with the same `ShiftRows` and the column-wise
  `(M⁻¹)ᵀ = circ(0e, 09, 0d, 0b)`; its linear layer is the inverse of `aesLinT`, and the backward
  reading is `maskTrail_iff_backward`. The backward maps have branch number at least `5`, and
  `MixColumns` and `aesLin` have linear branch number at least `5` (`isMDS_transpose_iff`). Every
  4-, 10-, 12- and 14-round linear trail with a nonzero input mask has a trail correlation of at
  most `2⁻⁷⁵`, `2⁻¹⁶⁵`, `2⁻²²⁵` and `2⁻²⁴⁰` in absolute value (at least `25`, `55`, `75` and `80`
  active S-boxes, each at most `2⁻³`; `rounds_correlation` for every round count); the expected
  linear probability over two rounds, and over any `R ≥ 2` rounds, is at most `2⁻²⁴` in the
  independent-key model;
* `Checks.AESCipher`: no linearity bound of the S-box clears `2⁴` per active S-box
  (`32 · 2⁴ > 256`); a non-MDS mix (`circ(0, 1, 1, 1)`, symmetric and an involution, so also the
  column layer of its own cipher's backward and forward mask maps) fails the branch hypotheses;
  the branch bound `5` cannot be raised to `6`; the forward mask map is not the state map; the
  hypotheses `T 0 ≠ 0` and `u ≠ 0` of the trail and hull bounds are needed;
* `Checks.AESCipherAxioms`: pinned axiom footprints for the AES trail and hull results;
* `Hades`: HADES rounds `x ↦ L (S_mask (x + c))` over a field `K`, under the pairing
  `⟨u, x⟩ = ℓ (u ⬝ᵥ x)` for any `ℓ : K →+ G`. Masks move forward through
  `maskLin L = (Lᵀ)⁻¹` (`maskLin_dotProduct`), and `maskSchedule` replaces every layer by its
  forward mask map. For a separating character into a domain: the Walsh value of a masked S-box
  layer (`walsh_masked`); the trail correlation `linCorr` and its fixed-key expansion; the Walsh
  value of the permutation with its fixed constants as the sum of the trail correlations; the
  bridge from a nonzero trail correlation to `Hades.IsTrail` of the mask schedule, and the
  equivalent backward reading through `Lᵀ` (`isTrail_maskSchedule_iff_backward`); inactive spaces
  and middle bounds of `L` transfer to `L⁻¹` (`inactiveSpace_symm_eq_bot_iff`,
  `MiddleBound.symm`); the linear activity of a HADES schedule from branch numbers and a middle
  bound of the forward mask maps; the linear branch number of a layer as the branch number of
  its forward mask map (when `|Idx → K| ≠ 0` in `R`); and, for an absolute value that is `1` on
  the character, the trail bound `abv (linCorr) · |K| ^ A ≤ c ^ A · |Idx → K| ^ r` with the S-box
  correlation bound `c` a hypothesis. It imports no `Mathlib.Analysis` module;
* `Poseidon2`: for the pinned Poseidon2 instances, every linear trail of the rounds after the
  initial external layer with a nonzero input mask and a nonzero correlation charges at least the
  same number of S-boxes as the differential counts: `33` and, with the relation certificates,
  `35` (SP1 and Pico KoalaBear); `32` (SP1 and OpenVM BabyBear); `34` and, with the automaton
  certificates, `43` (HorizenLabs BN254, width `3`) and `44` (Aztec BN254, width `4`). The
  external layers have linear branch number at least `8`, `4` and `5`; the trail bounds take the
  S-box correlation bound as a hypothesis; the permutation's Walsh value is the sum of its trail
  correlations;
* `Poseidon`: the same for Starknet's Poseidon permutation: at least `43`, and `57` with the
  automaton certificate;
* `Field`: for `ZMod p`, the standard character `ZMod.stdAddChar` is separating for the
  multiplication pairing and has values of norm `1`, so the results above hold with it and with
  the norm of `ℂ`, stated in norm form for HADES rounds. It is the only module here that imports
  `Mathlib.Analysis`, so this file does not import it: the library `WideTrailHeavy` does, and the
  default library never loads `Mathlib.Analysis`;
* `Checks.Hades`: `walsh_masked` and the bridge failing under a non-separating character; the
  zero trail, whose correlation is nonzero and which charges no S-box, so the hypothesis
  `T 0 ≠ 0` of the activity bounds is needed; the forward mask map of the BN254 external layer is
  not the layer;
* `Checks.HadesAxioms`: pinned axiom footprints for the HADES and Poseidon results.

Every module this file imports stays under about 3.1 GB of memory. `Field` needs about 3.4 GB,
almost all of it the `Mathlib.Analysis` import; it belongs to `WideTrailHeavy` and is audited by
`scripts/AuditAxiomsHeavy.lean`.

## What is not claimed

This file only imports the modules above and proves nothing itself. Apart from the 3-bit maps of the
checks (`chi3` and `andNext`, each with linearity bound `4`) and the AES S-box (linearity bound `32`
under the trace pairing, `AESSbox`), no S-box is shown to have a linearity bound. Apart from the toy
ciphers of the checks, the only concrete cipher with unconditional trail bounds, and the only one
with hull bounds, is AES (`AES`), under the trace pairing, with every round including `MixColumns`
and no final whitening key; the bit-pairing linear approximation table of the S-box is not treated,
no bit-pairing bound is derived (so the designers' four-round bound for bit masks is not proved),
and Rijndael with a 256-bit block is not treated. A trail bound bounds one trail: one summand of the
fixed-key correlation, the same in magnitude for every key; it is not a bound on the cipher's
correlation for a fixed key. Activity counts are lower bounds and are not claimed to be attained.
The hull bounds are averages over an additional independent uniform key per round; the AES bound
`2⁻²⁴` is coarse (the exact maximum two-round expected linear probability given by Keliher and Sui,
`≈ 1.638 · 2⁻²⁸`, is not proved here). The wide-trail specification of the toy (`Checks.ToySpec`)
has columns of one bundle and branch number `1`, so its instances of the specification-level trail
bounds show only that their hypotheses can be met together. For the Poseidon and Poseidon2 instances
(`Poseidon2`, `Poseidon`) only activity counts are proved: their trail bounds take the S-box
correlation bound as a hypothesis, and no bound on a Walsh value of `x ↦ x ^ d` over a prime field
(such as the Weil bound) is proved; their activity counts are lower bounds, the same as the
differential ones, and are not claimed to be attained. The claims, and the statements of what is not
claimed, are those of the individual modules.
-/

set_option autoImplicit false

namespace Linear

end Linear
