/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Hades
import WideTrail.Poseidon2.KoalaBearMiddle
import WideTrail.Poseidon2.PicoKoalaBearMiddle
import WideTrail.Poseidon2.BabyBear
import WideTrail.Poseidon2.OpenVMBabyBear
import WideTrail.Poseidon2.BN254MiddleSharp
import WideTrail.Poseidon2.AztecBN254Middle

/-!
# Linear activity of the pinned Poseidon2 permutations

For each Poseidon2 instance pinned in `WideTrail.Poseidon2`, this file proves that every linear
trail through the rounds that follow the initial external layer, with a nonzero input mask and a
nonzero correlation (`Hades.linCorr`), charges at least as many S-boxes as the differential
counts of that instance: the same lower bounds, now for masks. The pairing is the dot product read
through any `ℓ : F →+ G`, `⟨u, x⟩ = ℓ (u ⬝ᵥ x)`, and the character `ψ : AddChar G R` is any
character into a domain for which this pairing is separating (`Field.lean` supplies
`ZMod.stdAddChar` with `ℓ = id`). Masks move forward through `maskLin L = (Lᵀ)⁻¹`
(`WideTrail.Linear.Hades`).

## The linear layers seen by masks

* Plonky3 width sixteen (SP1 KoalaBear and BabyBear, Pico KoalaBear, OpenVM BabyBear): the
  forward mask map of the external layer is the inverse of its transpose `circ(2 m4ᵀ, …, m4ᵀ)`
  (`Plonky3.external_maskLin_symm_apply`), which has branch number at least `8`
  (`Plonky3.external_transpose_isBranchBound`), so `maskLin external` does too
  (`Plonky3.external_maskLin_isBranchBound`). The internal layer `c (diag d + J)` is self-adjoint
  (`Plonky3.Diag.internal_dotProduct`), so `maskLin internal = internal⁻¹`
  (`Plonky3.Diag.internal_maskLin`), and a middle bound for `diag d + J` is one for the forward
  mask map (`Plonky3.Diag.maskLin_middleBound`, through `Hades.MiddleBound.symm`).
* HorizenLabs BN254 width three: `circ(2, 1, 1)` and `[[2, 1, 1], [1, 2, 1], [1, 1, 3]]` are
  symmetric (`BN254.externalMatrix_transpose`, `BN254.internalMatrix_transpose`), so both layers
  are self-adjoint and move masks by their inverses (`BN254.maskLin_external`,
  `BN254.maskLin_internal`).
* Aztec BN254 width four: `hlMat4` is not symmetric; its transpose is MDS
  (`isMDS_transpose_iff`), so `hlMat4ᵀ` has branch number at least `5`
  (`AztecBN254.hlMat4_transpose_isBranchBound`) and so does the forward mask map of the external
  layer, the inverse of `hlMat4ᵀ` (`AztecBN254.maskLin_external_symm_apply`). The internal layer
  `diag d + J` is self-adjoint.

## Results

For a character into a domain for which the pairing is separating, every linear trail with a
nonzero input mask and a nonzero correlation, for every table of round constants, charges at
least (`linear_activity_general`, `linear_activity_middle_general`; `linear_activity` and
`linear_activity_middle` for the pinned rounds):

| Instance | Rounds | Count | Count with a middle bound |
|---|---|---|---|
| SP1 KoalaBear, `x³`, `rP = 20` | `28` | `33` | `35` |
| Pico KoalaBear, `x³`, `rP = 20` | `28` | `33` | `35` |
| SP1 BabyBear, `x⁷`, `rP = 13` | `21` | `32` | — |
| OpenVM BabyBear, `x⁷`, `rP = 13` | `21` | `32` | — |
| HorizenLabs BN254 width 3, `x⁵`, `rP = 56` | `64` | `34` | `43` |
| Aztec BN254 width 4, `x⁵`, `rP = 56` | `64` | `34` | `44` |

These are the same lower bounds as the differential counts of `WideTrail.Poseidon2`, with the
same window and middle-bound certificates: `Hades.MiddleBound.symm` transfers every middle bound
of a layer to its inverse, for the same rounds and count, so the improved counts `35`, `43` and
`44` of the differential side hold for masks as well (`linear_activity_middle_general`). The
counts `33` and `34` use the inactive-space windows (`16`, `3` and `4` rounds) of the
differential side, transferred by `Hades.inactiveSpace_symm_eq_bot_iff` or `MiddleBound.symm`.

`linear_bound_middle_general` (and `linear_bound_general` for BabyBear): for an absolute value
`abv` with `abv (ψ t) = 1` and an S-box whose Walsh values at every nonzero input mask are at most
`C` under `abv` (**a hypothesis**: no S-box correlation bound is proved here), every such trail
has `abv (linCorr) · p ^ A ≤ C ^ A · |F ^ t| ^ R` with `A` the count of the last column (`32` for
BabyBear), `p` the field size and `R` the number of rounds.

`external_isLinBranchBound` (each instance): for a separating `ψ` into a domain in which
`|F ^ t|` is nonzero, the external layer has linear branch number (through correlations,
`Linear.IsLinBranchBound`) at least `8`, `4` and `5`: the bounds that `Algebra/Transpose.lean`
reads off the transposes by its definition, now as statements about correlations.

`walsh_permutation_eq_sum_linCorr` (each instance): the permutation applies the external layer
and then the rounds, so, for the pinned constants and with no key, its Walsh value at `(u, v)`,
times `|F ^ t| ^ (R - 1)`, is the sum of the trail correlations `linCorr` of the rounds over the
trails from `maskLin external u` to `v` (`Hades.walsh_comp_execute_eq_sum_linCorr`).

## What is not claimed

The counts are lower bounds on charged S-boxes in the `IsTrail` model, for linear trails of the
rounds that follow the initial external layer; they are not claimed to be attained, and no
statement is made about trails with a zero correlation. A trail bound bounds one trail: one
summand of the fixed-key expansion `Hades.walsh_run_eq_sum_linCorr`, whatever the key and the round
constants; it is not a bound on the correlation of the permutation, which is a sum over all trails
whose summands can reinforce or cancel, and nothing is said about linear hulls. The S-box
correlation bound `C` is a hypothesis: over these prime fields the Weil bound `(d - 1) √p` for
`x ↦ x ^ d` is not proved in this library. No instance file is changed.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

open Linear
open scoped Matrix

/-! ### The width-sixteen Plonky3 layers -/

namespace Poseidon2.Plonky3

variable {K : Type*} [Field K]

/-- **The forward mask map of the external layer is the inverse of its transpose**:
`(maskLin (external h35))⁻¹` is `circ(2 m4ᵀ, m4ᵀ, m4ᵀ, m4ᵀ)` on the flat state
(`external_dotProduct`). -/
theorem external_maskLin_symm_apply (h35 : (35 : K) ≠ 0) (y : Fin 16 → K) :
    (Hades.maskLin (external h35)).symm y =
      BlockCirculant.blockMix (B := Fin 4) (Matrix.mulVecLin (m4 K)ᵀ) (y ∘ blockIndex) ∘
        blockIndex.symm :=
  Hades.maskLin_symm_eq_of_dotProduct _ (external_dotProduct h35) y

/-- **Branch number `8` for the forward mask map of the external layer**, under the `m4Primes`
hypothesis: its inverse, the transpose of the external layer, has branch number at least `8`
(`external_transpose_isBranchBound`). -/
theorem external_maskLin_isBranchBound [DecidableEq K] (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0)
    (h35 : (35 : K) ≠ 0) : isBranchBound id (Hades.maskLin (external h35)) 8 :=
  (Hades.isBranchBound_maskLin_iff _ (external_dotProduct h35) 8).mpr
    (external_transpose_isBranchBound hprimes)

/-- **Linear branch number `8` for the external layer.** For a pairing `ℓ (u ⬝ᵥ x)` separating
for `ψ`, into a domain in which `|K ^ 16|` is nonzero, and under the `m4Primes` hypothesis,
every pair of masks `(u, v) ≠ (0, 0)` at which the external layer has a nonzero Walsh value has
at least `8` nonzero coordinates in total. -/
theorem external_isLinBranchBound [DecidableEq K] [Fintype K] {G R : Type*} [AddCommGroup G]
    [CommRing R] [IsDomain R] {ψ : AddChar G R} {ℓ : K →+ G}
    (hP : (Pairing.traceForm ℓ).Separating ψ) (hcard : (Fintype.card (Fin 16 → K) : R) ≠ 0)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (h35 : (35 : K) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) (external h35) 8 :=
  (Hades.isLinBranchBound_iff_maskLin hP hcard _ 8).mpr
    (external_maskLin_isBranchBound hprimes h35)

namespace Diag

/-- **The internal layer moves masks by its inverse**, for every diagonal: it is self-adjoint
(`internal_dotProduct`), so `maskLin internal = internal⁻¹`. -/
theorem internal_maskLin (d : Fin 16 → K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) :
    Hades.maskLin (internal d c hc hd hs) = (internal d c hc hd hs).symm :=
  Hades.maskLin_eq_symm_of_selfAdjoint _ (internal_dotProduct d c hc hd hs)

/-- **A middle bound for `diag d + J` is a middle bound for the forward mask map of the internal
layer**, for the same number of rounds and the same count: the scale `c` is invisible
(`middleBound_internal`), and the forward mask map is the inverse of the self-adjoint layer
(`Hades.MiddleBound.maskLin_of_selfAdjoint`). -/
theorem maskLin_middleBound [DecidableEq K] (d : Fin 16 → K) (c : K) (hc : c ≠ 0)
    (hd : ∀ i, d i ≠ 0) (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (mask : Finset (Fin 16)) (m μ : ℕ)
    (h : Hades.MiddleBound (diagPlusOnes (1 : K) d) mask m μ) :
    Hades.MiddleBound (Hades.maskLin (internal d c hc hd hs)).toLinearMap mask m μ :=
  Hades.MiddleBound.maskLin_of_selfAdjoint (internal_dotProduct d c hc hd hs)
    ((middleBound_internal d c hc hd hs mask m μ).mpr h)

variable [DecidableEq K] [Fintype K] {d : Fin 16 → K} {c : K} {G R : Type*} [AddCommGroup G]
  [CommRing R] [IsDomain R] {ψ : AddChar G R} {ℓ : K →+ G}

/-- **Thirty-two active S-boxes for masks, for every diagonal.** For a pairing `ℓ (u ⬝ᵥ x)`
separating for `ψ` into a domain, under the `m4Primes` hypothesis, every linear trail through the
`8 + rP` rounds of `Diag.rounds` with a nonzero input mask and a nonzero correlation charges at
least `32` S-boxes, all in the full rounds: the forward mask map of the external layer has
branch number at least `8`. For every S-box, scale and constant table. A lower bound. -/
theorem linear_activity (hP : (Pairing.traceForm ℓ).Separating ψ) (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (rounds hD rP sbox values) (8 + rP) T ≠ 0) :
    32 ≤ Hades.scheduledWeight (rounds hD rP sbox values) T 0 (8 + rP) := by
  rw [show 8 + rP = 4 + rP + 4 by omega] at h ⊢
  have hA := Hades.hades_linear_outer_activity hP 4 rP 4 8 {0} (fun _ _ => sbox) (linear hD rP)
    values (fun j hj => by
      rw [linear_prefix hD rP (show j < 4 by omega)]
      exact external_maskLin_isBranchBound hprimes hD.thirtyFive)
    (fun j _ => by
      rw [linear_suffix hD rP j]
      exact external_maskLin_isBranchBound hprimes hD.thirtyFive) h0 h
  exact le_trans (le_of_eq (by norm_num)) hA

/-- **The partial rounds charged, for masks, for every diagonal.** As `Diag.linear_activity`,
and if every trail through `rP` consecutive partial rounds with the unscaled layer `diag d + J`
and mask `{0}`, from a nonzero difference, charges at least `μ` S-boxes (`hμ`), every such
linear trail charges at least `32 + μ` S-boxes. The middle bound is the one of the differential
side: it transfers to the forward mask map `internal⁻¹` (`maskLin_middleBound`). -/
theorem linear_activity_with_middle_bound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hD : Conditions d c) (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {μ : ℕ}
    (hμ : Hades.MiddleBound (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) rP μ)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (rounds hD rP sbox values) (8 + rP) T ≠ 0) :
    32 + μ ≤ Hades.scheduledWeight (rounds hD rP sbox values) T 0 (8 + rP) := by
  rw [show 8 + rP = 4 + rP + 4 by omega] at h ⊢
  have hA := Hades.hades_linear_activity hP 4 rP 4 8 μ {0} (fun _ _ => sbox) (linear hD rP)
    values (fun j hj => by
      rw [linear_prefix hD rP (show j < 4 by omega)]
      exact external_maskLin_isBranchBound hprimes hD.thirtyFive)
    (fun j _ => by
      rw [linear_suffix hD rP j]
      exact external_maskLin_isBranchBound hprimes hD.thirtyFive)
    (Hades.maskLin (internal d c hD.scale hD.diag hD.shermanMorrison)).toLinearMap
    (fun j hj => by rw [linear_middle hD rP hj])
    (maskLin_middleBound d c _ _ _ {0} rP μ hμ) h0 h
  exact le_trans (le_of_eq (by norm_num)) hA

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

/-- **The linear trail bound with a middle bound, for every diagonal.** Under the hypotheses of
`Diag.linear_activity_with_middle_bound`, for an absolute value `abv` that is `1` on the values of
`ψ`, and an S-box whose Walsh values at every nonzero input mask are at most `C ≥ 0` under `abv`,
every linear trail with a nonzero input mask satisfies
`abv (linCorr) · |K| ^ (32 + μ) ≤ C ^ (32 + μ) · |K ^ 16| ^ (8 + rP)`. One trail: not the
correlation of the permutation. -/
theorem linear_bound_with_middle_bound (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {μ : ℕ} (hμ : Hades.MiddleBound (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) rP μ)
    {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : K, a ≠ 0 → ∀ b : K,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (rounds hD rP sbox values) (8 + rP) T) *
        (Fintype.card K : S) ^ (32 + μ) ≤
      C ^ (32 + μ) * (Fintype.card (Fin 16 → K) : S) ^ (8 + rP) := by
  by_cases hz : Hades.linCorr ψ ℓ (rounds hD rP sbox values) (8 + rP) T = 0
  · rw [hz, abv.map_zero, zero_mul]
    exact mul_nonneg (pow_nonneg hC0 _) (pow_nonneg (Nat.cast_nonneg _) _)
  · exact Hades.abv_linCorr_mul_card_pow_le_of_le abv hψ hC0 (rounds hD rP sbox values) (8 + rP)
      (fun _ _ _ _ => hC) T
      (linear_activity_with_middle_bound hP hD hprimes rP sbox values hμ h0 hz)

/-- **The linear trail bound from the full rounds, for every diagonal.** As
`Diag.linear_bound_with_middle_bound` with the `32` S-boxes of `Diag.linear_activity`:
`abv (linCorr) · |K| ^ 32 ≤ C ^ 32 · |K ^ 16| ^ (8 + rP)`. One trail. -/
theorem linear_bound (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : K, a ≠ 0 → ∀ b : K,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (rounds hD rP sbox values) (8 + rP) T) * (Fintype.card K : S) ^ 32 ≤
      C ^ 32 * (Fintype.card (Fin 16 → K) : S) ^ (8 + rP) := by
  by_cases hz : Hades.linCorr ψ ℓ (rounds hD rP sbox values) (8 + rP) T = 0
  · rw [hz, abv.map_zero, zero_mul]
    exact mul_nonneg (pow_nonneg hC0 _) (pow_nonneg (Nat.cast_nonneg _) _)
  · exact Hades.abv_linCorr_mul_card_pow_le_of_le abv hψ hC0 (rounds hD rP sbox values) (8 + rP)
      (fun _ _ _ _ => hC) T (linear_activity hP hD hprimes rP sbox values h0 hz)

end Diag

end Poseidon2.Plonky3

/-! ### SP1 KoalaBear -/

namespace Poseidon2.KoalaBear

variable {G R S : Type*} [AddCommGroup G] [CommRing R] [IsDomain R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : F →+ G}

/-- **Linear branch number `8`** for the external layer (`Plonky3.external_isLinBranchBound`). -/
theorem external_isLinBranchBound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hcard : (Fintype.card (Fin 16 → F) : R) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) external 8 :=
  Plonky3.external_isLinBranchBound hP hcard m4Primes_ne_zero conditions.thirtyFive

/-- **Thirty-three active S-boxes for masks, for every round-constant table.** Every linear trail
through the `28` rounds with a nonzero input mask and a nonzero correlation charges at least
`33` S-boxes: `32` in the full rounds and `20 / 16 = 1` in the partial rounds, from the window
`inactive_trivial`. The count of `activity_general`, for masks. A lower bound. -/
theorem linear_activity_general (hP : (Pairing.traceForm ℓ).Separating ψ) (table : ℕ → State)
    {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Plonky3.rounds conditions 20 sbox table) 28 T ≠ 0) :
    33 ≤ Hades.scheduledWeight (Plonky3.rounds conditions 20 sbox table) T 0 28 :=
  Plonky3.Diag.linear_activity_with_middle_bound hP conditions.toDiag m4Primes_ne_zero 20 sbox
    table (Hades.MiddleBound.of_inactiveSpace inactive_trivial 20) h0 h

/-- **Thirty-five active S-boxes for masks, for every round-constant table.** Every linear trail
through the `28` rounds with a nonzero input mask and a nonzero correlation charges at least
`35` S-boxes: `32` in the full rounds and `3` in the partial rounds, from the relation certificate
`middle_bound`, transferred to the forward mask map. The count of `activity_middle_general`, for
masks. A lower bound. -/
theorem linear_activity_middle_general (hP : (Pairing.traceForm ℓ).Separating ψ)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Plonky3.rounds conditions 20 sbox table) 28 T ≠ 0) :
    35 ≤ Hades.scheduledWeight (Plonky3.rounds conditions 20 sbox table) T 0 28 :=
  Plonky3.Diag.linear_activity_with_middle_bound hP conditions.toDiag m4Primes_ne_zero 20 sbox
    table middle_bound h0 h

/-- **Thirty-five active S-boxes for masks** for the pinned rounds. -/
theorem linear_activity_middle (hP : (Pairing.traceForm ℓ).Separating ψ) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (h : Hades.linCorr ψ ℓ rounds 28 T ≠ 0) :
    35 ≤ Hades.scheduledWeight rounds T 0 28 :=
  linear_activity_middle_general hP values h0 h

/-- **The linear trail bound, for every round-constant table.** For an absolute value `abv` that
is `1` on the values of `ψ`, if the S-box `x ↦ x³` has Walsh values at most `C ≥ 0` under `abv`
at every nonzero input mask (a hypothesis), every linear trail through the `28` rounds with a
nonzero input mask has `abv (linCorr) · p ^ 35 ≤ C ^ 35 · |F ^ 16| ^ 28`, `p = modulus`. One trail:
not the correlation of the permutation. -/
theorem linear_bound_middle_general (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : F, a ≠ 0 → ∀ b : F,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (Plonky3.rounds conditions 20 sbox table) 28 T) *
        (modulus : S) ^ 35 ≤ C ^ 35 * (Fintype.card (Fin 16 → F) : S) ^ 28 := by
  have h := Plonky3.Diag.linear_bound_with_middle_bound abv hψ hP conditions.toDiag
    m4Primes_ne_zero 20 sbox table middle_bound hC0 hC h0
  rwa [field_card] at h

/-- **The permutation's Walsh value is a sum of trail correlations.** The permutation applies the
external layer and then the `28` rounds, so, for the pinned round constants and with no key,
`|F ^ 16| ^ 27 · walsh permutation u v = ∑_d linCorr rounds 28 T_d` over the trails
`T_d = Scheduled.throughTrail (maskLin external u) d v` of the rounds
(`Hades.walsh_comp_execute_eq_sum_linCorr`). The summands can reinforce or cancel; the trail
bounds above bound each of them, not the sum. -/
theorem walsh_permutation_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (u v : State) :
    (Fintype.card (Fin 16 → F) : R) ^ 27 *
        walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi permutation u v =
      ∑ d : Fin 27 → State,
        Hades.linCorr ψ ℓ rounds 28 (Scheduled.throughTrail (Hades.maskLin external u) d v) := by
  rw [show (permutation : State → State) = fun x => Hades.execute rounds (external x) (27 + 1)
    from funext permutation_eq]
  exact Hades.walsh_comp_execute_eq_sum_linCorr hP external rounds 27 u v

end Poseidon2.KoalaBear

/-! ### Pico KoalaBear -/

namespace Poseidon2.PicoKoalaBear

open Poseidon2.KoalaBear (F State modulus field_card sbox m4Primes_ne_zero)

variable {G R S : Type*} [AddCommGroup G] [CommRing R] [IsDomain R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : F →+ G}

/-- **Linear branch number `8`** for the external layer (`Plonky3.external_isLinBranchBound`). -/
theorem external_isLinBranchBound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hcard : (Fintype.card (Fin 16 → F) : R) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) external 8 :=
  Plonky3.external_isLinBranchBound hP hcard m4Primes_ne_zero conditions.thirtyFive

/-- **Thirty-three active S-boxes for masks, for every round-constant table**: `32` in the full
rounds and `20 / 16 = 1` in the partial rounds, from the window `inactive_trivial`. The count of
`activity_general`, for masks. A lower bound. -/
theorem linear_activity_general (hP : (Pairing.traceForm ℓ).Separating ψ) (table : ℕ → State)
    {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Plonky3.Diag.rounds conditions 20 sbox table) 28 T ≠ 0) :
    33 ≤ Hades.scheduledWeight (Plonky3.Diag.rounds conditions 20 sbox table) T 0 28 :=
  Plonky3.Diag.linear_activity_with_middle_bound hP conditions m4Primes_ne_zero 20 sbox table
    (Hades.MiddleBound.of_inactiveSpace inactive_trivial 20) h0 h

/-- **Thirty-five active S-boxes for masks, for every round-constant table**: `32` in the full
rounds and `3` in the partial rounds, from the relation certificate `middle_bound`. The count of
`activity_middle_general`, for masks. A lower bound. -/
theorem linear_activity_middle_general (hP : (Pairing.traceForm ℓ).Separating ψ)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Plonky3.Diag.rounds conditions 20 sbox table) 28 T ≠ 0) :
    35 ≤ Hades.scheduledWeight (Plonky3.Diag.rounds conditions 20 sbox table) T 0 28 :=
  Plonky3.Diag.linear_activity_with_middle_bound hP conditions m4Primes_ne_zero 20 sbox table
    middle_bound h0 h

/-- **Thirty-five active S-boxes for masks** for the pinned rounds. -/
theorem linear_activity_middle (hP : (Pairing.traceForm ℓ).Separating ψ) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (h : Hades.linCorr ψ ℓ rounds 28 T ≠ 0) :
    35 ≤ Hades.scheduledWeight rounds T 0 28 :=
  linear_activity_middle_general hP values h0 h

/-- **The linear trail bound, for every round-constant table**: under an S-box correlation
bound `C ≥ 0` (a hypothesis), every linear trail through the `28` rounds with a nonzero input mask
has `abv (linCorr) · p ^ 35 ≤ C ^ 35 · |F ^ 16| ^ 28`. One trail. -/
theorem linear_bound_middle_general (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : F, a ≠ 0 → ∀ b : F,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (Plonky3.Diag.rounds conditions 20 sbox table) 28 T) *
        (modulus : S) ^ 35 ≤ C ^ 35 * (Fintype.card (Fin 16 → F) : S) ^ 28 := by
  have h := Plonky3.Diag.linear_bound_with_middle_bound abv hψ hP conditions
    m4Primes_ne_zero 20 sbox table middle_bound hC0 hC h0
  rwa [field_card] at h

/-- **The permutation's Walsh value is a sum of trail correlations.** The permutation applies the
external layer and then the `28` rounds, so, for the pinned round constants and with no key,
`|F ^ 16| ^ 27 · walsh permutation u v = ∑_d linCorr rounds 28 T_d` over the trails
`T_d = Scheduled.throughTrail (maskLin external u) d v` of the rounds
(`Hades.walsh_comp_execute_eq_sum_linCorr`). The summands can reinforce or cancel; the trail
bounds above bound each of them, not the sum. -/
theorem walsh_permutation_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (u v : State) :
    (Fintype.card (Fin 16 → F) : R) ^ 27 *
        walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi permutation u v =
      ∑ d : Fin 27 → State,
        Hades.linCorr ψ ℓ rounds 28 (Scheduled.throughTrail (Hades.maskLin external u) d v) := by
  rw [show (permutation : State → State) = fun x => Hades.execute rounds (external x) (27 + 1)
    from funext permutation_eq]
  exact Hades.walsh_comp_execute_eq_sum_linCorr hP external rounds 27 u v

end Poseidon2.PicoKoalaBear

/-! ### SP1 BabyBear -/

namespace Poseidon2.BabyBear

variable {G R S : Type*} [AddCommGroup G] [CommRing R] [IsDomain R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : F →+ G}

/-- **Linear branch number `8`** for the external layer (`Plonky3.external_isLinBranchBound`). -/
theorem external_isLinBranchBound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hcard : (Fintype.card (Fin 16 → F) : R) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) external 8 :=
  Plonky3.external_isLinBranchBound hP hcard m4Primes_ne_zero conditions.thirtyFive

/-- **Thirty-two active S-boxes for masks, for every round-constant table**, all in the full
rounds. The count of `activity_general`, for masks: with `13` partial rounds no window of `16`
fits, and the middle term is `0` (`partial_window_term_eq_zero`). A lower bound. -/
theorem linear_activity_general (hP : (Pairing.traceForm ℓ).Separating ψ) (table : ℕ → State)
    {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Plonky3.rounds conditions 13 sbox table) 21 T ≠ 0) :
    32 ≤ Hades.scheduledWeight (Plonky3.rounds conditions 13 sbox table) T 0 21 :=
  Plonky3.Diag.linear_activity hP conditions.toDiag m4Primes_ne_zero 13 sbox table h0 h

/-- **Thirty-two active S-boxes for masks** for the pinned rounds. -/
theorem linear_activity (hP : (Pairing.traceForm ℓ).Separating ψ) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (h : Hades.linCorr ψ ℓ rounds 21 T ≠ 0) :
    32 ≤ Hades.scheduledWeight rounds T 0 21 :=
  linear_activity_general hP values h0 h

/-- **The linear trail bound, for every round-constant table**: under an S-box correlation
bound `C ≥ 0` for `x ↦ x⁷` (a hypothesis), every linear trail through the `21` rounds with a
nonzero input mask has `abv (linCorr) · p ^ 32 ≤ C ^ 32 · |F ^ 16| ^ 21`. One trail. -/
theorem linear_bound_general (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : F, a ≠ 0 → ∀ b : F,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (Plonky3.rounds conditions 13 sbox table) 21 T) *
        (modulus : S) ^ 32 ≤ C ^ 32 * (Fintype.card (Fin 16 → F) : S) ^ 21 := by
  have h := Plonky3.Diag.linear_bound abv hψ hP conditions.toDiag m4Primes_ne_zero 13 sbox table
    hC0 hC h0
  rwa [field_card] at h

/-- **The permutation's Walsh value is a sum of trail correlations.** The permutation applies the
external layer and then the `21` rounds, so, for the pinned round constants and with no key,
`|F ^ 16| ^ 20 · walsh permutation u v = ∑_d linCorr rounds 21 T_d` over the trails
`T_d = Scheduled.throughTrail (maskLin external u) d v` of the rounds
(`Hades.walsh_comp_execute_eq_sum_linCorr`). The summands can reinforce or cancel; the trail
bounds above bound each of them, not the sum. -/
theorem walsh_permutation_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (u v : State) :
    (Fintype.card (Fin 16 → F) : R) ^ 20 *
        walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi permutation u v =
      ∑ d : Fin 20 → State,
        Hades.linCorr ψ ℓ rounds 21 (Scheduled.throughTrail (Hades.maskLin external u) d v) := by
  rw [show (permutation : State → State) = fun x => Hades.execute rounds (external x) (20 + 1)
    from funext permutation_eq]
  exact Hades.walsh_comp_execute_eq_sum_linCorr hP external rounds 20 u v

end Poseidon2.BabyBear

/-! ### OpenVM BabyBear -/

namespace Poseidon2.OpenVMBabyBear

open Poseidon2.BabyBear (F State modulus field_card sbox m4Primes_ne_zero)

variable {G R S : Type*} [AddCommGroup G] [CommRing R] [IsDomain R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : F →+ G}

/-- **Linear branch number `8`** for the external layer (`Plonky3.external_isLinBranchBound`). -/
theorem external_isLinBranchBound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hcard : (Fintype.card (Fin 16 → F) : R) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) external 8 :=
  Plonky3.external_isLinBranchBound hP hcard m4Primes_ne_zero conditions.thirtyFive

/-- **Thirty-two active S-boxes for masks, for every round-constant table**, all in the full
rounds. The count of `activity_general`, for masks. A lower bound. -/
theorem linear_activity_general (hP : (Pairing.traceForm ℓ).Separating ψ) (table : ℕ → State)
    {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Plonky3.Diag.rounds conditions 13 sbox table) 21 T ≠ 0) :
    32 ≤ Hades.scheduledWeight (Plonky3.Diag.rounds conditions 13 sbox table) T 0 21 :=
  Plonky3.Diag.linear_activity hP conditions m4Primes_ne_zero 13 sbox table h0 h

/-- **Thirty-two active S-boxes for masks** for the pinned rounds. -/
theorem linear_activity (hP : (Pairing.traceForm ℓ).Separating ψ) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (h : Hades.linCorr ψ ℓ rounds 21 T ≠ 0) :
    32 ≤ Hades.scheduledWeight rounds T 0 21 :=
  linear_activity_general hP values h0 h

/-- **The linear trail bound, for every round-constant table**: under an S-box correlation
bound `C ≥ 0` for `x ↦ x⁷` (a hypothesis), every linear trail through the `21` rounds with a
nonzero input mask has `abv (linCorr) · p ^ 32 ≤ C ^ 32 · |F ^ 16| ^ 21`. One trail. -/
theorem linear_bound_general (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : F, a ≠ 0 → ∀ b : F,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (Plonky3.Diag.rounds conditions 13 sbox table) 21 T) *
        (modulus : S) ^ 32 ≤ C ^ 32 * (Fintype.card (Fin 16 → F) : S) ^ 21 := by
  have h := Plonky3.Diag.linear_bound abv hψ hP conditions m4Primes_ne_zero 13 sbox table
    hC0 hC h0
  rwa [field_card] at h

/-- **The permutation's Walsh value is a sum of trail correlations.** The permutation applies the
external layer and then the `21` rounds, so, for the pinned round constants and with no key,
`|F ^ 16| ^ 20 · walsh permutation u v = ∑_d linCorr rounds 21 T_d` over the trails
`T_d = Scheduled.throughTrail (maskLin external u) d v` of the rounds
(`Hades.walsh_comp_execute_eq_sum_linCorr`). The summands can reinforce or cancel; the trail
bounds above bound each of them, not the sum. -/
theorem walsh_permutation_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (u v : State) :
    (Fintype.card (Fin 16 → F) : R) ^ 20 *
        walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi permutation u v =
      ∑ d : Fin 20 → State,
        Hades.linCorr ψ ℓ rounds 21 (Scheduled.throughTrail (Hades.maskLin external u) d v) := by
  rw [show (permutation : State → State) = fun x => Hades.execute rounds (external x) (20 + 1)
    from funext permutation_eq]
  exact Hades.walsh_comp_execute_eq_sum_linCorr hP external rounds 20 u v

end Poseidon2.OpenVMBabyBear

/-! ### HorizenLabs BN254, width three -/

namespace Poseidon2.BN254

/-- **The external matrix `circ(2, 1, 1)` is symmetric.** -/
theorem externalMatrix_transpose : externalMatrixᵀ = externalMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The internal matrix `[[2, 1, 1], [1, 2, 1], [1, 1, 3]]` is symmetric.** -/
theorem internalMatrix_transpose : internalMatrixᵀ = internalMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The external layer is self-adjoint: `external x ⬝ᵥ y = x ⬝ᵥ external y`. -/
theorem external_selfAdjoint (x y : State) : external x ⬝ᵥ y = x ⬝ᵥ external y :=
  Hades.selfAdjoint_of_mulVec external_eq_mulVec externalMatrix_transpose x y

/-- The internal layer is self-adjoint: `internal x ⬝ᵥ y = x ⬝ᵥ internal y`. -/
theorem internal_selfAdjoint (x y : State) : internal x ⬝ᵥ y = x ⬝ᵥ internal y :=
  Hades.selfAdjoint_of_mulVec internal_eq_mulVec internalMatrix_transpose x y

/-- **The external layer moves masks by its inverse.** -/
theorem maskLin_external : Hades.maskLin external = external.symm :=
  Hades.maskLin_eq_symm_of_selfAdjoint external external_selfAdjoint

/-- **The internal layer moves masks by its inverse.** -/
theorem maskLin_internal : Hades.maskLin internal = internal.symm :=
  Hades.maskLin_eq_symm_of_selfAdjoint internal internal_selfAdjoint

/-- **Branch number `4` for the forward mask map of the external layer** (MDS,
`Hades.isBranchBound_maskLin_of_isMDS`). -/
theorem maskLin_external_isBranchBound : isBranchBound id (Hades.maskLin external) 4 :=
  Hades.isBranchBound_maskLin_of_isMDS external_mds external external_eq_mulVec

/-- **No nonzero mask stays off the S-box coordinate through three rounds of the forward mask
map of the internal layer**: `internal_inactive_trivial` for `internal⁻¹`
(`Hades.inactiveSpace_symm_eq_bot_iff`). -/
theorem maskLin_internal_inactive_trivial :
    Hades.inactiveSpace (Hades.maskLin internal).toLinearMap ({0} : Finset (Fin 3)) 3 = ⊥ := by
  rw [maskLin_internal, Hades.inactiveSpace_symm_eq_bot_iff]
  exact internal_inactive_trivial

/-- **The middle bound `27` for the forward mask map of the internal layer**: `middle_bound`,
transferred to `internal⁻¹` (`Hades.MiddleBound.maskLin_of_selfAdjoint`). -/
theorem maskLin_middle_bound :
    Hades.MiddleBound (Hades.maskLin internal).toLinearMap ({0} : Finset (Fin 3)) 56 27 :=
  Hades.MiddleBound.maskLin_of_selfAdjoint internal_selfAdjoint middle_bound

/-- The branch hypothesis of the first full block, for the forward mask maps. -/
theorem maskLin_full_prefix (j : ℕ) (hj : j + 1 < 4) :
    isBranchBound id (Hades.maskLin (linear j)) 4 := by
  rw [show linear j = external by simp [linear, show j < 4 by omega]]
  exact maskLin_external_isBranchBound

/-- The branch hypothesis of the second full block, for the forward mask maps. -/
theorem maskLin_full_suffix (j : ℕ) (_hj : j + 1 < 4) :
    isBranchBound id (Hades.maskLin (linear (4 + 56 + j))) 4 := by
  rw [show linear (4 + 56 + j) = external by simp [linear, show 60 ≤ 4 + 56 + j by omega]]
  exact maskLin_external_isBranchBound

variable {G R S : Type*} [AddCommGroup G] [CommRing R] [IsDomain R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : F →+ G}

/-- **Linear branch number `4`** for the external layer: for a pairing `ℓ (u ⬝ᵥ x)` separating
for `ψ`, into a domain in which `|F ^ 3|` is nonzero. -/
theorem external_isLinBranchBound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hcard : (Fintype.card (Fin 3 → F) : R) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) external 4 :=
  (Hades.isLinBranchBound_iff_maskLin hP hcard external 4).mpr maskLin_external_isBranchBound

/-- **Thirty-four active S-boxes for masks, for every round-constant table.** Every linear trail
through the `64` rounds with a nonzero input mask and a nonzero correlation charges at least
`34` S-boxes: `16` in the full rounds and `56 / 3 = 18` in the partial rounds, one per window of
three (`maskLin_internal_inactive_trivial`). The count of `activity_with_partial`, for masks. A
lower bound. -/
theorem linear_activity_general (hP : (Pairing.traceForm ℓ).Separating ψ) (table : ℕ → State)
    {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) 64 T
      ≠ 0) :
    34 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      T 0 64 :=
  Hades.hades_linear_activity hP 4 56 4 4 (56 / 3) {0} (fun _ _ => sbox) linear table
    maskLin_full_prefix maskLin_full_suffix (Hades.maskLin internal).toLinearMap
    (fun j hj => by rw [linear_middle j hj])
    (Hades.MiddleBound.of_inactiveSpace maskLin_internal_inactive_trivial 56) h0 h

/-- **Forty-three active S-boxes for masks, for every round-constant table**: `16` in the full
rounds and `27` in the partial rounds, from the automaton certificate `middle_bound` transferred
to the forward mask map (`maskLin_middle_bound`). The count of `activity_middle_general`, for
masks. A lower bound. -/
theorem linear_activity_middle_general (hP : (Pairing.traceForm ℓ).Separating ψ)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) 64 T
      ≠ 0) :
    43 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      T 0 64 :=
  Hades.hades_linear_activity hP 4 56 4 4 27 {0} (fun _ _ => sbox) linear table
    maskLin_full_prefix maskLin_full_suffix (Hades.maskLin internal).toLinearMap
    (fun j hj => by rw [linear_middle j hj]) maskLin_middle_bound h0 h

/-- **Forty-three active S-boxes for masks** for the pinned rounds. -/
theorem linear_activity_middle (hP : (Pairing.traceForm ℓ).Separating ψ) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (h : Hades.linCorr ψ ℓ rounds 64 T ≠ 0) :
    43 ≤ Hades.scheduledWeight rounds T 0 64 :=
  linear_activity_middle_general hP values h0 h

/-- **The linear trail bound, for every round-constant table**: under an S-box correlation
bound `C ≥ 0` for `x ↦ x⁵` (a hypothesis), every linear trail through the `64` rounds with a
nonzero input mask has `abv (linCorr) · p ^ 43 ≤ C ^ 43 · |F ^ 3| ^ 64`. One trail. -/
theorem linear_bound_middle_general (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : F, a ≠ 0 → ∀ b : F,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) 64 T) *
        (modulus : S) ^ 43 ≤ C ^ 43 * (Fintype.card (Fin 3 → F) : S) ^ 64 := by
  have h := Hades.hades_linear_bound abv hψ hP 4 56 4 4 27 {0} (fun _ _ => sbox) linear table
    hC0 (fun _ _ _ => hC) maskLin_full_prefix maskLin_full_suffix
    (Hades.maskLin internal).toLinearMap (fun j hj => by rw [linear_middle j hj])
    maskLin_middle_bound h0
  rwa [field_card] at h

/-- **The permutation's Walsh value is a sum of trail correlations.** The permutation applies the
external layer and then the `64` rounds, so, for the pinned round constants and with no key,
`|F ^ 3| ^ 63 · walsh permutation u v = ∑_d linCorr rounds 64 T_d` over the trails
`T_d = Scheduled.throughTrail (maskLin external u) d v` of the rounds
(`Hades.walsh_comp_execute_eq_sum_linCorr`). The summands can reinforce or cancel; the trail
bounds above bound each of them, not the sum. -/
theorem walsh_permutation_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (u v : State) :
    (Fintype.card (Fin 3 → F) : R) ^ 63 *
        walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi permutation u v =
      ∑ d : Fin 63 → State,
        Hades.linCorr ψ ℓ rounds 64 (Scheduled.throughTrail (Hades.maskLin external u) d v) := by
  exact Hades.walsh_comp_execute_eq_sum_linCorr hP external rounds 63 u v

end Poseidon2.BN254

/-! ### Aztec BN254, width four -/

namespace Poseidon2.AztecBN254

open Poseidon2.BN254 (modulus F field_card sbox)

/-- **`hlMat4ᵀ` has branch number at least `5`** over the BN254 field: it is MDS
(`isMDS_transpose_iff` and `external_mds`). -/
theorem hlMat4_transpose_isBranchBound : isBranchBound id (hlMat4 F)ᵀ.mulVec 5 := by
  intro a ha
  rw [colWeight_id, colWeight_id]
  exact isMDS_branch_bound (isMDS_transpose_iff.mpr external_mds) a
    (by have := Hades.one_le_weight ha; omega)

/-- **The forward mask map of the external layer is the inverse of `hlMat4ᵀ`.** -/
theorem maskLin_external_symm_apply (y : State) :
    (Hades.maskLin external).symm y = (hlMat4 F)ᵀ *ᵥ y :=
  Hades.maskLin_symm_eq_of_dotProduct external (Hades.dotProduct_of_mulVec external_eq_mulVec) y

/-- **Branch number `5` for the forward mask map of the external layer**: its inverse `hlMat4ᵀ`
has branch number at least `5` (`hlMat4_transpose_isBranchBound`). -/
theorem maskLin_external_isBranchBound : isBranchBound id (Hades.maskLin external) 5 :=
  (Hades.isBranchBound_maskLin_iff external (Hades.dotProduct_of_mulVec external_eq_mulVec) 5).mpr
    hlMat4_transpose_isBranchBound

/-- The internal layer `diag d + J` is self-adjoint (`Poseidon2.diagPlusOnes_dotProduct`). -/
theorem internal_selfAdjoint (x y : State) : internal x ⬝ᵥ y = x ⬝ᵥ internal y := by
  have h : ∀ v, internal v = diagPlusOnes (1 : F) internalDiag v := fun v =>
    LinearMap.congr_fun internal_toLinearMap v
  rw [h, h]
  exact diagPlusOnes_dotProduct 1 internalDiag x y

/-- **The internal layer moves masks by its inverse.** -/
theorem maskLin_internal : Hades.maskLin internal = internal.symm :=
  Hades.maskLin_eq_symm_of_selfAdjoint internal internal_selfAdjoint

/-- **No nonzero mask stays off the S-box coordinate through four rounds of the forward mask
map of the internal layer**: `internal_inactive_trivial` for `internal⁻¹`. -/
theorem maskLin_internal_inactive_trivial :
    Hades.inactiveSpace (Hades.maskLin internal).toLinearMap ({0} : Finset (Fin 4)) 4 = ⊥ := by
  rw [maskLin_internal, Hades.inactiveSpace_symm_eq_bot_iff]
  exact internal_inactive_trivial

/-- **The middle bound `24` for the forward mask map of the internal layer**: `middle_bound`,
transferred to `internal⁻¹`. -/
theorem maskLin_middle_bound :
    Hades.MiddleBound (Hades.maskLin internal).toLinearMap ({0} : Finset (Fin 4)) 56 24 :=
  Hades.MiddleBound.maskLin_of_selfAdjoint internal_selfAdjoint middle_bound

/-- The branch hypothesis of the first full block, for the forward mask maps. -/
theorem maskLin_full_prefix (j : ℕ) (hj : j + 1 < 4) :
    isBranchBound id (Hades.maskLin (linear j)) 5 := by
  rw [linear_prefix (show j < 4 by omega)]
  exact maskLin_external_isBranchBound

/-- The branch hypothesis of the second full block, for the forward mask maps. -/
theorem maskLin_full_suffix (j : ℕ) (_hj : j + 1 < 4) :
    isBranchBound id (Hades.maskLin (linear (4 + 56 + j))) 5 := by
  rw [linear_suffix]
  exact maskLin_external_isBranchBound

variable {G R S : Type*} [AddCommGroup G] [CommRing R] [IsDomain R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : F →+ G}

/-- **Linear branch number `5`** for the external layer `hlMat4`: for a pairing `ℓ (u ⬝ᵥ x)`
separating for `ψ`, into a domain in which `|F ^ 4|` is nonzero. -/
theorem external_isLinBranchBound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hcard : (Fintype.card (Fin 4 → F) : R) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) external 5 :=
  (Hades.isLinBranchBound_iff_maskLin hP hcard external 5).mpr maskLin_external_isBranchBound

/-- **Thirty-four active S-boxes for masks, for every round-constant table.** Every linear trail
through the `64` rounds with a nonzero input mask and a nonzero correlation charges at least
`34` S-boxes: `20` in the full rounds and `56 / 4 = 14` in the partial rounds, one per window of
four (`maskLin_internal_inactive_trivial`). The count of `activity_with_partial_general`, for
masks. A lower bound. -/
theorem linear_activity_general (hP : (Pairing.traceForm ℓ).Separating ψ) (table : ℕ → State)
    {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) 64 T
      ≠ 0) :
    34 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      T 0 64 :=
  Hades.hades_linear_activity hP 4 56 4 5 (56 / 4) {0} (fun _ _ => sbox) linear table
    maskLin_full_prefix maskLin_full_suffix (Hades.maskLin internal).toLinearMap
    (fun j hj => by rw [linear_middle hj])
    (Hades.MiddleBound.of_inactiveSpace maskLin_internal_inactive_trivial 56) h0 h

/-- **Forty-four active S-boxes for masks, for every round-constant table**: `20` in the full
rounds and `24` in the partial rounds, from the automaton certificate `middle_bound` transferred
to the forward mask map (`maskLin_middle_bound`). The count of `activity_middle_general`, for
masks. A lower bound. -/
theorem linear_activity_middle_general (hP : (Pairing.traceForm ℓ).Separating ψ)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) 64 T
      ≠ 0) :
    44 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      T 0 64 :=
  Hades.hades_linear_activity hP 4 56 4 5 24 {0} (fun _ _ => sbox) linear table
    maskLin_full_prefix maskLin_full_suffix (Hades.maskLin internal).toLinearMap
    (fun j hj => by rw [linear_middle hj]) maskLin_middle_bound h0 h

/-- **Forty-four active S-boxes for masks** for the pinned rounds. -/
theorem linear_activity_middle (hP : (Pairing.traceForm ℓ).Separating ψ) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (h : Hades.linCorr ψ ℓ rounds 64 T ≠ 0) :
    44 ≤ Hades.scheduledWeight rounds T 0 64 :=
  linear_activity_middle_general hP values h0 h

/-- **The linear trail bound, for every round-constant table**: under an S-box correlation
bound `C ≥ 0` for `x ↦ x⁵` (a hypothesis), every linear trail through the `64` rounds with a
nonzero input mask has `abv (linCorr) · p ^ 44 ≤ C ^ 44 · |F ^ 4| ^ 64`. One trail. -/
theorem linear_bound_middle_general (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : F, a ≠ 0 → ∀ b : F,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) 64 T) *
        (modulus : S) ^ 44 ≤ C ^ 44 * (Fintype.card (Fin 4 → F) : S) ^ 64 := by
  have h := Hades.hades_linear_bound abv hψ hP 4 56 4 5 24 {0} (fun _ _ => sbox) linear table
    hC0 (fun _ _ _ => hC) maskLin_full_prefix maskLin_full_suffix
    (Hades.maskLin internal).toLinearMap (fun j hj => by rw [linear_middle hj])
    maskLin_middle_bound h0
  rwa [field_card] at h

/-- **The permutation's Walsh value is a sum of trail correlations.** The permutation applies the
external layer and then the `64` rounds, so, for the pinned round constants and with no key,
`|F ^ 4| ^ 63 · walsh permutation u v = ∑_d linCorr rounds 64 T_d` over the trails
`T_d = Scheduled.throughTrail (maskLin external u) d v` of the rounds
(`Hades.walsh_comp_execute_eq_sum_linCorr`). The summands can reinforce or cancel; the trail
bounds above bound each of them, not the sum. -/
theorem walsh_permutation_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (u v : State) :
    (Fintype.card (Fin 4 → F) : R) ^ 63 *
        walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi permutation u v =
      ∑ d : Fin 63 → State,
        Hades.linCorr ψ ℓ rounds 64 (Scheduled.throughTrail (Hades.maskLin external u) d v) := by
  exact Hades.walsh_comp_execute_eq_sum_linCorr hP external rounds 63 u v

end Poseidon2.AztecBN254
