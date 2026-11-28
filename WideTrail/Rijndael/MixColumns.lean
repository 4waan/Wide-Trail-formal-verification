/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Propagation.Rijndael
import WideTrail.Algebra.AESMix

/-!
# Rijndael `MixColumns` at every block width, and unconditional active-S-box bounds

`Propagation/Rijndael.lean` states the Rijndael bounds with the branch number of `MixColumns`
and its invertibility as hypotheses (`rijndael256_fourteen_round`, `rijndael192_twelve_round`).
This file supplies the real map and discharges both, for every number of columns.

## The map

* `mixColumnsWith M cols` applies an `n × n` matrix `M` to each of the `cols` columns of an
  `n × cols` state. `localWeight_gridCol_eq_weight` reads the active bundles of one column of a
  grid state as the weight of that column, generalising `localWeight_sqCol_eq_weight` from the
  square state to `GridIdx`. For an MDS matrix, every column active on either side of the map
  carries at least `n + 1` active bundles (`mixColumnsWith_isColBranchBound`, from
  `isMDS_branch_bound`), and the map is additive and sends only `0` to `0`
  (`mixColumnsWith_add`, `mixColumnsWith_nondegenerate`).
* `mixColumns cols = mixColumnsWith aesMatrix cols` is Rijndael's `MixColumns` on a `4 × cols`
  state: the AES matrix `circ(02, 03, 01, 01)` over `GF(2⁸)`, applied to each column. At
  `cols = 4` it is `aesMixColumns` (`mixColumns_four`, by `rfl`).
* `mixColumns_isColBranchBound cols`: every column active on either side of `mixColumns cols`
  carries at least `5` active bytes across input and output. No hypothesis remains.
* `lin_isBranchBound cols off`: for every offset vector `off`, the whole-state linear layer
  `mixColumns cols ∘ transpose (shiftRowsPerm 4 cols off)` has branch number at least `5`.
  There is no injectivity hypothesis on `off`: `shiftRowsPerm 4 cols off` is a permutation for
  every `off`, so it does not change the number of active bytes.

## The specifications and the bounds

`linSpec cols off hoff` is `rijndaelSpec` with this `MixColumns`, ShiftRows at `off`, and the
placeholder `id` in the S-box field, as in `aesLinSpec`. `IsTrail` reads only the linear
layer, so the S-box field is never used (`isTrail_rijndaelSpec_iff`). `rijndael256LinSpec` and
`rijndael192LinSpec` are its instances at `Nb = 8` with offsets `0, 1, 3, 4` and at `Nb = 6`
with offsets `0, 1, 2, 3`.

For every sequence of difference patterns `T` with `T 0 ≠ 0` that is a trail of the
specification (`IsTrail`), with no branch-number or invertibility hypothesis:

| statement                             | state   | rounds          | active S-boxes, at least |
| ------------------------------------- | ------- | --------------- | ------------------------ |
| `rijndael256_four_round_concrete`     | `4 × 8` | any 4 in a row  | `25`                     |
| `rijndael256_rounds_concrete`         | `4 × 8` | `r`             | `r / 4 · 25` (`+ 5`)     |
| `rijndael256_fourteen_round_concrete` | `4 × 8` | `14`            | `80`                     |
| `rijndael192_four_round_concrete`     | `4 × 6` | any 4 in a row  | `25`                     |
| `rijndael192_rounds_concrete`         | `4 × 6` | `r`             | `r / 4 · 25` (`+ 5`)     |
| `rijndael192_twelve_round_concrete`   | `4 × 6` | `12`            | `75`                     |

Here `r / 4` is integer division, and the `+ 5` applies when `r % 4 ≥ 2`.

These are `IsTrail.four_round` and `IsTrail.bound_rounds` at the real `MixColumns`. Three
corollaries, `rijndael256_four_round_concrete_trail`, `rijndael256_fourteen_round_concrete_trail`
and `rijndael192_twelve_round_concrete_trail`, state the bounds `25`, `80` and `75` for the
functional trail `trail a` (with `a ≠ 0`) of `rijndaelSpec` with any support-preserving S-box
layer, in the shape of `rijndael256_fourteen_round`; each is the corresponding `IsTrail`
statement at `T = trail a`. There is no functional-trail form of the `r`-round statements or
of the Rijndael-192 four-round statement.

## What is not claimed

These are lower bounds on the number of active S-boxes of a differential trail, in the trail
model of `WideTrailSpec`. They are not claimed to be attained or to be the minimum activities;
no minimum is computed here. Nothing here is about probabilities, the S-box, the key schedule,
a fixed key, linear trails, differentials (as opposed to trails), or any attack. The `4 × 8`
statements use the real Rijndael-256 offsets `0, 1, 3, 4`, but the proofs read the offsets only
through injectivity, so the same bounds hold for every injective offset vector
(`four_round_concrete`, `rounds_concrete`). Every round of the trail model includes
`MixColumns`; the final round of the cipher, which omits it, is not modelled here.
-/

set_option autoImplicit false

namespace Rijndael

/-! ### Columns of a grid state -/

/-- The active bundles of column `ξ` of a grid state are the active entries of that column:
`localWeight_sqCol_eq_weight` on `GridIdx rows cols` instead of the square state. -/
theorem localWeight_gridCol_eq_weight {K : Type*} [Zero K] [DecidableEq K] (rows cols : ℕ)
    (ξ : Fin cols) (s : GridIdx rows cols → K) :
    localWeight (gridCol rows cols) ξ s = weight (fun r => s (r, ξ)) := by
  have himg : (activePattern s).filter (fun i => gridCol rows cols i = ξ)
      = (activePattern (fun r => s (r, ξ))).image (fun r => (r, ξ)) := by
    ext ⟨r, c⟩
    simp only [Finset.mem_filter, mem_activePattern, gridCol, Finset.mem_image]
    constructor
    · rintro ⟨hne, rfl⟩; exact ⟨r, hne, rfl⟩
    · rintro ⟨r', hne, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      exact ⟨hne, rfl⟩
  rw [localWeight, himg,
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq .. |>.mp h).1)]
  rfl

/-! ### A matrix applied to each column -/

section With

variable {K : Type*} [Field K] {n : ℕ}

/-- The `n × n` matrix `M` applied to each of the `cols` columns of an `n × cols` state. -/
def mixColumnsWith (M : Matrix (Fin n) (Fin n) K) (cols : ℕ) (a : GridIdx n cols → K) :
    GridIdx n cols → K :=
  fun i => M.mulVec (fun r => a (r, i.2)) i.1

/-- Column `ξ` of the output is `M` times column `ξ` of the input. -/
theorem mixColumnsWith_column (M : Matrix (Fin n) (Fin n) K) (cols : ℕ)
    (a : GridIdx n cols → K) (ξ : Fin cols) :
    (fun r => mixColumnsWith M cols a (r, ξ)) = M.mulVec (fun r => a (r, ξ)) := rfl

/-- `mixColumnsWith M cols` is additive. -/
theorem mixColumnsWith_add (M : Matrix (Fin n) (Fin n) K) (cols : ℕ)
    (x y : GridIdx n cols → K) :
    mixColumnsWith M cols (x + y) = mixColumnsWith M cols x + mixColumnsWith M cols y := by
  funext i
  change M.mulVec ((fun r => x (r, i.2)) + (fun r => y (r, i.2))) i.1 = _
  rw [Matrix.mulVec_add]
  rfl

/-- **For an MDS matrix, every column active on either side carries at least `n + 1` active
bundles across input and output.** This is `isMDS_branch_bound`, column by column. -/
theorem mixColumnsWith_isColBranchBound [DecidableEq K] {M : Matrix (Fin n) (Fin n) K}
    (hM : IsMDS M) (cols : ℕ) :
    IsColBranchBound (gridCol n cols) (mixColumnsWith M cols) (n + 1) := by
  intro a ξ hpos
  rw [localWeight_gridCol_eq_weight, localWeight_gridCol_eq_weight, mixColumnsWith_column]
    at hpos ⊢
  exact isMDS_branch_bound hM (fun r => a (r, ξ)) hpos

/-- For an MDS matrix, only the zero state is sent to zero. -/
theorem mixColumnsWith_nondegenerate {M : Matrix (Fin n) (Fin n) K} (hM : IsMDS M)
    (cols : ℕ) : NonDegenerate (mixColumnsWith M cols) := by
  classical
  intro a ha
  funext ⟨r, c⟩
  have hcol : (fun r' => a (r', c)) = 0 := by
    apply isMDS_injective hM
    rw [Matrix.mulVec_zero, ← mixColumnsWith_column M cols a c]
    funext r'
    exact congrFun ha (r', c)
  exact congrFun hcol r

end With

/-! ### Rijndael `MixColumns` -/

/-- **Rijndael's `MixColumns` on a `4 × cols` state**: the AES matrix `circ(02, 03, 01, 01)`
over `GF(2⁸)`, applied to each column. -/
def mixColumns (cols : ℕ) : (GridIdx 4 cols → GF256) → (GridIdx 4 cols → GF256) :=
  mixColumnsWith aesMatrix cols

theorem mixColumns_apply (cols : ℕ) (a : GridIdx 4 cols → GF256) (i : GridIdx 4 cols) :
    mixColumns cols a i = aesMatrix.mulVec (fun r => a (r, i.2)) i.1 := rfl

/-- At `cols = 4` this is the AES `MixColumns` of `Algebra/AESMix.lean`. -/
theorem mixColumns_four : mixColumns 4 = aesMixColumns := rfl

/-- `MixColumns` is additive. -/
theorem mixColumns_add (cols : ℕ) (x y : GridIdx 4 cols → GF256) :
    mixColumns cols (x + y) = mixColumns cols x + mixColumns cols y :=
  mixColumnsWith_add aesMatrix cols x y

/-- `MixColumns` sends only the zero state to zero. -/
theorem mixColumns_nondegenerate (cols : ℕ) : NonDegenerate (mixColumns cols) :=
  mixColumnsWith_nondegenerate aesMatrix_isMDS cols

/-- **Every column active on either side of `MixColumns` carries at least `5` active bytes
across input and output**, at every block width. This is the hypothesis `hmix` of
`rijndaelSpec`, discharged. -/
theorem mixColumns_isColBranchBound (cols : ℕ) :
    IsColBranchBound (gridCol 4 cols) (mixColumns cols) 5 :=
  mixColumnsWith_isColBranchBound aesMatrix_isMDS cols

/-- `MixColumns` alone has branch number at least `5` over the whole state. -/
theorem mixColumns_isBranchBound (cols : ℕ) : isBranchBound id (mixColumns cols) 5 :=
  fun a ha => by
    rw [colWeight_id, colWeight_id]
    exact branch_le_weight_add (mixColumns_isColBranchBound cols) ha

/-- **The whole-state linear layer `MixColumns ∘ ShiftRows` has branch number at least `5`**,
for every offset vector `off`. No injectivity of `off` is needed: `shiftRowsPerm 4 cols off`
is a permutation of the bundle positions for every `off`, so it does not change the number of
active bytes. -/
theorem lin_isBranchBound (cols : ℕ) [NeZero cols] (off : Fin 4 → Fin cols) :
    isBranchBound id (mixColumns cols ∘ transpose (shiftRowsPerm 4 cols off)) 5 :=
  fun a ha => by
    rw [colWeight_id, colWeight_id, Function.comp_apply,
      ← (supportPerm_transpose (shiftRowsPerm 4 cols off)).weight_eq a]
    exact branch_le_weight_add (mixColumns_isColBranchBound cols)
      ((supportPerm_transpose (shiftRowsPerm 4 cols off)).ne_zero ha)

/-! ### The specifications -/

/-- The Rijndael specification at block width `cols` with the real `MixColumns` and
ShiftRows at `off`. The `sbox` field is the placeholder `id`, as in `aesLinSpec`: `IsTrail`
reads only the linear layer (`isTrail_rijndaelSpec_iff`). -/
def linSpec (cols : ℕ) [NeZero cols] (off : Fin 4 → Fin cols) (hoff : Function.Injective off) :
    WideTrailSpec (GridIdx 4 cols) (Fin cols) GF256 :=
  rijndaelSpec cols off hoff id (mixColumns cols) (fun _ => rfl)
    (mixColumns_isColBranchBound cols) (mixColumns_nondegenerate cols)

/-- Rijndael with a 256-bit block: `Nb = 8`, ShiftRows offsets `0, 1, 3, 4`. -/
def rijndael256LinSpec : WideTrailSpec (GridIdx 4 8) (Fin 8) GF256 :=
  linSpec 8 shiftOff256 shiftOff256_injective

/-- Rijndael with a 192-bit block: `Nb = 6`, ShiftRows offsets `0, 1, 2, 3`. -/
def rijndael192LinSpec : WideTrailSpec (GridIdx 4 6) (Fin 6) GF256 :=
  linSpec 6 shiftOff192 shiftOff192_injective

section Spec

variable (cols : ℕ) [NeZero cols] (off : Fin 4 → Fin cols) (hoff : Function.Injective off)

@[simp] theorem linSpec_fourRoundBound : (linSpec cols off hoff).fourRoundBound = 25 := rfl

@[simp] theorem linSpec_branch : (linSpec cols off hoff).branch = 5 := rfl

/-- The linear layer of the specification is `MixColumns ∘ ShiftRows`. -/
theorem linSpec_lin :
    (linSpec cols off hoff).lin = mixColumns cols ∘ transpose (shiftRowsPerm 4 cols off) := rfl

/-- The linear layer of the specification has branch number at least `5`. -/
theorem linSpec_lin_isBranchBound : isBranchBound id (linSpec cols off hoff).lin 5 :=
  lin_isBranchBound cols off

/-- The linear layer of the specification is additive. -/
theorem linSpec_lin_add (x y : GridIdx 4 cols → GF256) :
    (linSpec cols off hoff).lin (x + y) = (linSpec cols off hoff).lin x
      + (linSpec cols off hoff).lin y := by
  change mixColumns cols (transpose (shiftRowsPerm 4 cols off) (x + y)) = _
  rw [show transpose (shiftRowsPerm 4 cols off) (x + y)
      = transpose (shiftRowsPerm 4 cols off) x + transpose (shiftRowsPerm 4 cols off) y from rfl,
    mixColumns_add]
  rfl

/-- **`IsTrail` does not read the S-box field.** A sequence is a trail of `rijndaelSpec` with
the real `MixColumns` and any support-preserving S-box layer exactly when it is a trail of
`linSpec`. -/
theorem isTrail_rijndaelSpec_iff (sbox : (GridIdx 4 cols → GF256) → (GridIdx 4 cols → GF256))
    (hsbox : PreserveSupport sbox) (T : ℕ → GridIdx 4 cols → GF256) (r : ℕ) :
    (rijndaelSpec cols off hoff sbox (mixColumns cols) hsbox (mixColumns_isColBranchBound cols)
        (mixColumns_nondegenerate cols)).IsTrail T r
      ↔ (linSpec cols off hoff).IsTrail T r := Iff.rfl

/-- **25 active S-boxes in any four consecutive rounds of every trail**, at block width
`cols`, for every injective offset vector. -/
theorem four_round_concrete {T : ℕ → GridIdx 4 cols → GF256} {r n : ℕ}
    (h : (linSpec cols off hoff).IsTrail T r) (h0 : T 0 ≠ 0) (hn : n + 3 ≤ r) :
    25 ≤ weight (T n) + weight (T (n + 1)) + weight (T (n + 2)) + weight (T (n + 3)) :=
  h.four_round h0 hn

/-- **The bound at every round count, for every trail**, at block width `cols`: `r / 4`
four-round blocks of `25`, plus `5` when at least two rounds are left over. -/
theorem rounds_concrete {T : ℕ → GridIdx 4 cols → GF256} {r : ℕ}
    (h : (linSpec cols off hoff).IsTrail T r) (h0 : T 0 ≠ 0) :
    r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0) ≤ patternWeight T r :=
  h.bound_rounds h0

end Spec

/-! ### Rijndael-256 -/

@[simp] theorem rijndael256LinSpec_fourRoundBound : rijndael256LinSpec.fourRoundBound = 25 :=
  rfl

@[simp] theorem rijndael256LinSpec_branch : rijndael256LinSpec.branch = 5 := rfl

/-- The linear layer of Rijndael-256 is `MixColumns ∘ ShiftRows` at offsets `0, 1, 3, 4`. -/
theorem rijndael256LinSpec_lin :
    rijndael256LinSpec.lin = mixColumns 8 ∘ transpose (shiftRowsPerm 4 8 shiftOff256) := rfl

/-- The whole-state linear layer of Rijndael-256 has branch number at least `5`. -/
theorem rijndael256LinSpec_lin_isBranchBound : isBranchBound id rijndael256LinSpec.lin 5 :=
  lin_isBranchBound 8 shiftOff256

/-- **Rijndael-256: at least 25 active S-boxes in any four consecutive rounds of every
differential trail.** No hypothesis on `MixColumns` remains. -/
theorem rijndael256_four_round_concrete {T : ℕ → GridIdx 4 8 → GF256} {r n : ℕ}
    (h : rijndael256LinSpec.IsTrail T r) (h0 : T 0 ≠ 0) (hn : n + 3 ≤ r) :
    25 ≤ weight (T n) + weight (T (n + 1)) + weight (T (n + 2)) + weight (T (n + 3)) :=
  four_round_concrete 8 shiftOff256 shiftOff256_injective h h0 hn

/-- **Rijndael-256 at every round count, for every differential trail.** -/
theorem rijndael256_rounds_concrete {T : ℕ → GridIdx 4 8 → GF256} {r : ℕ}
    (h : rijndael256LinSpec.IsTrail T r) (h0 : T 0 ≠ 0) :
    r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0) ≤ patternWeight T r :=
  rounds_concrete 8 shiftOff256 shiftOff256_injective h h0

/-- **Rijndael-256: at least 80 active S-boxes in 14 rounds of every differential trail.**
Three four-round blocks and a two-round tail: `3 · 25 + 5`. -/
theorem rijndael256_fourteen_round_concrete {T : ℕ → GridIdx 4 8 → GF256}
    (h : rijndael256LinSpec.IsTrail T 14) (h0 : T 0 ≠ 0) : 80 ≤ patternWeight T 14 := by
  have hb := rijndael256_rounds_concrete h h0
  have hval : (14 : ℕ) / 4 * 25 + (if 2 ≤ 14 % 4 then 5 else 0) = 80 := by decide
  omega

/-! ### Rijndael-192 -/

@[simp] theorem rijndael192LinSpec_fourRoundBound : rijndael192LinSpec.fourRoundBound = 25 :=
  rfl

/-- The whole-state linear layer of Rijndael-192 has branch number at least `5`. -/
theorem rijndael192LinSpec_lin_isBranchBound : isBranchBound id rijndael192LinSpec.lin 5 :=
  lin_isBranchBound 6 shiftOff192

/-- **Rijndael-192: at least 25 active S-boxes in any four consecutive rounds of every
differential trail.** -/
theorem rijndael192_four_round_concrete {T : ℕ → GridIdx 4 6 → GF256} {r n : ℕ}
    (h : rijndael192LinSpec.IsTrail T r) (h0 : T 0 ≠ 0) (hn : n + 3 ≤ r) :
    25 ≤ weight (T n) + weight (T (n + 1)) + weight (T (n + 2)) + weight (T (n + 3)) :=
  four_round_concrete 6 shiftOff192 shiftOff192_injective h h0 hn

/-- **Rijndael-192 at every round count, for every differential trail.** -/
theorem rijndael192_rounds_concrete {T : ℕ → GridIdx 4 6 → GF256} {r : ℕ}
    (h : rijndael192LinSpec.IsTrail T r) (h0 : T 0 ≠ 0) :
    r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0) ≤ patternWeight T r :=
  rounds_concrete 6 shiftOff192 shiftOff192_injective h h0

/-- **Rijndael-192: at least 75 active S-boxes in 12 rounds of every differential trail.**
`12 = 3 · 4`, so the four-round tiling is exact. -/
theorem rijndael192_twelve_round_concrete {T : ℕ → GridIdx 4 6 → GF256}
    (h : rijndael192LinSpec.IsTrail T 12) (h0 : T 0 ≠ 0) : 75 ≤ patternWeight T 12 := by
  have hb := rijndael192_rounds_concrete h h0
  have hval : (12 : ℕ) / 4 * 25 + (if 2 ≤ 12 % 4 then 5 else 0) = 75 := by decide
  omega

/-! ### The functional trail

The statements of `Propagation/Rijndael.lean`, for the trail `trail a` generated by a fixed
support-preserving S-box layer, with the real `MixColumns` and no remaining hypothesis on it.
Each is the `IsTrail` statement above at `T = trail a`. -/

section Functional

variable (sbox₈ : (GridIdx 4 8 → GF256) → (GridIdx 4 8 → GF256)) (hsbox₈ : PreserveSupport sbox₈)
  (sbox₆ : (GridIdx 4 6 → GF256) → (GridIdx 4 6 → GF256)) (hsbox₆ : PreserveSupport sbox₆)

/-- Rijndael-256 with the real `MixColumns`: 25 active S-boxes in any four consecutive rounds
of the functional trail. -/
theorem rijndael256_four_round_concrete_trail {a : GridIdx 4 8 → GF256} (ha : a ≠ 0) (n : ℕ) :
    25 ≤ weight ((rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ (mixColumns 8) hsbox₈
        (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)).trail a n)
      + weight ((rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ (mixColumns 8) hsbox₈
        (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)).trail a (n + 1))
      + weight ((rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ (mixColumns 8) hsbox₈
        (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)).trail a (n + 2))
      + weight ((rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ (mixColumns 8) hsbox₈
        (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)).trail a (n + 3)) :=
  rijndael256_four_round_concrete
    ((rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ (mixColumns 8) hsbox₈
      (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)).isTrail_trail a (n + 3))
    ha (le_refl _)

/-- **Rijndael-256 with the real `MixColumns`: 80 active S-boxes in the fourteen rounds of the
functional trail.** `rijndael256_fourteen_round` without its hypotheses on `MixColumns`. -/
theorem rijndael256_fourteen_round_concrete_trail {a : GridIdx 4 8 → GF256} (ha : a ≠ 0) :
    80 ≤ (rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ (mixColumns 8) hsbox₈
      (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)).trailWeight a 14 :=
  rijndael256_fourteen_round_concrete
    ((rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ (mixColumns 8) hsbox₈
      (mixColumns_isColBranchBound 8) (mixColumns_nondegenerate 8)).isTrail_trail a 14) ha

/-- **Rijndael-192 with the real `MixColumns`: 75 active S-boxes in the twelve rounds of the
functional trail.** `rijndael192_twelve_round` without its hypotheses on `MixColumns`. -/
theorem rijndael192_twelve_round_concrete_trail {a : GridIdx 4 6 → GF256} (ha : a ≠ 0) :
    75 ≤ (rijndaelSpec 6 shiftOff192 shiftOff192_injective sbox₆ (mixColumns 6) hsbox₆
      (mixColumns_isColBranchBound 6) (mixColumns_nondegenerate 6)).trailWeight a 12 :=
  rijndael192_twelve_round_concrete
    ((rijndaelSpec 6 shiftOff192 shiftOff192_injective sbox₆ (mixColumns 6) hsbox₆
      (mixColumns_isColBranchBound 6) (mixColumns_nondegenerate 6)).isTrail_trail a 12) ha

end Functional

end Rijndael
