/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.AES
import Mathlib.Data.Fin.VecNotation

/-!
# Rijndael at block sizes 128, 192 and 256

AES fixes the block at `4 × 4`. Rijndael as submitted is specified for a `4 × Nb` state
with `Nb ∈ {4, …, 8}`, and it does not use the same ShiftRows offsets at every width:

| `Nb` | offsets      |
| ---- | ------------ |
| 4    | `0, 1, 2, 3` |
| 6    | `0, 1, 2, 3` |
| 8    | `0, 1, 3, 4` |

A square index type cannot even state the `Nb = 6, 8` cases, which is why `Grid.lean`
exists. With it, the whole family is three instantiations of one specification, and the
offsets become objects the kernel can rule on.

## What the formalisation decides, and what it does not

The natural reading of the table is that `0, 1, 2, 3` *fails* on a wide state and had to be
replaced. Definition 5 says otherwise, and says it by computation:

* `shiftOff256_diffusionOptimal`: the real offsets `0, 1, 3, 4` are diffusion-optimal on
  `4 × 8`;
* `shiftOff256naive_diffusionOptimal`: so are `0, 1, 2, 3`;
* `card_diffusionOptimal_offsets_256`: and so are `1680` other offset vectors.

So Definition 5 does not select the Rijndael-256 offsets, and no amount of wide-trail
reasoning will make it do so. The four-round bound of `25` holds for Rijndael-256 under
*either* choice; `rijndael256_fourteen_round` is stated for the real offsets and its proof
never inspects them beyond injectivity. The Rijndael submission lists three criteria for
the offsets, of which "the offsets have to be different mod `Nb`" is the first and is
exactly Definition 5; the other two are resistance to truncated-differential and to
saturation attacks, and neither is a wide-trail criterion or is formalised anywhere here.

The criterion is not vacuous, though, and the same `decide` shows it:

* `shiftOff256_not_diffusionOptimal_on_128`: the Rijndael-256 offsets are *illegal* on a
  `4 × 4` state, because `4 ≡ 0 mod 4` collides with row `0`. Definition 5 constrains the
  wide state loosely and the narrow state tightly, which is the opposite of the reading the
  table invites.
* `no_diffusionOptimal_four_by_three`: on a `4 × 3` state no dispersion at all is
  diffusion-optimal. This is not about ShiftRows; it is `card_fiber_le_card_col` from the
  abstract theory. Four bundles per column and three columns to scatter them into cannot
  be reconciled, so `Nb ≥ 4` is forced for a four-row state before any offset is chosen.

## One property that does separate them

Definition 5 is a one-round criterion. `shiftRowsPerm_trans` gives the smallest two-round
one: `π²` is again a ShiftRows, at the doubled offsets, so it has its own Definition 5
status. Doubling separates the two candidates, and in the direction opposite to the folk
reading: the real offsets make `π²` *not* diffusion-optimal, matching `Nb = 4` and
`Nb = 6`, whereas the naive offsets would make `π²` diffusion-optimal and so make `Nb = 8`
behave unlike every other width.

That is a computed fact about the two offset vectors, recorded because it is the one place
in reach where they differ. It is not a claim about the designers' reasoning, and nothing
downstream depends on it.
-/

set_option autoImplicit false

variable {K : Type*} [Zero K] [DecidableEq K]

/-! ### The offset vectors -/

/-- Rijndael's ShiftRows offsets at `Nb = 4`: the AES ones, `0, 1, 2, 3`. -/
def shiftOff128 : Fin 4 → Fin 4 := ![0, 1, 2, 3]

/-- Rijndael's ShiftRows offsets at `Nb = 6`, still `0, 1, 2, 3`. -/
def shiftOff192 : Fin 4 → Fin 6 := ![0, 1, 2, 3]

/-- Rijndael's ShiftRows offsets at `Nb = 8`: `0, 1, 3, 4`, not `0, 1, 2, 3`. -/
def shiftOff256 : Fin 4 → Fin 8 := ![0, 1, 3, 4]

/-- The offsets Rijndael-256 does *not* use, kept so the two can be compared as objects
rather than as prose. -/
def shiftOff256naive : Fin 4 → Fin 8 := ![0, 1, 2, 3]

/-- The Rijndael-256 offsets read on a `4 × 4` state, where `4` wraps to `0`. -/
def shiftOff256on128 : Fin 4 → Fin 4 := ![0, 1, 3, 4]

theorem shiftOff128_injective : Function.Injective shiftOff128 := by decide
theorem shiftOff192_injective : Function.Injective shiftOff192 := by decide
theorem shiftOff256_injective : Function.Injective shiftOff256 := by decide
theorem shiftOff256naive_injective : Function.Injective shiftOff256naive := by decide

/-! ### Definition 5 on each state shape -/

theorem shiftOff128_diffusionOptimal :
    DiffusionOptimal (gridCol 4 4) (shiftRowsPerm 4 4 shiftOff128) := by decide

theorem shiftOff192_diffusionOptimal :
    DiffusionOptimal (gridCol 4 6) (shiftRowsPerm 4 6 shiftOff192) := by decide

/-- The offsets Rijndael-256 actually uses are diffusion-optimal. -/
theorem shiftOff256_diffusionOptimal :
    DiffusionOptimal (gridCol 4 8) (shiftRowsPerm 4 8 shiftOff256) := by decide

/-- **And so are the offsets it does not use.** Definition 5 does not distinguish the two,
so it is not the reason Rijndael changed them at `Nb = 8`. -/
theorem shiftOff256naive_diffusionOptimal :
    DiffusionOptimal (gridCol 4 8) (shiftRowsPerm 4 8 shiftOff256naive) := by decide

/-- **The criterion still bites, in the other direction.** On a `4 × 4` state the offset
`4` wraps onto the offset `0`, two bundles of one column collide in one column of the
image, and Definition 5 fails. So the Rijndael-256 offsets are specific to the wide state,
even though the wide state does not require them. -/
theorem shiftOff256_not_diffusionOptimal_on_128 :
    ¬ DiffusionOptimal (gridCol 4 4) (shiftRowsPerm 4 4 shiftOff256on128) := by decide

/-! ### How loose Definition 5 is at each width

`card_diffusionOptimal_offsets` counts the admissible offset vectors in closed form. The
numbers are the measurement that turns "Definition 5 does not select the offsets" from an
observation about two vectors into a statement about the whole search space. -/

/-- `4 · 3 · 2 · 1` offset vectors are diffusion-optimal on the AES state. -/
theorem card_diffusionOptimal_offsets_128 :
    Fintype.card {off : Fin 4 → Fin 4 //
      DiffusionOptimal (gridCol 4 4) (shiftRowsPerm 4 4 off)} = 24 :=
  (card_diffusionOptimal_offsets 4 4).trans (by decide)

/-- `6 · 5 · 4 · 3` on the Rijndael-192 state. -/
theorem card_diffusionOptimal_offsets_192 :
    Fintype.card {off : Fin 4 → Fin 6 //
      DiffusionOptimal (gridCol 4 6) (shiftRowsPerm 4 6 off)} = 360 :=
  (card_diffusionOptimal_offsets 4 6).trans (by decide)

/-- `8 · 7 · 6 · 5` on the Rijndael-256 state. Definition 5 admits `1680` offset vectors
there, so it cannot be what picks out `0, 1, 3, 4`. -/
theorem card_diffusionOptimal_offsets_256 :
    Fintype.card {off : Fin 4 → Fin 8 //
      DiffusionOptimal (gridCol 4 8) (shiftRowsPerm 4 8 off)} = 1680 :=
  (card_diffusionOptimal_offsets 4 8).trans (by decide)

set_option maxRecDepth 100000 in
/-- **The closed form, checked against raw enumeration.** `card_diffusionOptimal_offsets`
reaches its answer through `Fintype.card_embedding_eq`, an argument that runs entirely in
the abstract: it never looks at a single offset vector. The chain it goes through
(`Equiv.subtypeEquivRight`, then `Equiv.subtypeInjectiveEquivEmbedding`, then the
`Fintype` instance on a subtype) has several places where a wrong-shaped instance would
produce a well-typed but meaningless number.

So on the one state small enough to enumerate, the kernel is asked to count instead: all
`256` offset vectors on `Fin 4 → Fin 4`, each tested against Definition 5 over all
`16 × 16` position pairs. -/
theorem card_diffusionOptimal_offsets_128_enumerated :
    (Finset.univ.filter (fun off : Fin 4 → Fin 4 =>
      DiffusionOptimal (gridCol 4 4) (shiftRowsPerm 4 4 off))).card = 24 := by decide

/-- The two routes agree. Neither is derived from the other: one is
`Fintype.card_embedding_eq`, the other is `decide` over the whole function space. -/
example : (Finset.univ.filter (fun off : Fin 4 → Fin 4 =>
      DiffusionOptimal (gridCol 4 4) (shiftRowsPerm 4 4 off))).card
    = Fintype.card {off : Fin 4 → Fin 4 //
        DiffusionOptimal (gridCol 4 4) (shiftRowsPerm 4 4 off)} :=
  card_diffusionOptimal_offsets_128_enumerated.trans
    card_diffusionOptimal_offsets_128.symm

/-! ### The state shape is forced before the offsets are

A four-row state needs at least four columns, and this is a theorem about every possible
dispersion layer, not about rotations. -/

/-- On a `4 × 3` state no permutation of the twelve bundle positions is diffusion-optimal,
so `Nb ≥ 4` is forced for a four-row Rijndael. -/
theorem no_diffusionOptimal_four_by_three (p : Equiv.Perm (GridIdx 4 3)) :
    ¬ DiffusionOptimal (gridCol 4 3) p :=
  not_diffusionOptimal_of_cols_lt 4 3 (by omega) p

/-! ### The two-round refinement

`π²` is a ShiftRows at the doubled offsets, so Definition 5 applies to it verbatim. This is
the one property in reach that separates the real Rijndael-256 offsets from the naive
ones. -/

/-- At `Nb = 4`, `π²` is not diffusion-optimal: `2 · (0,1,2,3) = (0,2,0,2) mod 4`. -/
theorem shiftOff128_sq_not_diffusionOptimal :
    ¬ DiffusionOptimal (gridCol 4 4)
      ((shiftRowsPerm 4 4 shiftOff128).trans (shiftRowsPerm 4 4 shiftOff128)) := by
  rw [diffusionOptimal_shiftRowsPerm_trans_self_iff]
  decide

/-- At `Nb = 6`, likewise: `2 · (0,1,2,3) = (0,2,4,0) mod 6`. -/
theorem shiftOff192_sq_not_diffusionOptimal :
    ¬ DiffusionOptimal (gridCol 4 6)
      ((shiftRowsPerm 4 6 shiftOff192).trans (shiftRowsPerm 4 6 shiftOff192)) := by
  rw [diffusionOptimal_shiftRowsPerm_trans_self_iff]
  decide

/-- At `Nb = 8` with the real offsets, likewise: `2 · (0,1,3,4) = (0,2,6,0) mod 8`. The
real offsets keep `Nb = 8` in line with every other width. -/
theorem shiftOff256_sq_not_diffusionOptimal :
    ¬ DiffusionOptimal (gridCol 4 8)
      ((shiftRowsPerm 4 8 shiftOff256).trans (shiftRowsPerm 4 8 shiftOff256)) := by
  rw [diffusionOptimal_shiftRowsPerm_trans_self_iff]
  decide

/-- At `Nb = 8` with the naive offsets, `π²` *is* diffusion-optimal:
`2 · (0,1,2,3) = (0,2,4,6) mod 8` is still injective. This is the only place in this
development where the two candidate offset vectors behave differently. -/
theorem shiftOff256naive_sq_diffusionOptimal :
    DiffusionOptimal (gridCol 4 8)
      ((shiftRowsPerm 4 8 shiftOff256naive).trans (shiftRowsPerm 4 8 shiftOff256naive)) := by
  rw [diffusionOptimal_shiftRowsPerm_trans_self_iff]
  decide

/-! ### The specifications and their bounds

MixColumns is the same `4 × 4` MDS map at every block size, acting one copy per column, so
the branch-number hypothesis has the same shape and the same value `5` throughout. Only the
number of columns and the number of rounds change. -/

/-- A Rijndael specification at block width `cols`: SubBytes, ShiftRows at `off`,
MixColumns of branch number `5`. -/
def rijndaelSpec (cols : ℕ) [NeZero cols] (off : Fin 4 → Fin cols)
    (hoff : Function.Injective off)
    (sbox mix : (GridIdx 4 cols → K) → (GridIdx 4 cols → K))
    (hsbox : PreserveSupport sbox) (hmix : IsColBranchBound (gridCol 4 cols) mix 5)
    (hnd : NonDegenerate mix) : WideTrailSpec (GridIdx 4 cols) (Fin cols) K :=
  gridSpec 4 cols off sbox mix 5 hsbox hoff hmix hnd

section Rijndael

variable (cols : ℕ) [NeZero cols] (off : Fin 4 → Fin cols) (hoff : Function.Injective off)
  (sbox mix : (GridIdx 4 cols → K) → (GridIdx 4 cols → K))
  (hsbox : PreserveSupport sbox) (hmix : IsColBranchBound (gridCol 4 cols) mix 5)
  (hnd : NonDegenerate mix)

@[simp] theorem rijndael_fourRoundBound :
    (rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).fourRoundBound = 25 := rfl

/-- **25 active S-boxes in four rounds, at every Rijndael block size.** The count does not
depend on `Nb`: a wider state has more columns, but Lemma 2 still only forces `B = 5` of
them to be active, and Lemma 1 still charges `B = 5` bundles to each. -/
theorem rijndael_four_round {a : GridIdx 4 cols → K} (ha : a ≠ 0) (n : ℕ) :
    25 ≤ weight ((rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).trail a n)
      + weight ((rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).trail a (n + 1))
      + weight ((rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).trail a (n + 2))
      + weight ((rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).trail a (n + 3)) :=
  (rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).four_round ha n

/-- The Rijndael bound at an arbitrary round count, at every block size. -/
theorem rijndael_rounds {a : GridIdx 4 cols → K} (ha : a ≠ 0) (r : ℕ) :
    r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0)
      ≤ (rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).trailWeight a r := by
  have h := (rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).trailWeight_bound_rounds ha r
  have e₁ : (rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).fourRoundBound = 25 := rfl
  have e₂ : (rijndaelSpec cols off hoff sbox mix hsbox hmix hnd).branch = 5 := rfl
  rwa [e₁, e₂] at h

end Rijndael

section Instances

variable (sbox₆ mix₆ : (GridIdx 4 6 → K) → (GridIdx 4 6 → K))
  (hsbox₆ : PreserveSupport sbox₆) (hmix₆ : IsColBranchBound (gridCol 4 6) mix₆ 5)
  (hnd₆ : NonDegenerate mix₆)

/-- **75 active S-boxes in the twelve rounds of Rijndael with a 192-bit block and a
192-bit key.** `12 = 3 · 4`, so the four-round tiling is exact. -/
theorem rijndael192_twelve_round {a : GridIdx 4 6 → K} (ha : a ≠ 0) :
    75 ≤ (rijndaelSpec 6 shiftOff192 shiftOff192_injective sbox₆ mix₆ hsbox₆ hmix₆
      hnd₆).trailWeight a 12 := by
  have h := rijndael_rounds 6 shiftOff192 shiftOff192_injective sbox₆ mix₆ hsbox₆ hmix₆
    hnd₆ ha 12
  have hval : (12 : ℕ) / 4 * 25 + (if 2 ≤ 12 % 4 then 5 else 0) = 75 := by decide
  omega

end Instances

section Instances256

variable (sbox₈ mix₈ : (GridIdx 4 8 → K) → (GridIdx 4 8 → K))
  (hsbox₈ : PreserveSupport sbox₈) (hmix₈ : IsColBranchBound (gridCol 4 8) mix₈ 5)
  (hnd₈ : NonDegenerate mix₈)

/-- **80 active S-boxes in the fourteen rounds of Rijndael with a 256-bit block and a
256-bit key.** Three four-round blocks and a two-round tail. -/
theorem rijndael256_fourteen_round {a : GridIdx 4 8 → K} (ha : a ≠ 0) :
    80 ≤ (rijndaelSpec 8 shiftOff256 shiftOff256_injective sbox₈ mix₈ hsbox₈ hmix₈
      hnd₈).trailWeight a 14 := by
  have h := rijndael_rounds 8 shiftOff256 shiftOff256_injective sbox₈ mix₈ hsbox₈ hmix₈
    hnd₈ ha 14
  have hval : (14 : ℕ) / 4 * 25 + (if 2 ≤ 14 % 4 then 5 else 0) = 80 := by decide
  omega

/-- The same bound holds under the offsets Rijndael-256 rejected, which is the sharpest
form of the negative result: the wide-trail guarantee is blind to the choice. -/
theorem rijndael256_fourteen_round_naive {a : GridIdx 4 8 → K} (ha : a ≠ 0) :
    80 ≤ (rijndaelSpec 8 shiftOff256naive shiftOff256naive_injective sbox₈ mix₈ hsbox₈
      hmix₈ hnd₈).trailWeight a 14 := by
  have h := rijndael_rounds 8 shiftOff256naive shiftOff256naive_injective sbox₈ mix₈ hsbox₈
    hmix₈ hnd₈ ha 14
  have hval : (14 : ℕ) / 4 * 25 + (if 2 ≤ 14 % 4 then 5 else 0) = 80 := by decide
  omega

end Instances256
