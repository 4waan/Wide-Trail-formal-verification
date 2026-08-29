/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.Cipher
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Rectangular states and the ShiftRows family

Rijndael is specified for a `4 × Nb` state with `Nb ∈ {4, 5, 6, 7, 8}`, not just the
`4 × 4` of AES. A square index type cannot express that, so the state here is
`GridIdx rows cols = Fin rows × Fin cols`, partitioned into columns by `Prod.snd`, and the
dispersion layer is ShiftRows with an arbitrary *offset vector* `off : Fin rows → Fin cols`
rotating row `r` by `off r`.

Nothing above this file changes. `WideTrailSpec` and the four-round theorem were already
stated for an arbitrary index type and an arbitrary column map, so widening the state costs
no new theory; what it buys is a place to *test* the abstraction against a design decision
that was actually made.

The whole file turns on one equivalence:

```
DiffusionOptimal (gridCol rows cols) (shiftRowsPerm rows cols off) ↔ Function.Injective off
```

Definition 5 asks that the bundles of one column land in pairwise distinct columns. Two
bundles of one column differ only in their row, and ShiftRows moves them to columns
`c + off r` and `c + off r'`; those are distinct exactly when `off r ≠ off r'`. So the
paper's geometric condition on a permutation of `rows · cols` positions collapses to
injectivity of a function on `rows` points, and the kernel can then settle any concrete
candidate by `decide` and count all the admissible ones in closed form.

Two consequences fall straight out:

* `rows_le_cols_of_diffusionOptimal`: a state with more rows than columns admits no
  diffusion-optimal dispersion at all, and not merely no ShiftRows-shaped one. This is
  `card_fiber_le_card_col` from the abstract theory, evaluated on a grid.
* `card_diffusionOptimal_offsets`: the number of offset vectors Definition 5 admits is
  `cols.descFactorial rows`, so the criterion is a counting statement, not a unique
  prescription. `Rijndael.lean` uses this to measure how much of the actual Rijndael
  design choice the wide-trail strategy accounts for.
-/

set_option autoImplicit false

variable {K : Type*} [Zero K] [DecidableEq K]

/-- A rectangular state, indexed by `(row, column)`. -/
abbrev GridIdx (rows cols : ℕ) := Fin rows × Fin cols

/-- The column partition of a rectangular state: the α-sets are the columns. -/
abbrev gridCol (rows cols : ℕ) : GridIdx rows cols → Fin cols := Prod.snd

/-- ShiftRows as a permutation of bundle positions, for an arbitrary offset vector.

Reading the paper's convention `bᵢ = a_{p(i)}`, the bundle at `(r, c)` of the output is
the bundle at `(r, c + off r)` of the input: row `r` is rotated left by `off r`. -/
def shiftRowsPerm (rows cols : ℕ) [NeZero cols] (off : Fin rows → Fin cols) :
    Equiv.Perm (GridIdx rows cols) where
  toFun i := (i.1, i.2 + off i.1)
  invFun i := (i.1, i.2 - off i.1)
  left_inv := fun i => by simp
  right_inv := fun i => by simp

@[simp] theorem shiftRowsPerm_apply (rows cols : ℕ) [NeZero cols] (off : Fin rows → Fin cols)
    (i : GridIdx rows cols) : shiftRowsPerm rows cols off i = (i.1, i.2 + off i.1) := rfl

/-! ### Diffusion optimality is injectivity of the offset vector -/

/-- **Definition 5, solved.** ShiftRows with offsets `off` is diffusion-optimal on a
`rows × cols` state exactly when `off` is injective.

Left to right: put two bundles in column `0`, one in row `r` and one in row `r'`. They
land in columns `off r` and `off r'`, which Definition 5 forces to differ.
Right to left: two distinct bundles of one column share their column `c` and so differ in
their row, and `c + off r = c + off r'` cancels to `off r = off r'`. -/
theorem diffusionOptimal_shiftRowsPerm_iff (rows cols : ℕ) [NeZero cols]
    (off : Fin rows → Fin cols) :
    DiffusionOptimal (gridCol rows cols) (shiftRowsPerm rows cols off)
      ↔ Function.Injective off := by
  constructor
  · intro h r r' hoff
    by_contra hne
    refine h (r, 0) (r', 0) (fun hEq => hne (congrArg Prod.fst hEq)) rfl ?_
    simp only [shiftRowsPerm_apply, gridCol, hoff]
  · rintro hinj ⟨r, c⟩ ⟨r', c'⟩ hne hcol
    simp only [gridCol] at hcol
    subst hcol
    simp only [shiftRowsPerm_apply, gridCol]
    intro hEq
    exact hne (congrArg (fun r => (r, c)) (hinj (add_left_cancel hEq)))

/-- The offsets of a diffusion-optimal ShiftRows are pairwise distinct: this is the
"the offsets have to be different mod `Nb`" criterion of the Rijndael specification, and
`diffusionOptimal_shiftRowsPerm_iff` says it is not merely necessary but the *entire*
content of Definition 5 for this family. -/
theorem offsets_ne_of_diffusionOptimal {rows cols : ℕ} [NeZero cols]
    {off : Fin rows → Fin cols}
    (h : DiffusionOptimal (gridCol rows cols) (shiftRowsPerm rows cols off))
    {r r' : Fin rows} (hne : r ≠ r') : off r ≠ off r' :=
  fun hEq => hne ((diffusionOptimal_shiftRowsPerm_iff rows cols off).mp h hEq)

/-! ### A wide state needs wide rows

The bound here is not about ShiftRows. It is `card_fiber_le_card_col`, proved once in the
abstract theory for every column map and every dispersion, and simply evaluated on a grid:
a column holds `rows` bundles and there are `cols` columns to scatter them into. -/

/-- **No dispersion at all is diffusion-optimal on a state with more rows than columns.**
Not "no rotation": no permutation of the `rows · cols` bundle positions whatsoever. -/
theorem rows_le_cols_of_diffusionOptimal (rows cols : ℕ) [NeZero cols]
    (p : Equiv.Perm (GridIdx rows cols))
    (h : DiffusionOptimal (gridCol rows cols) p) : rows ≤ cols := by
  have hfib := card_fiber_le_card_col h (0 : Fin cols)
  rw [Fintype.card_fin] at hfib
  refine le_trans ?_ hfib
  have hinj : (Finset.univ : Finset (Fin rows)).card
      ≤ (Finset.univ.filter (fun i : GridIdx rows cols => gridCol rows cols i = 0)).card := by
    refine Finset.card_le_card_of_injOn (fun r => (r, (0 : Fin cols))) (by simp [gridCol]) ?_
    intro a _ b _ hab
    exact congrArg Prod.fst hab
  simpa using hinj

/-- Contrapositive, in the form a state-shape search would use. -/
theorem not_diffusionOptimal_of_cols_lt (rows cols : ℕ) [NeZero cols] (hlt : cols < rows)
    (p : Equiv.Perm (GridIdx rows cols)) : ¬ DiffusionOptimal (gridCol rows cols) p :=
  fun h => absurd (rows_le_cols_of_diffusionOptimal rows cols p h) (by omega)

/-! ### How many offset vectors Definition 5 admits -/

/-- The offset vectors that Definition 5 accepts are exactly the embeddings
`Fin rows ↪ Fin cols`, so there are `cols · (cols - 1) ⋯ (cols - rows + 1)` of them.

The point of computing this is negative and is the point of the file: Definition 5 is a
counting constraint on the offsets and nothing more. When the count is large, the
criterion cannot be what singles out one offset vector, and any explanation that says it
does is wrong about the theory rather than about the cipher. -/
theorem card_diffusionOptimal_offsets (rows cols : ℕ) [NeZero cols] :
    Fintype.card {off : Fin rows → Fin cols //
        DiffusionOptimal (gridCol rows cols) (shiftRowsPerm rows cols off)}
      = cols.descFactorial rows := by
  have e₁ : {off : Fin rows → Fin cols //
      DiffusionOptimal (gridCol rows cols) (shiftRowsPerm rows cols off)}
      ≃ {off : Fin rows → Fin cols // Function.Injective off} :=
    Equiv.subtypeEquivRight (diffusionOptimal_shiftRowsPerm_iff rows cols)
  rw [Fintype.card_congr e₁,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin rows) (Fin cols)),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-! ### Composing two ShiftRows layers

Two rounds apply ShiftRows twice, and the composite is again a ShiftRows with the offsets
added pointwise. Definition 5 is a one-round criterion; this is the smallest handle the
formalisation gives on a two-round one. -/

theorem shiftRowsPerm_trans (rows cols : ℕ) [NeZero cols] (off off' : Fin rows → Fin cols) :
    (shiftRowsPerm rows cols off).trans (shiftRowsPerm rows cols off')
      = shiftRowsPerm rows cols (off + off') := by
  refine Equiv.ext (fun i => ?_)
  simp [Equiv.trans_apply, add_assoc]

/-- `π²` is diffusion-optimal exactly when the doubled offset vector is injective. -/
theorem diffusionOptimal_shiftRowsPerm_trans_self_iff (rows cols : ℕ) [NeZero cols]
    (off : Fin rows → Fin cols) :
    DiffusionOptimal (gridCol rows cols)
        ((shiftRowsPerm rows cols off).trans (shiftRowsPerm rows cols off))
      ↔ Function.Injective (off + off) := by
  rw [shiftRowsPerm_trans]
  exact diffusionOptimal_shiftRowsPerm_iff rows cols (off + off)

/-! ### The specification -/

/-- A wide-trail specification on a rectangular state: a bricklayer S-box layer, ShiftRows
with offsets `off`, and a column mixing of branch number `b`.

The only thing asked of `off` is injectivity, which
`diffusionOptimal_shiftRowsPerm_iff` converts into Definition 5. -/
def gridSpec (rows cols : ℕ) [NeZero cols] (off : Fin rows → Fin cols)
    (sbox mix : (GridIdx rows cols → K) → (GridIdx rows cols → K)) (b : ℕ)
    (hsbox : PreserveSupport sbox) (hoff : Function.Injective off)
    (hmix : IsColBranchBound (gridCol rows cols) mix b) (hnd : NonDegenerate mix) :
    WideTrailSpec (GridIdx rows cols) (Fin cols) K where
  col := gridCol rows cols
  sbox := sbox
  disp := shiftRowsPerm rows cols off
  mix := mix
  branch := b
  sbox_preserves := hsbox
  disp_optimal := (diffusionOptimal_shiftRowsPerm_iff rows cols off).mpr hoff
  mix_branch := hmix
  mix_nondeg := hnd

@[simp] theorem gridSpec_fourRoundBound (rows cols : ℕ) [NeZero cols]
    (off : Fin rows → Fin cols)
    (sbox mix : (GridIdx rows cols → K) → (GridIdx rows cols → K)) (b : ℕ)
    (hsbox : PreserveSupport sbox) (hoff : Function.Injective off)
    (hmix : IsColBranchBound (gridCol rows cols) mix b) (hnd : NonDegenerate mix) :
    (gridSpec rows cols off sbox mix b hsbox hoff hmix hnd).fourRoundBound = b * b := rfl
