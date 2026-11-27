/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Character
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.NatAbs

/-!
# The binary case: Walsh values in `ℤ`

For states built from bits the pairing is valued in `ZMod 2` and the character is the sign
`sign₂ t = (-1)ᵗ`, valued in `ℤ`. Then a Walsh value is an integer,

`walsh sign₂ P Q F u v = ∑ₓ (-1) ^ (⟨u, x⟩ + ⟨v, F x⟩)`         (`walsh_sign₂_apply`),

the plan's form of the Walsh sum (in `ZMod 2`, `-t = t`), and every statement about it is exact
integer arithmetic, decidable for a small enough state.

This file proves:

* `sign₂`, and the facts `sign₂ t * sign₂ t = 1` and `(sign₂ t).natAbs = 1`;
* `bitPairing Idx`, the dot product `⟨u, x⟩ = ∑ᵢ uᵢ xᵢ` of `Idx → ZMod 2`, and that it is
  separating for `sign₂` (`bitPairing_separating`). This is the bit pairing for states without
  field structure; a cipher over `GF(2⁸)` may instead use a trace-form pairing (see
  `Character.lean`), and which one a statement uses is part of the statement;
* `natAbs_walsh_le_card`: `|W| ≤ |X|`;
* (W9) Parseval, `sum_walsh_sq_left` and `sum_walsh_sq_right`: the squares of a column of
  Walsh values sum to `|X|²` for every map; the squares of a row sum to `|X| · |Y|` when the map
  is injective. Both need a separating pairing (on the input side for columns, on the output side
  for rows);
* `IsLinearityBound P F c`: every Walsh value of `F` at a nonzero input mask has absolute value at
  most `c`, so every correlation at a nonzero input mask is at most `c / |X|` in absolute value.
  It is decidable;
* `natAbs_walsh_bricklayer_le`: for a bricklayer of S-boxes with linearity bound `c`,
  `|W(u, v)| ≤ c ^ weight u · |K| ^ (|Idx| - weight u)`. An active bundle costs a factor `c`, an
  inactive one at most `|K|`. This is the linear twin of `diffCount_bricklayer_le`.

## What is not claimed

No S-box is shown to satisfy a linearity bound here, and no trail or cipher is considered.
-/

set_option autoImplicit false

namespace Linear

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- The sign character of `ZMod 2`: `t ↦ (-1) ^ t`, valued in `ℤ`. -/
def sign₂ : AddChar (ZMod 2) ℤ where
  toFun t := if t = 0 then 1 else -1
  map_zero_eq_one' := rfl
  map_add_eq_mul' := by decide

theorem sign₂_apply (t : ZMod 2) : sign₂ t = if t = 0 then 1 else -1 := rfl

@[simp] theorem sign₂_zero : sign₂ 0 = 1 := rfl

@[simp] theorem sign₂_one : sign₂ 1 = -1 := rfl

theorem sign₂_mul_self (t : ZMod 2) : sign₂ t * sign₂ t = 1 := by
  revert t
  decide

@[simp] theorem natAbs_sign₂ (t : ZMod 2) : (sign₂ t).natAbs = 1 := by
  revert t
  decide

/-- One bit is separated from itself: `sign₂ (u * x) = -1` for `u = x = 1`. -/
theorem mulPairing_two_separating : (mulPairing (ZMod 2)).Separating sign₂ where
  left := by decide
  right := by decide

/-- The bit pairing of `Idx → ZMod 2`: the dot product `⟨u, x⟩ = ∑ᵢ uᵢ xᵢ`. -/
abbrev bitPairing (Idx : Type*) [Fintype Idx] : Pairing (Idx → ZMod 2) (ZMod 2) :=
  (mulPairing (ZMod 2)).pi

/-- The bit pairing is separating for `sign₂`. -/
theorem bitPairing_separating (Idx : Type*) [Fintype Idx] :
    (bitPairing Idx).Separating sign₂ :=
  mulPairing_two_separating.pi

section Walsh

variable [Fintype X] (P : Pairing X (ZMod 2)) (Q : Pairing Y (ZMod 2))

/-- **The plan's form of the Walsh sum**: `walsh sign₂ P Q F u v = ∑ₓ (-1) ^ (⟨u, x⟩ + ⟨v, F x⟩)`,
with the exponent read as a natural number `0` or `1`. -/
theorem walsh_sign₂_apply (F : X → Y) (u : X) (v : Y) :
    walsh sign₂ P Q F u v = ∑ x, (-1 : ℤ) ^ (P.dot u x + Q.dot v (F x)).val := by
  unfold walsh
  refine Finset.sum_congr rfl fun x _ => ?_
  generalize P.dot u x = a
  generalize Q.dot v (F x) = b
  revert a b
  decide

/-- In the binary case the masks `-u` and `u` coincide in every pairing, so
`W(-u, -v) = W(u, v)`. -/
theorem walsh_neg_neg (F : X → Y) (u : X) (v : Y) :
    walsh sign₂ P Q F (-u) (-v) = walsh sign₂ P Q F u v := by
  unfold walsh
  simp only [map_neg, AddMonoidHom.neg_apply, ZMod.neg_eq_self_mod_two]

/-- A Walsh value is at most `|X|` in absolute value. -/
theorem natAbs_walsh_le_card (F : X → Y) (u : X) (v : Y) :
    (walsh sign₂ P Q F u v).natAbs ≤ Fintype.card X := by
  unfold walsh
  refine (Int.natAbs_sum_le _ _).trans ?_
  simp

variable {P Q}

/-- **(W9) Parseval, columns.** For a pairing separating on the input side and every map `F`,
`∑ᵤ W(u, v)² = |X|²`. -/
theorem sum_walsh_sq_left (hP : P.Separating sign₂) (F : X → Y) (v : Y) :
    ∑ u, walsh sign₂ P Q F u v ^ 2 = (Fintype.card X : ℤ) ^ 2 := by
  have h := sum_walsh_mul_walsh_neg_left (Q := Q) hP F v
  simp_rw [walsh_neg_neg] at h
  simpa [sq] using h

/-- **(W9) Parseval, rows.** For an injective map and a pairing separating on the output side,
`∑ᵥ W(u, v)² = |X| · |Y|`. -/
theorem sum_walsh_sq_right [Fintype Y] (hQ : Q.Separating sign₂) {F : X → Y}
    (hF : Function.Injective F) (u : X) :
    ∑ v, walsh sign₂ P Q F u v ^ 2 = (Fintype.card X : ℤ) * Fintype.card Y := by
  have h := sum_walsh_mul_walsh_neg_right (P := P) hQ hF u
  simp_rw [walsh_neg_neg] at h
  simpa [sq] using h

end Walsh

/-! ### Linearity bounds -/

/-- `c` bounds every Walsh value of `F` at a nonzero input mask: `|W_F(a, b)| ≤ c` for all
`a ≠ 0` and all `b`. Equivalently every correlation of `F` at a nonzero input mask is at most
`c / |X|` in absolute value. -/
def IsLinearityBound [Fintype X] (P : Pairing X (ZMod 2)) (F : X → X) (c : ℕ) : Prop :=
  ∀ a, a ≠ 0 → ∀ b, (walsh sign₂ P P F a b).natAbs ≤ c

/-- A linearity bound is a bounded quantifier over a finite type, so the kernel can settle it
for a concrete S-box. -/
instance decidableIsLinearityBound [Fintype X] [DecidableEq X] (P : Pairing X (ZMod 2))
    (F : X → X) (c : ℕ) : Decidable (IsLinearityBound P F c) :=
  inferInstanceAs (Decidable (∀ a, a ≠ 0 → ∀ b, (walsh sign₂ P P F a b).natAbs ≤ c))

/-- **The active-S-box count is the exponent.** For a bricklayer of S-boxes with linearity bound
`c` and the bundle-sum pairing, `|W(u, v)| ≤ c ^ weight u · |K| ^ (|Idx| - weight u)`: every
active bundle costs a factor of at most `c`, every inactive bundle at most `|K|`. -/
theorem natAbs_walsh_bricklayer_le {Idx K : Type*} [Fintype Idx] [DecidableEq Idx]
    [AddCommGroup K] [Fintype K] [DecidableEq K] {P : Pairing K (ZMod 2)} {s : Idx → K → K}
    {c : ℕ} (hc : ∀ i, IsLinearityBound P (s i) c) (u v : Idx → K) :
    (walsh sign₂ P.pi P.pi (bricklayer s) u v).natAbs
      ≤ c ^ weight u * Fintype.card K ^ (Fintype.card Idx - weight u) := by
  have hprod : (∏ i, walsh sign₂ P P (s i) (u i) (v i)).natAbs
      = ∏ i, (walsh sign₂ P P (s i) (u i) (v i)).natAbs :=
    map_prod Int.natAbsHom _ _
  rw [walsh_bricklayer, hprod, ← Finset.prod_mul_prod_compl (activePattern u)]
  refine Nat.mul_le_mul ?_ ?_
  · calc ∏ i ∈ activePattern u, (walsh sign₂ P P (s i) (u i) (v i)).natAbs
        ≤ ∏ _i ∈ activePattern u, c :=
          Finset.prod_le_prod' (fun i hi => hc i (u i) (mem_activePattern.mp hi) (v i))
      _ = c ^ weight u := by rw [Finset.prod_const, weight]
  · calc ∏ i ∈ (activePattern u)ᶜ, (walsh sign₂ P P (s i) (u i) (v i)).natAbs
        ≤ ∏ _i ∈ (activePattern u)ᶜ, Fintype.card K :=
          Finset.prod_le_prod' (fun i _ => natAbs_walsh_le_card P P (s i) (u i) (v i))
      _ = Fintype.card K ^ (Fintype.card Idx - weight u) := by
          rw [Finset.prod_const, Finset.card_compl, weight, Fintype.card]

end Linear
