/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel

/-!
# Differential counts

Layers 1 and 2 count *active S-boxes*. Differential layer turns that count into a probability. The
first step is to say what a differential probability is, and to say it without measure
theory.

A differential of `F` is a pair `(a, b)` of an input and an output difference, and its
probability is the fraction of inputs realising it:

`DP F a b = |{x : F (x + a) - F x = b}| / |X|`.

Everything below keeps the **numerator**, `diffCount`, and never divides. A statement of
the form `DP ≤ 2⁻ᵈ` becomes `diffCount * 2 ^ d ≤ |X|`, which is exact arithmetic in `ℕ`,
needs no rationals, and stays decidable on a small cipher so the kernel can check it by
enumeration.

Two facts here carry the weight of the whole layer.

* `sum_diffCount`: a row of the difference distribution table sums to `|X|`. This is
  "the probabilities add to one", and it is what makes any single-differential bound a
  bound on one term of a sum.
* `diffCount_comp`: the differential count of `G ∘ H` is the sum, over intermediate
  differences, of the count of inputs taking that particular route. This is an
  **identity**, with no independence assumption anywhere, and it is the precise statement
  of the *hull effect*: a wide-trail theorem controls one summand, while an attacker gets
  the whole sum. Nothing in Layers 1 to 3 closes that gap, and this file is where the gap
  is made visible rather than mentioned.

Key additions and invertible linear layers are invisible to all of this
(`diffCount_addKey`, `diffCount_addEquiv`), which is the differential-probability version
of Propagation layer's remark that keys never appear in a wide-trail statement. There it was a
hypothesis (`PreserveSupport` covers key addition); here it is a computation.
-/

set_option autoImplicit false

variable {X Y Z : Type*} [Fintype X] [AddCommGroup X]
  [AddCommGroup Y] [DecidableEq Y] [AddCommGroup Z] [DecidableEq Z]

/-- The inputs on which `F` carries the input difference `a` to the output difference
`b`. -/
def diffSet (F : X → Y) (a : X) (b : Y) : Finset X :=
  Finset.univ.filter (fun x => F (x + a) - F x = b)

/-- The differential count of `F` at `(a, b)`: the numerator of `DP`, whose denominator is
always `Fintype.card X`. -/
def diffCount (F : X → Y) (a : X) (b : Y) : Nat := (diffSet F a b).card

@[simp] theorem mem_diffSet {F : X → Y} {a : X} {b : Y} {x : X} :
    x ∈ diffSet F a b ↔ F (x + a) - F x = b := by
  simp [diffSet]

theorem diffCount_le_card (F : X → Y) (a : X) (b : Y) :
    diffCount F a b ≤ Fintype.card X :=
  Finset.card_le_univ _

/-- **An inactive bundle is free.** A zero input difference produces a zero output
difference on every input, so its differential probability is `1`, and any other output
difference is impossible. This is the `DP = 1` that lets the product over bundles ignore
the inactive ones. -/
theorem diffCount_zero_left (F : X → Y) (b : Y) :
    diffCount F 0 b = if b = 0 then Fintype.card X else 0 := by
  rw [diffCount, diffSet]
  simp only [add_zero, sub_self]
  split
  · next h =>
      subst h
      simp
  · next h =>
      rw [Finset.filter_eq_empty_iff.mpr (fun x _ => fun hx => h hx.symm), Finset.card_empty]

/-- **A row of the difference distribution table sums to `|X|`.** Every input realises
exactly one output difference, so the differential probabilities out of a fixed `a` add up
to one. No bound on a single differential can therefore be read as a bound on the family. -/
theorem sum_diffCount [Fintype Y] (F : X → Y) (a : X) :
    ∑ b : Y, diffCount F a b = Fintype.card X := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun x => F (x + a) - F x) (s := (Finset.univ : Finset X))
    (t := (Finset.univ : Finset Y)) (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  exact h.symm

/-- **Round keys are invisible.** Adding a key before the map permutes the inputs, and a
count is invariant under permuting what it counts. -/
theorem diffCount_addKey (F : X → Y) (k a : X) (b : Y) :
    diffCount (fun x => F (x + k)) a b = diffCount F a b := by
  refine Finset.card_equiv
    ⟨fun x => x + k, fun x => x - k, fun x => by simp, fun x => by simp⟩ (fun x => ?_)
  simp only [mem_diffSet, Equiv.coe_fn_mk]
  rw [add_right_comm]

/-- **An invertible linear layer only relabels output differences.** `θ` and `π` are
linear, so a round's differential counts are the S-box layer's counts, read at a different
output difference. -/
theorem diffCount_addEquiv (e : Y ≃+ Z) (F : X → Y) (a : X) (b : Z) :
    diffCount (fun x => e (F x)) a b = diffCount F a (e.symm b) := by
  rw [diffCount, diffCount]
  congr 1
  ext x
  simp only [mem_diffSet, ← map_sub e]
  exact ⟨fun h => by rw [← h, e.symm_apply_apply], fun h => by rw [h, e.apply_symm_apply]⟩

/-- `u` bounds every differential count of `F` at a nonzero input difference. For the AES
S-box the sharp value is `u = 4` out of `256` inputs, which is the `2⁻⁶` of the literature;
`u` enters this development as a hypothesis, exactly as `IsColBranchBound` did in Propagation
layer. -/
def IsDiffUniform (F : X → Y) (u : Nat) : Prop := ∀ a, a ≠ 0 → ∀ b, diffCount F a b ≤ u

/-- Differential uniformity is a bounded quantifier over finite types, so the kernel can
settle it for any concrete S-box. Propagation layer made `DiffusionOptimal` decidable for the same
reason: a hypothesis that cannot be refuted on a small cipher is a hypothesis nobody is
testing. -/
instance decidableIsDiffUniform [DecidableEq X] [Fintype Y] (F : X → Y) (u : Nat) :
    Decidable (IsDiffUniform F u) :=
  inferInstanceAs (Decidable (∀ a, a ≠ 0 → ∀ b, diffCount F a b ≤ u))

/-- The inputs that take the route `a → b → c` through `H` and then `G`. -/
def jointCount [Fintype Y] (G : Y → Z) (H : X → Y) (a : X) (b : Y) (c : Z) : Nat :=
  ((diffSet H a b).filter (fun x => H x ∈ diffSet G b c)).card

/-- **The hull identity.** The differential count of a composition is the sum, over
intermediate differences, of the counts along each route. It is an equality, it holds for
arbitrary `G` and `H`, and it assumes nothing about keys or independence.

Read it in the direction that matters for cryptanalysis: a wide-trail theorem bounds one
summand, and what an attacker exploits is the whole sum. That gap is the hull effect, and
it is not closed anywhere in this development. -/
theorem diffCount_comp [Fintype Y] (G : Y → Z) (H : X → Y) (a : X) (c : Z) :
    diffCount (fun x => G (H x)) a c = ∑ b : Y, jointCount G H a b c := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun x => H (x + a) - H x) (s := diffSet (fun x => G (H x)) a c)
    (t := (Finset.univ : Finset Y)) (fun x _ => Finset.mem_univ _)
  rw [diffCount, h]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [jointCount]
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_diffSet]
  constructor
  · rintro ⟨hc, hb⟩
    have hH : H (x + a) = H x + b := by rw [← hb]; abel
    exact ⟨hb, by rw [← hH]; exact hc⟩
  · rintro ⟨hb, hc⟩
    have hH : H (x + a) = H x + b := by rw [← hb]; abel
    exact ⟨by rw [hH]; exact hc, hb⟩
