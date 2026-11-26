/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Differential.Hull
import Mathlib.Data.ZMod.Basic

/-!
# Checks for the two-round differential bound

`Hull.lean` bounds every two-round differential with a nonzero input difference, averaged over an
additional independent uniform key per round: `diffKeyCount * |K| ^ (B - 1) ≤
u ^ (B - 1) * |Idx → K| ^ 2` (`Scheduled.bricklayer_two_round_bound`). This file tests that
statement on a cipher small enough for the kernel to enumerate, and shows that it is a statement
about the key-averaged model only.

The cipher: the state is `Fin 2 → ZMod 5`, twenty-five states. The S-box is the cube map, a
permutation of `ZMod 5` with differential uniformity exactly `2` (`cube_uniform`,
`cube_not_uniform_one`). The linear layer is `(x₀, x₁) ↦ (x₀ + x₁, x₀ + 2 x₁)`, whose matrix
`[[1, 1], [1, 2]]` has nonzero entries and determinant `1`, so its branch number is `3`
(`lin_isBranchBound`). Rounds are `z ↦ lin (cube (z + k))` on both coordinates. The theorem gives
`diffKeyCount * 5 ^ 2 ≤ 2 ^ 2 * 25 ^ 2`, that is, at most `100` of the `625` key pairs, for every
`a ≠ 0` and every `b` (`toy_bound`).

* **The bound, by enumeration.** `toy_count` is the sum formula of `Scheduled.diffKeyCount_two`
  written with the cube's difference table `ddt`, and `diffKeyCount_eq_toy_count` proves that it
  is the two-round count. The kernel evaluates it for all `24 * 25` pairs `(a, b)` with `a ≠ 0`:
  the maximum is `85` (`toy_count_le`), attained at `a = (0, 1)`, `b = (4, 2)`
  (`toy_count_max`). So the bound `100` holds with room `85 / 100`; it is not attained here.
* **The sum formula against the definition.** For `a = (0, 1)`, `b = (4, 2)` and the input `0`,
  the kernel also enumerates all `625` key pairs and counts `85` of them (`toy_direct`).
* **The model is load-bearing.** With both keys fixed to zero, the same differential is realised
  by `5` of the `25` inputs (`toy_fixed_count`). As a probability that is `5 / 25 = 1 / 5`, above
  the bound `(2 / 5) ^ 2 = 4 / 25` (`toy_fixed_exceeds`). With zero keys this is the cipher with
  fixed round constants `0`, so the theorem is not a statement about a fixed key or about fixed
  round constants.

All finite checks are kernel `decide`; `toy_count_le` uses `decide +kernel`, which leaves the
whole evaluation to the kernel. The parameters were chosen, and the maximum and the witness found,
by an exhaustive search outside Lean; the kernel rechecks every value used.
-/

set_option autoImplicit false
-- The kernel enumerates `625` key pairs in `toy_direct` and unfolds two rounds on each.
set_option maxRecDepth 40000

namespace Scheduled.HullChecks

/-! ### The cipher -/

abbrev F := ZMod 5
abbrev State := Fin 2 → F

/-- The cube map on `ZMod 5`. -/
def cube (x : F) : F := x ^ 3

theorem cube_bijective : Function.Bijective cube := by decide

/-- The cube map has differential uniformity `2`. -/
theorem cube_uniform : IsDiffUniform cube 2 := by decide

/-- And not `1`. -/
theorem cube_not_uniform_one : ¬ IsDiffUniform cube 1 := by decide

/-- The linear layer `(x₀, x₁) ↦ (x₀ + x₁, x₀ + 2 x₁)`, with inverse
`(y₀, y₁) ↦ (2 y₀ - y₁, y₁ - y₀)`. -/
def lin : State ≃+ State where
  toFun x := ![x 0 + x 1, x 0 + 2 * x 1]
  invFun y := ![2 * y 0 - y 1, y 1 - y 0]
  left_inv := by decide
  right_inv := by decide
  map_add' := by decide

/-- Branch number `3`: every nonzero `a` has at least three nonzero coordinates in `a` and
`lin a` together. -/
theorem lin_isBranchBound : isBranchBound id lin 3 := by
  unfold isBranchBound
  decide

/-- Every round has the same linear layer. -/
def lamT : ℕ → State ≃+ State := fun _ => lin

/-- Every round has the cube on both coordinates. -/
def sboxes : ℕ → Fin 2 → F → F := fun _ _ => cube

/-! ### The bound, instantiated -/

theorem card_F : Fintype.card F = 5 := ZMod.card 5

theorem card_State : Fintype.card State = 25 := by
  rw [Fintype.card_fun, card_F, Fintype.card_fin]
  norm_num

/-- **The theorem on the toy.** For `a ≠ 0`, at most `100` of the `625` key pairs realise the
two-round differential `(a, b)`: `diffKeyCount * 5 ^ 2 ≤ 2 ^ 2 * 25 ^ 2`. -/
theorem toy_bound {a : State} (ha : a ≠ 0) (b x : State) :
    diffKeyCount lamT (fun n => bricklayer (sboxes n)) 2 a b x * 5 ^ 2 ≤ 2 ^ 2 * 25 ^ 2 := by
  have h := bricklayer_two_round_bound lamT sboxes (fun _ _ _ => cube_bijective)
    (fun _ _ _ => cube_uniform) lin_isBranchBound ha b x
  rwa [card_F, card_State] at h

/-! ### The bound, by enumeration -/

/-- The difference table of the cube map on `ZMod 5`: `ddt a b` inputs `x` satisfy
`(x + a) ^ 3 - x ^ 3 = b`. -/
def ddt : F → F → ℕ :=
  ![![5, 0, 0, 0, 0], ![0, 2, 2, 0, 1], ![0, 2, 1, 2, 0], ![0, 0, 2, 1, 2], ![0, 1, 0, 2, 2]]

theorem ddt_eq : ∀ a b : F, diffCount cube a b = ddt a b := by decide

/-- The sum formula of `Scheduled.diffKeyCount_two`, with the bricklayer counts written as
products of table entries. -/
def toy_count (a b : State) : ℕ :=
  ∑ c : State, ddt (a 0) (c 0) * ddt (a 1) (c 1) * ddt (lin c 0) (lin.symm b 0)
    * ddt (lin c 1) (lin.symm b 1)

/-- `toy_count` is the two-round count. -/
theorem diffKeyCount_eq_toy_count (a b x : State) :
    diffKeyCount lamT (fun n => bricklayer (sboxes n)) 2 a b x = toy_count a b := by
  rw [diffKeyCount_two, toy_count]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [diffCount_bricklayer, Fin.prod_univ_two, sboxes, lamT, ddt_eq]
  ring

/-- **The maximum is `85`.** For every `a ≠ 0` and every `b`, `toy_count a b ≤ 85`. -/
theorem toy_count_le : ∀ a b : State, a ≠ 0 → toy_count a b ≤ 85 := by decide +kernel

/-- The maximum is attained at `a = (0, 1)`, `b = (4, 2)`. -/
theorem toy_count_max : toy_count ![0, 1] ![4, 2] = 85 := by decide

/-- The exhaustive check in the form of the theorem: `85` key pairs at most, where `100` is
allowed. -/
theorem toy_max_le :
    ∀ a b x : State, a ≠ 0 →
      diffKeyCount lamT (fun n => bricklayer (sboxes n)) 2 a b x ≤ 85 := by
  intro a b x ha
  rw [diffKeyCount_eq_toy_count]
  exact toy_count_le a b ha

/-- The direct count: of the `625` key pairs, `85` take the pair `(0, (0, 1))` to the output
difference `(4, 2)`. -/
theorem toy_direct :
    diffKeyCount lamT (fun n => bricklayer (sboxes n)) 2 ![0, 1] ![4, 2] 0 = 85 := by decide

/-! ### The keys fixed to zero -/

/-- With both keys zero, `5` of the `25` inputs realise the differential `((0, 1), (4, 2))`. -/
theorem toy_fixed_count :
    diffCount (fun x => run lamT (fun n => bricklayer (sboxes n)) 2 0 x) ![0, 1] ![4, 2] = 5 := by
  decide

/-- **The model is load-bearing.** With both keys zero, the count over the inputs, in the
normalisation of `bricklayer_two_round_bound`, exceeds the bound: `5 * 5 ^ 2 > 2 ^ 2 * 25`. -/
theorem toy_fixed_exceeds :
    ¬ diffCount (fun x => run lamT (fun n => bricklayer (sboxes n)) 2 0 x) ![0, 1] ![4, 2]
        * Fintype.card F ^ (3 - 1) ≤ 2 ^ (3 - 1) * Fintype.card State := by
  rw [toy_fixed_count, card_F, card_State]
  decide

end Scheduled.HullChecks

/-! ### Axiom footprints -/

/-- info: 'diffCount_eq_zero_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_eq_zero_of_injective

/-- info: 'sum_diffCount_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_diffCount_col

/-- info: 'Scheduled.diffKeyCount_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_const

/-- info: 'Scheduled.diffKeyCount_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_succ

/-- info: 'Scheduled.diffKeyCount_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_add

/-- info: 'Scheduled.sum_diffKeyCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.sum_diffKeyCount

/-- info: 'Scheduled.sum_diffKeyCount_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.sum_diffKeyCount_col

/-- info: 'Scheduled.diffKeyCount_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_eq_zero

/-- info: 'Scheduled.diffKeyCount_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_window_bound

/-- info: 'Scheduled.diffKeyCount_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_two

/-- info: 'Scheduled.diffKeyCount_two_eq_sum_trailKeyCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_two_eq_sum_trailKeyCount

/-- info: 'Scheduled.sum_prod_le_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.sum_prod_le_of_weight

/-- info: 'Scheduled.diffKeyCount_two_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_two_round_bound

/-- info: 'Scheduled.bricklayer_two_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.bricklayer_two_round_bound

/-- info: 'Scheduled.diffKeyCount_bound_of_two_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.diffKeyCount_bound_of_two_rounds

/-- info: 'Scheduled.HullChecks.lin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.lin_isBranchBound

/-- info: 'Scheduled.HullChecks.cube_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.cube_uniform

/-- info: 'Scheduled.HullChecks.toy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.toy_bound

/-- info: 'Scheduled.HullChecks.toy_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.toy_count_le

/-- info: 'Scheduled.HullChecks.toy_count_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.toy_count_max

/-- info: 'Scheduled.HullChecks.toy_max_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.toy_max_le

/-- info: 'Scheduled.HullChecks.toy_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.toy_direct

/-- info: 'Scheduled.HullChecks.toy_fixed_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.toy_fixed_count

/-- info: 'Scheduled.HullChecks.toy_fixed_exceeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Scheduled.HullChecks.toy_fixed_exceeds
