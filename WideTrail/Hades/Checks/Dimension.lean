/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Dimension
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Toy checks for the inactive-dimension results

Two small examples over `ZMod 5` show that the hypotheses of `WideTrail.Hades.Dimension` matter
and that its bounds are attained.

* **A collision in the diagonal.** With three coordinates and `d = (2, 1, 1)`, the entries off
  coordinate `0` coincide, `d 1 = d 2` (`collision_not_injOn`). By
  `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff` the stable space of `diag d + J` is then
  nonzero (`collision_inactive_ne_bot`); the difference `e_1 - e_2` stays inactive through every
  number of consecutive partial rounds (`collision_witness_mem`). This is the same mechanism as
  `Poseidon2.Plonky3.Checks.twentyThree_inactive_ne_bot`, where `2^11 = 1` in `ZMod 23` makes
  two entries of the SP1 diagonal coincide. The chain stops after two rounds, earlier than
  `card Idx = 3` (`collision_chain_strict`, `collision_chain_stable`), and the stable space has
  dimension `1` (`collision_finrank_stable`), not `3 - 3 = 0`.
* **A mask of size two.** On four coordinates, the coordinate permutation
  `swap a = (a 2, a 3, a 0, a 1)` with the mask `{0, 1}` loses two dimensions in one round:
  `inactiveSpace swap {0, 1} 1` has dimension `2` and `inactiveSpace swap {0, 1} 2 = ⊥`
  (`swap_finrank_drop`). So `Hades.finrank_inactiveSpace_sub_succ_le` is attained, and the
  formula `card Idx - r` of `Hades.finrank_inactiveSpace_singleton` needs a single S-box
  coordinate. The chain is `⊥` from two rounds on (`swap_inactive_eq_bot`), again earlier than
  `card Idx = 4`.

The axiom footprints of every theorem of `WideTrail.Hades.Dimension` and of this file are pinned
at the end of the file.
-/

set_option autoImplicit false

namespace Hades.DimensionToy

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5

/-! ### A collision in the diagonal -/

/-- The diagonal `(2, 1, 1)`: the two entries off coordinate `0` coincide. -/
def d : Fin 3 → F := ![2, 1, 1]

/-- The toy layer `diag d + J`. -/
abbrev L : Module.End F (Fin 3 → F) := Poseidon2.diagPlusOnes 1 d

theorem collision_not_injOn : ¬ Set.InjOn d {i | i ≠ 0} := by
  intro h
  have h12 : (1 : Fin 3) = 2 := h (by decide) (by decide) (by decide)
  exact absurd h12 (by decide)

/-- **A collision leaves a nonzero stable space**, by the criterion. -/
theorem collision_inactive_ne_bot : inactiveSpace L ({0} : Finset (Fin 3)) 3 ≠ ⊥ := fun h =>
  collision_not_injOn ((inactiveSpace_diagPlusOnes_card_eq_bot_iff one_ne_zero d 0).mp h)

/-- The difference `e_1 - e_2`. -/
def witness : Fin 3 → F := ![0, 1, -1]

theorem L_witness : L witness = witness := by
  funext i
  rw [Poseidon2.diagPlusOnes_apply, Fin.sum_univ_three]
  fin_cases i <;> simp [d, witness]

/-- **`e_1 - e_2` never reaches coordinate `0`**: it is fixed by `diag d + J`. -/
theorem collision_witness_mem (r : ℕ) : witness ∈ inactiveSpace L ({0} : Finset (Fin 3)) r := by
  have hpow : ∀ m : ℕ, (L ^ m) witness = witness := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, L_witness]
  intro j _ i hi
  rw [hpow, Finset.mem_singleton.mp hi]
  rfl

theorem single_zero_not_mem :
    (Pi.single 0 1 : Fin 3 → F) ∉ inactiveSpace L ({0} : Finset (Fin 3)) 1 := by
  rw [mem_inactiveSpace_one]
  intro h
  exact absurd (h 0 (Finset.mem_singleton_self 0)) (by decide)

theorem single_one_mem :
    (Pi.single 1 1 : Fin 3 → F) ∈ inactiveSpace L ({0} : Finset (Fin 3)) 1 := by
  rw [mem_inactiveSpace_one]
  intro i hi
  rw [Finset.mem_singleton.mp hi]
  rfl

theorem single_one_not_mem :
    (Pi.single 1 1 : Fin 3 → F) ∉ inactiveSpace L ({0} : Finset (Fin 3)) 2 := by
  intro h
  have h1 := h 1 (by norm_num) 0 (Finset.mem_singleton_self 0)
  rw [pow_one, Poseidon2.diagPlusOnes_apply, Fin.sum_univ_three] at h1
  exact absurd h1 (by decide)

/-- One round removes a dimension: `e_1` is inactive in one round but not in two. -/
theorem collision_chain_strict :
    inactiveSpace L ({0} : Finset (Fin 3)) 1 ≠ inactiveSpace L ({0} : Finset (Fin 3)) 2 :=
  fun h => single_one_not_mem (h ▸ single_one_mem)

/-- **The chain stops after two rounds**, before `card Idx = 3`. A difference with `a 0 = 0`
and `(L a) 0 = 0` has coordinate sum `0`, so `L a = a`. -/
theorem collision_chain_stable :
    inactiveSpace L ({0} : Finset (Fin 3)) 2 = inactiveSpace L ({0} : Finset (Fin 3)) 3 := by
  refine le_antisymm (fun a ha => ?_) (inactiveSpace_anti L _ (by norm_num))
  have h0 := ha 0 (by norm_num) 0 (Finset.mem_singleton_self 0)
  have h1 := ha 1 (by norm_num) 0 (Finset.mem_singleton_self 0)
  rw [pow_zero, Module.End.one_apply] at h0
  rw [pow_one, Poseidon2.diagPlusOnes_apply, Fin.sum_univ_three] at h1
  intro j hj i hi
  rw [Finset.mem_singleton.mp hi]
  interval_cases j
  · rwa [pow_zero, Module.End.one_apply]
  · rwa [pow_one, Poseidon2.diagPlusOnes_apply, Fin.sum_univ_three]
  · rw [pow_two, Module.End.mul_apply, Poseidon2.diagPlusOnes_apply, Fin.sum_univ_three]
    simp only [Poseidon2.diagPlusOnes_apply, Fin.sum_univ_three, d, one_mul] at h1 ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h1 ⊢
    linear_combination (6 : F) * h1 - (7 : F) * h0

/-- **The stable space has dimension `1`**, not `card Idx - card Idx = 0`. -/
theorem collision_finrank_stable :
    Module.finrank F (inactiveSpace L ({0} : Finset (Fin 3)) 3) = 1 := by
  rw [← collision_chain_stable]
  have hlower := card_sub_le_finrank_inactiveSpace L ({0} : Finset (Fin 3)) 2
  rw [Fintype.card_fin, Finset.card_singleton] at hlower
  have hlt1 : inactiveSpace L ({0} : Finset (Fin 3)) 1 < inactiveSpace L {0} 0 :=
    lt_of_le_of_ne (inactiveSpace_anti L _ (by norm_num)) fun h =>
      single_zero_not_mem (h ▸ (inactiveSpace_zero L _ ▸ Submodule.mem_top))
  have hlt2 : inactiveSpace L ({0} : Finset (Fin 3)) 2 < inactiveSpace L {0} 1 :=
    lt_of_le_of_ne (inactiveSpace_anti L _ (by norm_num)) (Ne.symm collision_chain_strict)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt1
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt2
  have h0 := Submodule.finrank_le (inactiveSpace L ({0} : Finset (Fin 3)) 0)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h0
  omega

/-! ### A mask of size two -/

/-- The coordinate permutation `a ↦ (a 2, a 3, a 0, a 1)`. -/
def swap : Module.End F (Fin 4 → F) := LinearMap.funLeft F F ![2, 3, 0, 1]

/-- The mask `{0, 1}`. -/
def mask : Finset (Fin 4) := {0, 1}

/-- **Two rounds leave no inactive difference.** The first round forces `a 0 = a 1 = 0`, the
second `a 2 = a 3 = 0`. -/
theorem swap_inactive_two : inactiveSpace swap mask 2 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  have h00 := ha 0 (by norm_num) 0 (by decide)
  have h01 := ha 0 (by norm_num) 1 (by decide)
  have h10 := ha 1 (by norm_num) 0 (by decide)
  have h11 := ha 1 (by norm_num) 1 (by decide)
  rw [pow_zero, Module.End.one_apply] at h00 h01
  rw [pow_one] at h10 h11
  funext i
  fin_cases i
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- **One round costs two dimensions**, the bound of `Hades.finrank_inactiveSpace_sub_succ_le`
for a mask of size two. -/
theorem swap_finrank_drop :
    Module.finrank F (inactiveSpace swap mask 1) = 2 ∧
      Module.finrank F (inactiveSpace swap mask 2) = 0 := by
  have hlower := card_sub_le_finrank_inactiveSpace swap mask 1
  have hstep := finrank_inactiveSpace_sub_succ_le swap mask 1
  have hmask : mask.card = 2 := by decide
  rw [Fintype.card_fin, hmask] at hlower
  rw [hmask, swap_inactive_two, finrank_bot] at hstep
  rw [swap_inactive_two, finrank_bot]
  omega

/-- **The chain is `⊥` from two rounds on**, before `card Idx = 4`. -/
theorem swap_inactive_eq_bot {r : ℕ} (hr : 2 ≤ r) : inactiveSpace swap mask r = ⊥ :=
  le_bot_iff.mp (swap_inactive_two ▸ inactiveSpace_anti swap mask hr)

end Hades.DimensionToy

/-- info: 'Hades.inactiveSpace_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_zero

/-- info: 'Hades.mem_inactiveSpace_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.mem_inactiveSpace_one

/-- info: 'Hades.inactiveSpace_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_succ

/-- info: 'Hades.inactiveSpace_eq_of_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_eq_of_succ_eq

/-- info: 'Hades.finrank_inactiveSpace_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.finrank_inactiveSpace_add_le

/-- info: 'Hades.inactiveSpace_eq_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_eq_card

/-- info: 'Hades.inactiveSpace_card_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_card_le_one

/-- info: 'Hades.apply_mem_inactiveSpace_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.apply_mem_inactiveSpace_card

/-- info: 'Hades.le_inactiveSpace_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.le_inactiveSpace_of_invariant

/-- info: 'Hades.mem_inactiveSpace_card_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.mem_inactiveSpace_card_iff

/-- info: 'Hades.no_infinite_inactive_trail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.no_infinite_inactive_trail

/-- info: 'Hades.finrank_inactiveSpace_sub_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.finrank_inactiveSpace_sub_succ_le

/-- info: 'Hades.finrank_inactiveSpace_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.finrank_inactiveSpace_le_add

/-- info: 'Hades.finrank_inactiveSpace_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.finrank_inactiveSpace_singleton

/-- info: 'Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff

/-- info: 'Hades.finrank_inactiveSpace_diagPlusOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.finrank_inactiveSpace_diagPlusOnes

/-- info: 'Hades.DimensionToy.collision_not_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.collision_not_injOn

/-- info: 'Hades.DimensionToy.collision_inactive_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.collision_inactive_ne_bot

/-- info: 'Hades.DimensionToy.L_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.L_witness

/-- info: 'Hades.DimensionToy.collision_witness_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.collision_witness_mem

/-- info: 'Hades.DimensionToy.single_zero_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.single_zero_not_mem

/-- info: 'Hades.DimensionToy.single_one_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.single_one_mem

/-- info: 'Hades.DimensionToy.single_one_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.single_one_not_mem

/-- info: 'Hades.DimensionToy.collision_chain_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.collision_chain_strict

/-- info: 'Hades.DimensionToy.collision_chain_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.collision_chain_stable

/-- info: 'Hades.DimensionToy.collision_finrank_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.collision_finrank_stable

/-- info: 'Hades.DimensionToy.swap_inactive_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.swap_inactive_two

/-- info: 'Hades.DimensionToy.swap_finrank_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.swap_finrank_drop

/-- info: 'Hades.DimensionToy.swap_inactive_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.DimensionToy.swap_inactive_eq_bot
