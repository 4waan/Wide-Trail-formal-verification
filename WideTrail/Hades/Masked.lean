/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Differential.Bricklayer

/-!
# Masked S-box layers and charged activity

An active identity coordinate contributes no S-box application. `sboxWeight` counts
only the intersection of the input support with the round's mask. A full mask
recovers the propagation layer's `weight`.
-/

set_option autoImplicit false

namespace Hades

variable {Idx K : Type*} [DecidableEq Idx]

/-- Apply the coordinate S-box exactly at the positions selected by `mask`. -/
def maskedBricklayer (mask : Finset Idx) (s : Idx → K → K) : (Idx → K) → (Idx → K) :=
  bricklayer (fun i => if i ∈ mask then s i else id)

@[simp] theorem maskedBricklayer_apply (mask : Finset Idx) (s : Idx → K → K)
    (x : Idx → K) (i : Idx) :
    maskedBricklayer mask s x i = if i ∈ mask then s i (x i) else x i := by
  by_cases hi : i ∈ mask <;> simp [maskedBricklayer, bricklayer, hi]

/-- Coordinate equivalences give an executable inverse for the masked layer. -/
def maskedEquiv (mask : Finset Idx) (s : Idx → K ≃ K) : (Idx → K) ≃ (Idx → K) where
  toFun := maskedBricklayer mask (fun i => s i)
  invFun := maskedBricklayer mask (fun i => (s i).symm)
  left_inv x := by
    funext i
    by_cases hi : i ∈ mask <;> simp [hi]
  right_inv x := by
    funext i
    by_cases hi : i ∈ mask <;> simp [hi]

@[simp] theorem maskedEquiv_apply (mask : Finset Idx) (s : Idx → K ≃ K) (x : Idx → K) :
    maskedEquiv mask s x = maskedBricklayer mask (fun i => s i) x := rfl

section Activity

variable [Fintype Idx] [Zero K] [DecidableEq K]

/-- The S-box applications whose input differences are nonzero. -/
def activeSboxes (mask : Finset Idx) (a : Idx → K) : Finset Idx :=
  mask ∩ activePattern a

/-- Charged activity, excluding identity coordinates. -/
def sboxWeight (mask : Finset Idx) (a : Idx → K) : Nat :=
  (activeSboxes mask a).card

@[simp] theorem sboxWeight_full (a : Idx → K) :
    sboxWeight Finset.univ a = weight a := by simp [sboxWeight, activeSboxes, weight]

@[simp] theorem sboxWeight_empty (a : Idx → K) : sboxWeight ∅ a = 0 := by
  simp [sboxWeight, activeSboxes]

@[simp] theorem sboxWeight_singleton (i : Idx) (a : Idx → K) :
    sboxWeight {i} a = if a i = 0 then 0 else 1 := by
  by_cases hi : a i = 0 <;> simp [sboxWeight, activeSboxes, activePattern, hi]

theorem sboxWeight_le_weight (mask : Finset Idx) (a : Idx → K) :
    sboxWeight mask a ≤ weight a :=
  Finset.card_le_card Finset.inter_subset_right

theorem sboxWeight_le_mask (mask : Finset Idx) (a : Idx → K) :
    sboxWeight mask a ≤ mask.card :=
  Finset.card_le_card Finset.inter_subset_left

omit [DecidableEq Idx] in
/-- A nonzero pattern has at least one active coordinate. -/
theorem one_le_weight {a : Idx → K} (ha : a ≠ 0) : 1 ≤ weight a := by
  change 0 < (activePattern a).card
  rw [Finset.card_pos]
  exact Finset.nonempty_iff_ne_empty.mpr (fun h => ha (activePattern_eq_empty.mp h))

end Activity

section Differences

variable [Fintype Idx] [AddCommGroup K] [DecidableEq K]

/-- Injective coordinate S-boxes preserve the support of an actual difference.
This concerns a pair of inputs, not a fictitious function on differences. -/
theorem masked_support (mask : Finset Idx) (s : Idx → K ≃ K) (x y : Idx → K) :
    activePattern (maskedEquiv mask s x - maskedEquiv mask s y) = activePattern (x - y) := by
  ext i
  simp only [mem_activePattern, Pi.sub_apply, sub_ne_zero, maskedEquiv_apply,
    maskedBricklayer_apply]
  by_cases hi : i ∈ mask <;> simp [hi]

omit [Fintype Idx] [DecidableEq K] in
/-- Outside the mask, even the value of the difference is unchanged. -/
theorem masked_difference_of_not_mem (mask : Finset Idx) (s : Idx → K ≃ K)
    (x y : Idx → K) {i : Idx} (hi : i ∉ mask) :
    (maskedEquiv mask s x - maskedEquiv mask s y) i = (x - y) i := by simp [hi]

end Differences

end Hades
