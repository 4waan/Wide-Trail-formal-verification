/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Masked
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Executable scheduled rounds

Every round uses pre-addition: `lin (maskedSbox (x + constant))`. Round values
are fixed parameters. The activity results concern actual pairs of executions
and do not assume a distribution on keys or public constants.
-/

set_option autoImplicit false

namespace Hades

variable {Idx K : Type*} [DecidableEq Idx] [Field K]

/-- One round, with an executable inverse for both nonlinear and linear layers. -/
structure RoundSpec (Idx K : Type*) [Field K] where
  mask : Finset Idx
  sbox : Idx → K ≃ K
  lin : (Idx → K) ≃ₗ[K] (Idx → K)
  constant : Idx → K

/-- One pre-addition round. -/
def RoundSpec.apply (R : RoundSpec Idx K) (x : Idx → K) : Idx → K :=
  R.lin (maskedEquiv R.mask R.sbox (x + R.constant))

/-- The inverse is explicit, so toy executions remain kernel-computable. -/
def RoundSpec.equiv (R : RoundSpec Idx K) : (Idx → K) ≃ (Idx → K) where
  toFun := R.apply
  invFun y := (maskedEquiv R.mask R.sbox).symm (R.lin.symm y) - R.constant
  left_inv x := by
    simp only [RoundSpec.apply, LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply,
      add_sub_cancel_right]
  right_inv y := by simp [RoundSpec.apply]

theorem RoundSpec.injective (R : RoundSpec Idx K) : Function.Injective R.apply :=
  R.equiv.injective

/-- Execute the first `n` rounds. A schedule is a total function; the theorem
specifies the finite prefix it consumes. -/
def execute (rounds : Nat → RoundSpec Idx K) (x : Idx → K) : Nat → (Idx → K)
  | 0 => x
  | n + 1 => (rounds n).apply (execute rounds x n)

@[simp] theorem execute_zero (rounds : Nat → RoundSpec Idx K) (x : Idx → K) :
    execute rounds x 0 = x := rfl

@[simp] theorem execute_succ (rounds : Nat → RoundSpec Idx K) (x : Idx → K) (n : Nat) :
    execute rounds x (n + 1) = (rounds n).apply (execute rounds x n) := rfl

theorem execute_injective (rounds : Nat → RoundSpec Idx K) (n : Nat) :
    Function.Injective (fun x => execute rounds x n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih => exact (rounds n).injective.comp ih

/-- A finite execution is itself an equivalence, not merely an injective map. -/
def executeEquiv (rounds : Nat → RoundSpec Idx K) : Nat → (Idx → K) ≃ (Idx → K)
  | 0 => Equiv.refl _
  | n + 1 => (executeEquiv rounds n).trans (rounds n).equiv

@[simp] theorem executeEquiv_apply (rounds : Nat → RoundSpec Idx K) (n : Nat)
    (x : Idx → K) : executeEquiv rounds n x = execute rounds x n := by
  induction n with
  | zero => rfl
  | succ n ih => change (rounds n).apply (executeEquiv rounds n x) = _; rw [ih]; rfl

theorem execute_bijective (rounds : Nat → RoundSpec Idx K) (n : Nat) :
    Function.Bijective (fun x => execute rounds x n) := by
  have heq : (fun x => execute rounds x n) = (executeEquiv rounds n : (Idx → K) → (Idx → K)) :=
    funext (fun x => (executeEquiv_apply rounds n x).symm)
  rw [heq]
  exact (executeEquiv rounds n).bijective

/-- The round-input difference of two actual executions. Adding the same round
value to both inputs does not change this difference. -/
def differenceTrace (rounds : Nat → RoundSpec Idx K) (x y : Idx → K) (n : Nat) : Idx → K :=
  execute rounds x n - execute rounds y n

theorem differenceTrace_ne_zero (rounds : Nat → RoundSpec Idx K)
    {x y : Idx → K} (hxy : x ≠ y) (n : Nat) : differenceTrace rounds x y n ≠ 0 := by
  intro h
  exact hxy (execute_injective rounds n (sub_eq_zero.mp h))

/-- The actual output difference of the masked nonlinear layer, before mixing. -/
def nonlinearDifference (rounds : Nat → RoundSpec Idx K) (x y : Idx → K)
    (n : Nat) : Idx → K :=
  maskedEquiv (rounds n).mask (rounds n).sbox (execute rounds x n + (rounds n).constant)
    - maskedEquiv (rounds n).mask (rounds n).sbox
      (execute rounds y n + (rounds n).constant)

theorem differenceTrace_succ (rounds : Nat → RoundSpec Idx K) (x y : Idx → K) (n : Nat) :
    differenceTrace rounds x y (n + 1) = (rounds n).lin (nonlinearDifference rounds x y n) := by
  simp only [differenceTrace, execute_succ, RoundSpec.apply, nonlinearDifference, map_sub]

variable [Fintype Idx] [DecidableEq K]

theorem nonlinearDifference_support (rounds : Nat → RoundSpec Idx K)
    (x y : Idx → K) (n : Nat) :
    activePattern (nonlinearDifference rounds x y n) =
      activePattern (differenceTrace rounds x y n) := by
  unfold nonlinearDifference
  rw [masked_support]
  congr 1
  exact add_sub_add_right_eq_sub _ _ _

omit [Fintype Idx] [DecidableEq K] in
theorem nonlinearDifference_outside (rounds : Nat → RoundSpec Idx K)
    (x y : Idx → K) (n : Nat) {i : Idx} (hi : i ∉ (rounds n).mask) :
    nonlinearDifference rounds x y n i = differenceTrace rounds x y n i := by
  unfold nonlinearDifference
  rw [masked_difference_of_not_mem _ _ _ _ hi]
  simp [differenceTrace]

/-- Charge only S-box positions with nonzero input differences. -/
def scheduledWeight (rounds : Nat → RoundSpec Idx K) (T : Nat → (Idx → K))
    (start length : Nat) : Nat :=
  ∑ j ∈ Finset.range length, sboxWeight (rounds (start + j)).mask (T (start + j))

@[simp] theorem scheduledWeight_zero (rounds : Nat → RoundSpec Idx K)
    (T : Nat → (Idx → K)) (start : Nat) : scheduledWeight rounds T start 0 = 0 := by
  simp [scheduledWeight]

theorem scheduledWeight_add (rounds : Nat → RoundSpec Idx K)
    (T : Nat → (Idx → K)) (start a b : Nat) :
    scheduledWeight rounds T start (a + b) = scheduledWeight rounds T start a
      + scheduledWeight rounds T (start + a) b := by
  simp [scheduledWeight, Finset.sum_range_add, Nat.add_assoc]

/-- A full/partial/full mask schedule with explicit lengths on both sides. -/
def hadesMask (r m s : Nat) (partialMask : Finset Idx) (n : Nat) : Finset Idx :=
  if n < r then Finset.univ
  else if n < r + m then partialMask
  else if n < r + m + s then Finset.univ else ∅

omit [DecidableEq Idx] in
@[simp] theorem hadesMask_prefix (r m s : Nat) (mask : Finset Idx) {n : Nat} (hn : n < r) :
    hadesMask r m s mask n = Finset.univ := by simp [hadesMask, hn]

omit [DecidableEq Idx] in
@[simp] theorem hadesMask_middle (r m s : Nat) (mask : Finset Idx) {j : Nat} (hj : j < m) :
    hadesMask r m s mask (r + j) = mask := by
  simp [hadesMask, show ¬r + j < r by omega, show r + j < r + m by omega]

omit [DecidableEq Idx] in
@[simp] theorem hadesMask_suffix (r m s : Nat) (mask : Finset Idx) {j : Nat} (hj : j < s) :
    hadesMask r m s mask (r + m + j) = Finset.univ := by
  simp [hadesMask, show ¬r + m + j < r by omega,
    show ¬r + m + j < r + m by omega, show r + m + j < r + m + s by omega]

omit [DecidableEq Idx] in
@[simp] theorem hadesMask_end (r m s : Nat) (mask : Finset Idx) :
    hadesMask r m s mask (r + m + s) = ∅ := by
  simp [hadesMask, show ¬r + m + s < r by omega, show ¬r + m + s < r + m by omega]

/-- Attach a HADES mask schedule to arbitrary round-specific S-boxes, matrices,
and fixed additions. -/
def hadesSchedule (r m s : Nat) (mask : Finset Idx)
    (boxes : Nat → Idx → K ≃ K) (linear : Nat → (Idx → K) ≃ₗ[K] (Idx → K))
    (values : Nat → Idx → K) : Nat → RoundSpec Idx K :=
  fun n => ⟨hadesMask r m s mask n, boxes n, linear n, values n⟩

end Hades
