/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Krylov
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Krylov certificates on a toy internal matrix

The toy internal layer works over `ZMod 13` with four coordinates and the matrix
`diag d + J`, `d = (-2, 1, 2, 4)`. These are the first four entries of the width-sixteen
diagonal `(-2, 1, 2, 4, …, 2^13, 2^15)` of the Plonky3 fork SP1 pins (`p3-koala-bear` and
`p3-baby-bear` at `0.4.3-succinct` and `0.2.3-succinct`), reduced to this field; upstream
Plonky3 has since changed its diagonal. All table checks are plain `decide`.

* `internal_inactive_trivial` has the statement shape of
  `Poseidon2.BN254.internal_inactive_trivial`: no nonzero difference stays off
  coordinate `0` for four rounds. It is proved by the certificate lemma
  `Hades.inactiveSpace_diagPlusOnes_eq_bot` from two literal tables. It fills the same
  `inactiveSpace L.toLinearMap mask w = ⊥` hypothesis that `BN254Middle.lean` fills for
  `Hades.outer_middle_bound`; here it is passed to `Hades.IsTrail.middle_bound`.
* `internal_inactive_three_nontrivial`: three rounds are not enough, so no certificate
  exists for `r = 3`.
* `scaled_inactive_trivial`: the same certificate works after scaling the matrix by `5`.
* `selfAdjoint_needed`: for the non-symmetric shift `x ↦ (0, x 0)`, tables satisfying
  every other hypothesis of `Hades.inactiveSpace_eq_bot_of_krylov` exist, yet the
  inactive space is nonzero. Self-adjointness cannot be dropped.
* `singular_example`: with `1 + ∑ i, (d i)⁻¹ = 0` the internal map is not injective.

The axiom footprints of the main results are pinned at the end of the file.
-/

set_option autoImplicit false

namespace Hades.KrylovToy

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

abbrev F := ZMod 13
abbrev State := Fin 4 → F

/-- The diagonal, `(-2, 1, 2, 4)` in `ZMod 13`. -/
def d : State := ![-2, 1, 2, 4]

/-- Explicit inverses of the diagonal entries. -/
def dInv : State := ![6, 1, 7, 10]

theorem d_mul_dInv : ∀ i, d i * dInv i = 1 := by decide

theorem one_add_sum_dInv : 1 + ∑ i, dInv i ≠ 0 := by decide

theorem one_add_sum_inv : 1 + ∑ i, (d i)⁻¹ ≠ 0 := by
  rw [Poseidon2.sum_inv_eq_of_mul_eq_one d_mul_dInv]
  exact one_add_sum_dInv

/-- The toy internal layer `diag d + J` as a linear equivalence. -/
def internal : State ≃ₗ[F] State :=
  Poseidon2.diagPlusOnesEquiv 1 d one_ne_zero (Poseidon2.ne_zero_of_mul_eq_one d_mul_dInv)
    one_add_sum_inv

/-- Rows `e_0, L e_0, L ^ 2 e_0, L ^ 3 e_0` for `L = diag d + J`. -/
def krylov : Fin 4 → State :=
  ![![1, 0, 0, 0], ![12, 1, 1, 1], ![4, 3, 4, 6], ![9, 7, 12, 2]]

/-- A left inverse of the matrix with rows `krylov j`. -/
def krylovInv : Fin 4 → Fin 4 → F :=
  ![![1, 0, 0, 0], ![10, 11, 6, 9], ![3, 6, 10, 6], ![1, 10, 10, 11]]

theorem krylov_zero : ∀ j : Fin 4, (j : ℕ) = 0 → krylov j = Pi.single 0 1 := by decide

theorem krylov_succ : ∀ j k : Fin 4, (k : ℕ) = j + 1 →
    krylov k = fun i => d i * krylov j i + ∑ m, krylov j m := by decide

theorem krylovInv_mul : ∀ i k : Fin 4,
    ∑ j, krylovInv i j * krylov j k = if i = k then 1 else 0 := by decide

/-- **Four internal rounds leave no inactive difference.** The statement has the shape of
`Poseidon2.BN254.internal_inactive_trivial`; the proof is the Krylov certificate. -/
theorem internal_inactive_trivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 4)) 4 = ⊥ :=
  inactiveSpace_diagPlusOnes_eq_bot one_ne_zero d 0 4 krylov krylov_zero krylov_succ
    krylovInv krylovInv_mul

/-- Three rounds are not enough: three conditions on four coordinates leave a nonzero
solution. The window length four cannot be shortened. -/
theorem internal_inactive_three_nontrivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 4)) 3 ≠ ⊥ :=
  Hades.inactiveSpace_ne_bot _ _ 3 (by simp)

/-- The certificate fills the hypothesis `BN254Middle.lean` fills with its own: tiling
`m` internal rounds with windows of four gives one active S-box per window. -/
theorem middle_activity {rounds : Nat → RoundSpec (Fin 4) F} {T : Nat → State} {R : Nat}
    (hT : IsTrail rounds T R) (h0 : T 0 ≠ 0) (start m : Nat) (hend : start + m ≤ R)
    (hlin : ∀ j < m, (rounds (start + j)).lin = internal)
    (hmask : ∀ j < m, (rounds (start + j)).mask = {0}) :
    m / 4 ≤ scheduledWeight rounds T start m :=
  hT.middle_bound h0 internal {0} start m 4 hend hlin hmask internal_inactive_trivial

/-- The layer scaled by `5`, standing in for a Montgomery constant. -/
def scaled : State ≃ₗ[F] State :=
  Poseidon2.diagPlusOnesEquiv 5 d (by decide) (Poseidon2.ne_zero_of_mul_eq_one d_mul_dInv)
    one_add_sum_inv

/-- The scaling is invisible to the inactive space: the same tables certify it. -/
theorem scaled_inactive_trivial :
    Hades.inactiveSpace scaled.toLinearMap ({0} : Finset (Fin 4)) 4 = ⊥ :=
  inactiveSpace_diagPlusOnes_eq_bot (by decide) d 0 4 krylov krylov_zero krylov_succ
    krylovInv krylovInv_mul

/-- The nilpotent shift `x ↦ (0, x 0)`. Its matrix is not symmetric. -/
def shift : Module.End F (Fin 2 → F) where
  toFun x := ![0, x 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' a x := by
    funext i
    fin_cases i <;> simp

def shiftKrylov : Fin 2 → Fin 2 → F := ![![1, 0], ![0, 1]]

def shiftInv : Fin 2 → Fin 2 → F := ![![1, 0], ![0, 1]]

/-- **Self-adjointness cannot be dropped.** For the shift, the tables `shiftKrylov` and
`shiftInv` meet the recurrence and left-inverse hypotheses of
`Hades.inactiveSpace_eq_bot_of_krylov` for `i0 = 0` and `r = 2`, the shift is not
self-adjoint, and the conclusion fails: `e_1` stays off coordinate `0` for two rounds. -/
theorem selfAdjoint_needed :
    (∀ j : Fin 2, (j : ℕ) = 0 → shiftKrylov j = Pi.single 0 1) ∧
    (∀ j k : Fin 2, (k : ℕ) = j + 1 → shiftKrylov k = shift (shiftKrylov j)) ∧
    (∀ i k : Fin 2, ∑ j, shiftInv i j * shiftKrylov j k = if i = k then 1 else 0) ∧
    ¬ (∀ a b : Fin 2 → F, shift a ⬝ᵥ b = a ⬝ᵥ shift b) ∧
    Hades.inactiveSpace shift ({0} : Finset (Fin 2)) 2 ≠ ⊥ := by
  refine ⟨by decide, by decide, by decide, fun h => ?_, fun hbot => ?_⟩
  · have h01 := h (Pi.single 0 1) (Pi.single 1 1)
    revert h01
    decide
  · have hmem : (Pi.single 1 1 : Fin 2 → F) ∈ Hades.inactiveSpace shift {0} 2 := by
      intro j hj i hi
      rw [Finset.mem_singleton.mp hi]
      interval_cases j
      · simp
      · simp [shift]
    rw [hbot, Submodule.mem_bot] at hmem
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrFun hmem 1)

/-- With `d = (1, 6)` in `ZMod 13`, `1 + 1⁻¹ + 6⁻¹ = 1 + 1 + 11 = 0`, and the layer
`diag d + J` is singular. -/
theorem singular_example : ¬ Function.Injective (Poseidon2.diagPlusOnes (1 : F) ![1, 6]) := by
  have he : ∀ i, (![1, 6] : Fin 2 → F) i * (![1, 11] : Fin 2 → F) i = 1 := by decide
  apply Poseidon2.diagPlusOnes_not_injective (Poseidon2.ne_zero_of_mul_eq_one he)
  rw [Poseidon2.sum_inv_eq_of_mul_eq_one he]
  decide

end Hades.KrylovToy

/-- info: 'Poseidon2.diagPlusOnes_eq_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnes_eq_mulVec

/-- info: 'Poseidon2.diagPlusOnes_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnes_dotProduct

/-- info: 'Poseidon2.diagPlusOnesEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnesEquiv

/-- info: 'Poseidon2.diagPlusOnes_injective_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnes_injective_iff

/-- info: 'Hades.inactiveSpace_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_smul

/-- info: 'Hades.pow_apply_eq_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.pow_apply_eq_dotProduct

/-- info: 'Hades.inactiveSpace_eq_bot_of_krylov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_eq_bot_of_krylov

/-- info: 'Hades.inactiveSpace_diagPlusOnes_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_diagPlusOnes_eq_bot

/-- info: 'Hades.KrylovToy.internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.KrylovToy.internal_inactive_trivial

/-- info: 'Hades.KrylovToy.middle_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.KrylovToy.middle_activity

/-- info: 'Hades.KrylovToy.scaled_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.KrylovToy.scaled_inactive_trivial

/-- info: 'Hades.KrylovToy.selfAdjoint_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.KrylovToy.selfAdjoint_needed

/-- info: 'Hades.KrylovToy.singular_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.KrylovToy.singular_example
