/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Bounds
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.IntervalCases

/-!
# Concrete HADES executions and missing-assumption counterexamples

The 25-state cipher uses cubing over `ZMod 5`, the matrix `[[1,1],[1,2]]`,
and two full rounds on each side of one partial round. Fixed additions are
`(n, 2*n+1)`. All finite checks use kernel `decide`.
-/

set_option autoImplicit false
set_option maxRecDepth 16000

namespace Hades.Toy

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev State := Fin 2 → ZMod 5

/-- Cubing is its own inverse over this toy field. -/
def cube : ZMod 5 ≃ ZMod 5 where
  toFun x := x ^ 3
  invFun x := x ^ 3
  left_inv := by decide
  right_inv := by decide

/-- Whole-state diffusion with an explicitly executable inverse. -/
def mix : State ≃ₗ[ZMod 5] State where
  toFun x := ![x 0 + x 1, x 0 + 2 * x 1]
  invFun y := ![2 * y 0 - y 1, y 1 - y 0]
  left_inv := by decide
  right_inv := by decide
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

def matrix : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![1, 1; 1, 2]

theorem mix_eq_mulVec (x : State) : mix x = matrix.mulVec x := by
  funext i
  fin_cases i <;> simp [mix, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Check raw injective selections, then transport to canonical minor indexing. -/
theorem matrix_mds : IsMDS matrix := by
  have h : ∀ (k : Nat) (a b : Fin k → Fin 2), Function.Injective a →
      Function.Injective b → (matrix.submatrix a b).det ≠ 0 := by
    intro k a b ha hb
    have hk : k ≤ 2 := by simpa using Fintype.card_le_of_injective a ha
    interval_cases k <;> revert a b ha hb <;> decide
  intro k Row Col hRow hCol
  exact h k _ _
    (fun a b hab => (Row.orderIsoOfFin hRow).injective (Subtype.ext hab))
    (fun a b hab => (Col.orderIsoOfFin hCol).injective (Subtype.ext hab))

theorem mix_branch : isBranchBound id mix 3 :=
  branch_of_mds matrix_mds mix mix_eq_mulVec

/-- An independent finite check of the branch hypothesis. -/
theorem mix_branch_decide : isBranchBound id mix 3 := by
  unfold isBranchBound
  simp only [colWeight_id]
  decide

def values (n : Nat) : State := ![(n : ZMod 5), 2 * (n : ZMod 5) + 1]

def schedule : Nat → RoundSpec (Fin 2) (ZMod 5) :=
  hadesSchedule 2 1 2 {0} (fun _ _ => cube) (fun _ => mix) values

def count (x y : State) : Nat := scheduledWeight schedule (differenceTrace schedule x y) 0 5

/-- The theorem specializes to a bound of six for any distinct inputs. -/
theorem bound {x y : State} (hxy : x ≠ y) : 6 ≤ count x y :=
  hades_bound 2 1 2 3 {0} (fun _ _ => cube) (fun _ => mix) values hxy
    (fun _ _ => mix_branch) (fun _ _ => mix_branch)

set_option maxHeartbeats 4000000 in
-- Scan all 625 pairs and recompute five rounds per pair inside the kernel.
/-- Recompute the bound by scanning all 625 ordered pairs, including the diagonal. -/
theorem bound_decide : ∀ x y : State, x ≠ y → 6 ≤ count x y := by decide

/-- The independently predicted minimum is attained by actual executions. -/
theorem minimum_witness : count ![0, 0] ![1, 0] = 6 := by decide

/-- Charging identity coordinates would give an incorrect S-box count. -/
theorem masked_witness : count ![0, 0] ![0, 1] = 7 := by decide

theorem unmasked_witness :
    (∑ n ∈ Finset.range 5, weight (differenceTrace schedule ![0, 0] ![0, 1] n)) = 8 := by
  decide

/-- Invertibility alone does not supply the MDS branch bound. -/
def weakSchedule : Nat → RoundSpec (Fin 2) (ZMod 5) :=
  hadesSchedule 2 1 2 {0} (fun _ _ => cube) (fun _ => LinearEquiv.refl _ _) values

theorem identity_mix_fails :
    scheduledWeight weakSchedule (differenceTrace weakSchedule ![0, 0] ![0, 1]) 0 5 = 4 := by
  decide

/-- This raw execution deliberately violates `RoundSpec` at the middle step:
the middle map collapses every input to zero. -/
def singularExecute (x : State) : Nat → State
  | 0 => x
  | n + 1 => if n = 2 then 0 else (schedule n).apply (singularExecute x n)

def singularTrace (x y : State) (n : Nat) : State :=
  singularExecute x n - singularExecute y n

theorem singular_middle_collapses : singularTrace ![0, 0] ![1, 0] 3 = 0 := by decide

theorem singular_middle_fails :
    scheduledWeight schedule (singularTrace ![0, 0] ![1, 0]) 0 5 < 6 := by decide

/-- Odd outer blocks and an empty middle use the same theorem and indexing. -/
theorem odd_zero_middle {x y : State} (hxy : x ≠ y) :
    5 ≤ scheduledWeight
      (hadesSchedule 3 0 1 {0} (fun _ _ => cube) (fun _ => mix) values)
      (differenceTrace
        (hadesSchedule 3 0 1 {0} (fun _ _ => cube) (fun _ => mix) values) x y) 0 4 :=
  hades_bound 3 0 1 3 {0} (fun _ _ => cube) (fun _ => mix) values hxy
    (fun _ _ => mix_branch) (fun _ _ => mix_branch)

/-- The final round's mixing can be omitted without changing the count bound. -/
def finalIdentity (n : Nat) : State ≃ₗ[ZMod 5] State :=
  if n = 4 then LinearEquiv.refl _ _ else mix

theorem omitted_final_mix {x y : State} (hxy : x ≠ y) :
    6 ≤ scheduledWeight
      (hadesSchedule 2 1 2 {0} (fun _ _ => cube) finalIdentity values)
      (differenceTrace
        (hadesSchedule 2 1 2 {0} (fun _ _ => cube) finalIdentity values) x y) 0 5 := by
  apply hades_bound 2 1 2 3 {0} (fun _ _ => cube) finalIdentity values hxy
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact mix_branch
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact mix_branch

end Hades.Toy
