/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.BlockCirculant
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Adversarial checks for the block-circulant branch bound

Every `blockMix` instance here has four blocks of two positions (`t = 4`, `k = 2`), so the bound of
`BlockCirculant.isBranchBound_blockMix` is `min (4 + 2) (2 * 3) = 6`. The block map is
`N = [[1, 1], [1, 2]]`. Its entries and its determinant `1` are nonzero in `ZMod 5` and in
`ZMod 7`, so `N` has branch number `3` over both; this is decided below rather than
assumed.

* Over `ZMod 5` the hypothesis on `1, …, t + 1` fails only at `5`. There the state whose
  four blocks all equal `(1, 0)` is sent to `0`, so it has weight `4 < 6`. The
  characteristic hypothesis cannot be dropped, and `blockMix N` is not injective, so the
  hypothesis of `blockMixEquiv` cannot be dropped either.
* Over `ZMod 7` all hypotheses hold and the theorem gives `6`. A state of weight exactly
  `6` is exhibited, so the branch number there is exactly `6` and the bound is attained.
  The witness was found by an exhaustive search over all `7 ^ 8` states outside Lean;
  only the witness itself is used here.
* For `t = k = 4` the two terms of the bound are `8` and `10`, so the term `2 (k + 1)`
  from states with zero block sum is not the binding one.

All finite checks are kernel `decide`. The explicit inverse `blockMixInv` is not
evaluated here, because division in `ZMod` does not reduce in the kernel; it is covered
by the general proofs `blockMixInv_blockMix` and `blockMix_blockMixInv`.
-/

set_option autoImplicit false

namespace BlockCirculant.Checks

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `N = [[1, 1], [1, 2]]` over any commutative ring, with its inverse
`[[2, -1], [-1, 1]]`. -/
def mix (K : Type) [CommRing K] : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![x 0 + x 1, x 0 + 2 * x 1]
  invFun y := ![2 * y 0 - y 1, y 1 - y 0]
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

/-! ### Over `ZMod 5`: the characteristic hypothesis cannot be dropped -/

/-- `N` has branch number `3` over `ZMod 5`, by enumeration of all `25` inputs. -/
theorem mix_five_branch : isBranchBound id (mix (ZMod 5)) 3 := by
  unfold isBranchBound
  simp only [colWeight_id]
  decide

/-- The integers `1, …, 4` are nonzero in `ZMod 5`; only `t + 1 = 5` fails. -/
theorem five_char_partial : ∀ n : ℕ, 1 ≤ n → n ≤ 4 → (n : ZMod 5) ≠ 0 := by
  intro n h1 h2
  interval_cases n <;> decide

theorem five_char_fails : ((Fintype.card (Fin 4) + 1 : ℕ) : ZMod 5) = 0 := by decide

/-- Every block equal to `(1, 0)`. -/
def flat : Fin 4 × Fin 2 → ZMod 5 := fun ic => if ic.2 = 0 then 1 else 0

theorem flat_ne_zero : flat ≠ 0 := by decide

/-- The block sum is `(4, 0) = -(1, 0)`, so every block is cancelled and the output is `0`.
In particular `blockMix N` is not injective over `ZMod 5`. -/
theorem blockMix_flat : blockMix (B := Fin 4) (mix (ZMod 5)).toLinearMap flat = 0 := by
  decide

theorem flat_weight :
    weight flat + weight (blockMix (B := Fin 4) (mix (ZMod 5)).toLinearMap flat) = 4 := by
  decide

/-- **The conclusion fails without `t + 1 ≠ 0`.** All other hypotheses of
`isBranchBound_blockMix` hold, and the promised bound `min (4 + 2) (2 * 3) = 6` does not. -/
theorem five_not_branch :
    ¬ isBranchBound id (blockMix (B := Fin 4) (mix (ZMod 5)).toLinearMap)
      (min (Fintype.card (Fin 4) + Fintype.card (Fin 2)) (2 * (Fintype.card (Fin 2) + 1))) := by
  intro h
  have h' := h flat flat_ne_zero
  rw [colWeight_id, colWeight_id, flat_weight] at h'
  simp at h'

/-! ### Over `ZMod 7`: the bound is attained -/

theorem mix_seven_branch : isBranchBound id (mix (ZMod 7)) 3 := by
  unfold isBranchBound
  simp only [colWeight_id]
  decide

theorem seven_char : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card (Fin 4) + 1 → (n : ZMod 7) ≠ 0 := by
  intro n h1 h2
  rw [Fintype.card_fin] at h2
  interval_cases n <;> decide

/-- The theorem applies over `ZMod 7` and gives `6`. -/
theorem seven_branch : isBranchBound id (blockMix (B := Fin 4) (mix (ZMod 7)).toLinearMap) 6 := by
  have h := isBranchBound_blockMix (B := Fin 4) (N := (mix (ZMod 7)).toLinearMap)
    (by simpa using mix_seven_branch) seven_char
  simpa using h

/-- Three zero blocks and a last block `(1, 3)`. The block sum is `(1, 3)`, so the zero
blocks map to `N (1, 3) = (4, 0)` and the last to `N (2, 6) = (1, 0)`. -/
def tight : Fin 4 × Fin 2 → ZMod 7 := fun ic => if ic.1 = 3 then ![1, 3] ic.2 else 0

theorem tight_ne_zero : tight ≠ 0 := by decide

theorem tight_weight :
    weight tight + weight (blockMix (B := Fin 4) (mix (ZMod 7)).toLinearMap tight) = 6 := by
  decide

/-- **The bound is attained.** Over `ZMod 7` the branch number of `blockMix N` is exactly
`6`: `seven_branch` gives `6` and `tight` reaches it. -/
theorem seven_not_seven :
    ¬ isBranchBound id (blockMix (B := Fin 4) (mix (ZMod 7)).toLinearMap) 7 := by
  intro h
  have h' := h tight tight_ne_zero
  rw [colWeight_id, colWeight_id, tight_weight] at h'
  omega

/-! ### The flat layout of `isBranchBound_blockMix_sixteen` -/

/-- Block `1`, position `2` is flat coordinate `4 * 1 + 2 = 6`. -/
example : (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16) (1, 2) = 6 := by decide

/-- Flat coordinate `13` is block `3`, position `1`. -/
example : (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm 13 = (3, 1) := by decide

/-! ### `t = k = 4`: the zero-block-sum term is not binding -/

/-- For four blocks of four the two cases give `t + k = 8` and `2 (k + 1) = 10`, so the
bound `8` comes from states with nonzero block sum. -/
example : 4 + 4 < 2 * (4 + 1) ∧ min (4 + 4) (2 * (4 + 1)) = 8 := by decide

end BlockCirculant.Checks
