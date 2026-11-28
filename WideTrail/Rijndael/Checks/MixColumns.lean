/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Rijndael.MixColumns

/-!
# Checks for Rijndael `MixColumns` and the Rijndael-192/256 activity bounds

Controls for `Rijndael/MixColumns.lean`:

* `mixColumns_appendixB`: on a `4 × 8` state whose columns `0-3` are the state after
  `ShiftRows` in round 1 of FIPS 197-upd1 Appendix B (pdf p. 42) and whose columns `4-7` are
  the same for round 2, `mixColumns 8` gives the two states listed there after `MixColumns`,
  column by column. The kernel evaluates all `32` bytes. The same input under the transpose of
  the matrix, and under `corruptMatrix` below, does not give that output
  (`mixColumns_transpose_appendixB_ne`, `corrupt_appendixB_ne`), so the check fixes the
  orientation of the matrix and the column indexing at width `8`.
* `corruptMatrix` is `aesMatrix` with the entry in row `0`, column `3` changed from `01` to `00`.
  It is invertible (`corruptMatrix_mul_inv`, `corruptInv_mul_corruptMatrix`, both checked by
  the kernel), so its column-wise map is non-degenerate (`corruptMix_nondegenerate`), but it
  sends one active byte to three. So on `GridIdx 4 8` it fails the branch hypothesis
  `IsColBranchBound (gridCol 4 8) · 5` of `rijndaelSpec` (`corruptMix_not_isColBranchBound`),
  its whole-state layer with the Rijndael-256 ShiftRows fails `isBranchBound id · 5`
  (`corruptLin_not_isBranchBound`), and the matrix is not MDS (`corruptMatrix_not_isMDS`).
* `mixColumns_not_isColBranchBound_six`, `rijndael256_lin_not_isBranchBound_six`: the real
  `MixColumns` sends one active byte to four, so the lower bound `5` on the branch numbers
  cannot be raised to `6`.
* `zero_isTrail`, `fourteen_round_needs_h0`: the zero sequence is a trail of
  `rijndael256LinSpec` with no active S-box, so the hypothesis `T 0 ≠ 0` of
  `rijndael256_fourteen_round_concrete` is needed.

## What is not claimed

These are checks of hypotheses and of single values. They do not show that any activity bound
of `Rijndael/MixColumns.lean` is attained, and they do not evaluate the cipher. The Appendix B
states are AES-128 states (`Nb = 4`) placed side by side in a `4 × 8` state; they test
`MixColumns` only, not Rijndael-256 encryption.
-/

set_option autoImplicit false

namespace Rijndael.Checks

open scoped Matrix

/-! ### FIPS 197-upd1 Appendix B, round 1 and round 2 -/

/-- Columns `0-3`: the state after `ShiftRows` in round 1 of FIPS 197-upd1 Appendix B.
Columns `4-7`: the same in round 2. Entry `c` is column `c`, listed from row `0` to row `3`. -/
def appendixBShiftRows : Fin 8 → Fin 4 → GF256 :=
  ![![⟨0xd4#8⟩, ⟨0xbf#8⟩, ⟨0x5d#8⟩, ⟨0x30#8⟩],
    ![⟨0xe0#8⟩, ⟨0xb4#8⟩, ⟨0x52#8⟩, ⟨0xae#8⟩],
    ![⟨0xb8#8⟩, ⟨0x41#8⟩, ⟨0x11#8⟩, ⟨0xf1#8⟩],
    ![⟨0x1e#8⟩, ⟨0x27#8⟩, ⟨0x98#8⟩, ⟨0xe5#8⟩],
    ![⟨0x49#8⟩, ⟨0xdb#8⟩, ⟨0x87#8⟩, ⟨0x3b#8⟩],
    ![⟨0x45#8⟩, ⟨0x39#8⟩, ⟨0x53#8⟩, ⟨0x89#8⟩],
    ![⟨0x7f#8⟩, ⟨0x02#8⟩, ⟨0xd2#8⟩, ⟨0xf1#8⟩],
    ![⟨0x77#8⟩, ⟨0xde#8⟩, ⟨0x96#8⟩, ⟨0x1a#8⟩]]

/-- Columns `0-3`: the state after `MixColumns` in round 1 of FIPS 197-upd1 Appendix B.
Columns `4-7`: the same in round 2. -/
def appendixBMixColumns : Fin 8 → Fin 4 → GF256 :=
  ![![⟨0x04#8⟩, ⟨0x66#8⟩, ⟨0x81#8⟩, ⟨0xe5#8⟩],
    ![⟨0xe0#8⟩, ⟨0xcb#8⟩, ⟨0x19#8⟩, ⟨0x9a#8⟩],
    ![⟨0x48#8⟩, ⟨0xf8#8⟩, ⟨0xd3#8⟩, ⟨0x7a#8⟩],
    ![⟨0x28#8⟩, ⟨0x06#8⟩, ⟨0x26#8⟩, ⟨0x4c#8⟩],
    ![⟨0x58#8⟩, ⟨0x4d#8⟩, ⟨0xca#8⟩, ⟨0xf1#8⟩],
    ![⟨0x1b#8⟩, ⟨0x4b#8⟩, ⟨0x5a#8⟩, ⟨0xac#8⟩],
    ![⟨0xdb#8⟩, ⟨0xe7#8⟩, ⟨0xca#8⟩, ⟨0xa8#8⟩],
    ![⟨0x1b#8⟩, ⟨0x6b#8⟩, ⟨0xb0#8⟩, ⟨0xe5#8⟩]]

/-- The `4 × 8` input state: byte `(r, c)` is row `r` of column `c` of `appendixBShiftRows`. -/
def katIn : GridIdx 4 8 → GF256 := fun i => appendixBShiftRows i.2 i.1

/-- The `4 × 8` expected output. -/
def katOut : GridIdx 4 8 → GF256 := fun i => appendixBMixColumns i.2 i.1

/-- **`MixColumns` at width `8` reproduces the `MixColumns` steps of rounds 1 and 2 of FIPS 197
Appendix B**, in every column. -/
theorem mixColumns_appendixB : mixColumns 8 katIn = katOut := by decide +kernel

/-- The transpose of the matrix does not reproduce them. -/
theorem mixColumns_transpose_appendixB_ne : mixColumnsWith aesMatrixᵀ 8 katIn ≠ katOut := by
  decide +kernel

/-! ### A mixing layer below branch number `5` -/

/-- `aesMatrix` with the entry in row `0`, column `3` changed from `01` to `00`. -/
def corruptMatrix : Matrix (Fin 4) (Fin 4) GF256 :=
  !![⟨2#8⟩, ⟨3#8⟩, ⟨1#8⟩, ⟨0#8⟩;
     ⟨1#8⟩, ⟨2#8⟩, ⟨3#8⟩, ⟨1#8⟩;
     ⟨1#8⟩, ⟨1#8⟩, ⟨2#8⟩, ⟨3#8⟩;
     ⟨3#8⟩, ⟨1#8⟩, ⟨1#8⟩, ⟨2#8⟩]

/-- The inverse of `corruptMatrix`, computed outside Lean and checked below. -/
def corruptInv : Matrix (Fin 4) (Fin 4) GF256 :=
  !![⟨0xa5#8⟩, ⟨0x53#8⟩, ⟨0xf7#8⟩, ⟨0xa5#8⟩;
     ⟨0x7a#8⟩, ⟨0x7a#8⟩, ⟨0x8c#8⟩, ⟨0xf7#8⟩;
     ⟨0xde#8⟩, ⟨0x28#8⟩, ⟨0x7a#8⟩, ⟨0x53#8⟩;
     ⟨0x28#8⟩, ⟨0xde#8⟩, ⟨0x7a#8⟩, ⟨0xa5#8⟩]

theorem corruptMatrix_mul_inv : corruptMatrix * corruptInv = 1 := by decide +kernel

theorem corruptInv_mul_corruptMatrix : corruptInv * corruptMatrix = 1 := by decide +kernel

/-- `corruptMatrix` applied to each column of a `4 × 8` state. -/
def corruptMix : (GridIdx 4 8 → GF256) → (GridIdx 4 8 → GF256) := mixColumnsWith corruptMatrix 8

/-- The corrupted matrix does not reproduce Appendix B either. -/
theorem corrupt_appendixB_ne : corruptMix katIn ≠ katOut := by decide +kernel

/-- **The corrupted layer is non-degenerate**: `corruptMatrix` is invertible, so each column of
a state sent to zero is zero. Only the branch hypothesis fails below. -/
theorem corruptMix_nondegenerate : NonDegenerate corruptMix := by
  intro a ha
  funext ⟨r, c⟩
  have hcol : corruptMatrix.mulVec (fun r' => a (r', c)) = 0 := by
    rw [← mixColumnsWith_column corruptMatrix 8 a c]
    funext r'
    exact congrFun ha (r', c)
  have h := congrArg corruptInv.mulVec hcol
  rw [Matrix.mulVec_mulVec, corruptInv_mul_corruptMatrix, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  exact congrFun h r

/-- The state with one active byte, `1` at row `3` of column `0`. -/
def e30 : GridIdx 4 8 → GF256 := fun i => if i = (3, 0) then ⟨1#8⟩ else 0

theorem e30_ne_zero : e30 ≠ 0 := fun h => by
  have h0 := congrFun h (3, 0)
  revert h0
  decide +kernel

theorem weight_e30 : weight e30 = 1 := by decide +kernel

/-- Column `3` of `corruptMatrix` is `(00, 01, 03, 02)`: one active byte becomes three. -/
theorem weight_corruptMix_e30 : weight (corruptMix e30) = 3 := by decide +kernel

/-- After the Rijndael-256 `ShiftRows` the active byte is still alone in its column, which the
corrupted matrix again sends to three. -/
theorem weight_corruptLin_e30 :
    weight ((corruptMix ∘ transpose (shiftRowsPerm 4 8 shiftOff256)) e30) = 3 := by
  decide +kernel

/-- **`corruptMix` fails the branch hypothesis of `rijndaelSpec`** on `GridIdx 4 8`: one active
byte becomes three, `1 + 3 < 5`. -/
theorem corruptMix_not_isColBranchBound : ¬ IsColBranchBound (gridCol 4 8) corruptMix 5 :=
  fun h => by
    have := branch_le_weight_add h e30_ne_zero
    rw [weight_e30, weight_corruptMix_e30] at this
    omega

/-- **The whole-state layer `corruptMix ∘ ShiftRows` fails `isBranchBound id · 5`.** -/
theorem corruptLin_not_isBranchBound :
    ¬ isBranchBound id (corruptMix ∘ transpose (shiftRowsPerm 4 8 shiftOff256)) 5 := fun h => by
  have := h e30 e30_ne_zero
  rw [colWeight_id, colWeight_id, weight_e30, weight_corruptLin_e30] at this
  omega

/-- `corruptMatrix` is not MDS: for an MDS matrix the column-wise map would satisfy the branch
hypothesis (`mixColumnsWith_isColBranchBound`). -/
theorem corruptMatrix_not_isMDS : ¬ IsMDS corruptMatrix := fun h =>
  corruptMix_not_isColBranchBound (mixColumnsWith_isColBranchBound h 8)

/-! ### The branch number `5` cannot be raised -/

theorem weight_mixColumns_e30 : weight (mixColumns 8 e30) = 4 := by decide +kernel

theorem weight_rijndael256Lin_e30 : weight (rijndael256LinSpec.lin e30) = 4 := by
  rw [rijndael256LinSpec_lin]
  decide +kernel

/-- `6` is not a branch-number lower bound of `MixColumns` on its columns: `1 + 4 < 6`. -/
theorem mixColumns_not_isColBranchBound_six :
    ¬ IsColBranchBound (gridCol 4 8) (mixColumns 8) 6 := fun h => by
  have := branch_le_weight_add h e30_ne_zero
  rw [weight_e30, weight_mixColumns_e30] at this
  omega

/-- `6` is not a branch-number lower bound of the whole-state layer of Rijndael-256. -/
theorem rijndael256_lin_not_isBranchBound_six : ¬ isBranchBound id rijndael256LinSpec.lin 6 :=
  fun h => by
    have := h e30 e30_ne_zero
    rw [colWeight_id, colWeight_id, weight_e30, weight_rijndael256Lin_e30] at this
    omega

/-! ### The hypothesis `T 0 ≠ 0` is needed -/

theorem rijndael256Lin_zero : rijndael256LinSpec.lin 0 = 0 := by
  rw [rijndael256LinSpec_lin]
  decide +kernel

/-- The zero sequence is a trail of `rijndael256LinSpec`. -/
theorem zero_isTrail (r : ℕ) :
    rijndael256LinSpec.IsTrail (fun _ => (0 : GridIdx 4 8 → GF256)) r :=
  fun _ _ => ⟨0, rfl, rijndael256Lin_zero.symm⟩

theorem patternWeight_zero (r : ℕ) :
    patternWeight (fun _ => (0 : GridIdx 4 8 → GF256)) r = 0 := by
  have hw : weight (0 : GridIdx 4 8 → GF256) = 0 := by
    rw [weight, activePattern_eq_empty.mpr rfl, Finset.card_empty]
  simp only [patternWeight, hw, Finset.sum_const_zero]

/-- **The hypothesis `T 0 ≠ 0` of `rijndael256_fourteen_round_concrete` is needed**: the zero
trail has no active S-box. -/
theorem fourteen_round_needs_h0 :
    ¬ ∀ T : ℕ → GridIdx 4 8 → GF256, rijndael256LinSpec.IsTrail T 14 → 80 ≤ patternWeight T 14 :=
  fun h => by
    have := h _ (zero_isTrail 14)
    rw [patternWeight_zero] at this
    omega

end Rijndael.Checks
