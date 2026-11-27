/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.AES

/-!
# Checks for the AES trail and hull bounds

Controls for `Linear/AES.lean`, under the trace pairing `GF256.tracePairing`:

* `sbox_clears_iff`, `not_exists_sbox_clears_four`: a linearity bound `c` of the S-box with
  `c · 2 ^ d ≤ 256` exists exactly when `d ≤ 3`. So the hypothesis `c · 2 ^ d ≤ |K|` of
  `trailCorr_le_of_spec` fails for `d = 4` with every linearity bound of the S-box
  (`32 · 2⁴ = 512 > 256`), and the exponents `75, 165, 225, 240` of the AES trail bounds cannot
  be raised to `100, 220, 300, 320` this way.
* `binMixColumns_not_isColBranchBound`, `binMixColumns_not_isBranchBound`,
  `binMatrix_not_isMDS`: the column-wise layer of the non-MDS matrix `circ(0, 1, 1, 1)` sends
  one active byte to three, so it fails the branch hypothesis `IsColBranchBound (sqCol 4) · 5` of
  `aesSpec` and the hypothesis `isBranchBound id (lamT 0) 5` of `elpCount_two_round_bound`. The
  matrix is symmetric and an involution (`binMatrix_transpose`, `binMatrix_mul_self`), so this
  layer is its own trace adjoint (`binMixColumns_isAdjoint`) and the matrix is the transpose of
  its own inverse (`binMatrix_inv_transpose`). As the `MixColumns` of a cipher, it is therefore
  also the column layer of that cipher's backward mask map and of its forward mask map, so the
  mask specification of that cipher would fail the same hypothesis of `aesSpec`.
* `aesLinT_not_isBranchBound_six`, `aesLin_not_isLinBranchBound_six`,
  `aesMixColumns_not_isLinBranchBound_six`: one active byte is sent to four by the backward map
  `aesLinT`, so the lower bound `5` on the (linear) branch numbers cannot be raised to `6`.
* `maskSpec_lin_ne`: the forward mask map `aesMaskSpec.lin` and the state map `aesLinSpec.lin`
  differ: on one active byte the first column becomes `(0e, 0b, 0d, 09)` against
  `(02, 01, 01, 03)`.
* `natAbs_trailCorr_zero_masks`, `four_round_correlation_needs_h0`: for any finite group of
  states and maps `lamT n` fixing the zero mask, the zero trail has `|trailCorr| = |X| ^ r`. So
  not every four-round trail of AES satisfies the bound of `AES.four_round_correlation`, and its
  hypothesis `T 0 ≠ 0` is needed.
* `elpCount_zero_masks`, `two_round_elp_needs_hu`: `elpCount r 0 0 = |X| ^ r · |X| ^ 2` for every
  map, so not every pair of masks satisfies the bound of `AES.two_round_elp`, and its hypothesis
  `u ≠ 0` is needed.

## What is not claimed

These are checks of hypotheses and of single values. They do not evaluate any correlation of
AES over its `2¹²⁸` states, and they do not show that any trail or hull bound of
`Linear/AES.lean` is attained.
-/

set_option autoImplicit false

namespace Linear.Checks

open GF256 AES
open scoped Matrix

/-! ### The exponent `3` per active S-box -/

/-- **A linearity bound of the S-box clears `2 ^ d` exactly when `d ≤ 3`**: there is a `c` with
`IsLinearityBound tracePairing sbox c` and `c · 2 ^ d ≤ |GF256|` if and only if `d ≤ 3`. The
least linearity bound is `32` (`AES.sbox_isLinearityBound_iff`). -/
theorem sbox_clears_iff (d : ℕ) :
    (∃ c, IsLinearityBound tracePairing sbox c ∧ c * 2 ^ d ≤ Fintype.card GF256) ↔ d ≤ 3 := by
  rw [card_gf256]
  constructor
  · rintro ⟨c, hc, hd⟩
    have h32 := (sbox_isLinearityBound_iff c).mp hc
    by_contra h
    have h4 : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h512 : 32 * 2 ^ 4 ≤ c * 2 ^ d := Nat.mul_le_mul h32 h4
    norm_num at h512
    omega
  · intro hd
    refine ⟨32, sbox_isLinearityBound, ?_⟩
    calc 32 * 2 ^ d ≤ 32 * 2 ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hd)
      _ = 256 := by norm_num

/-- **`d = 4` fails**: no linearity bound `c` of the S-box has `c · 2⁴ ≤ |GF256|`. -/
theorem not_exists_sbox_clears_four :
    ¬ ∃ c, IsLinearityBound tracePairing sbox c ∧ c * 2 ^ 4 ≤ Fintype.card GF256 := fun h =>
  absurd ((sbox_clears_iff 4).mp h) (by decide)

/-! ### A mixing layer below branch number `5` -/

/-- The non-MDS circulant `circ(0, 1, 1, 1)` over `GF(2⁸)`. -/
def binMatrix : Matrix (Fin 4) (Fin 4) GF256 :=
  !![⟨0#8⟩, ⟨1#8⟩, ⟨1#8⟩, ⟨1#8⟩;
     ⟨1#8⟩, ⟨0#8⟩, ⟨1#8⟩, ⟨1#8⟩;
     ⟨1#8⟩, ⟨1#8⟩, ⟨0#8⟩, ⟨1#8⟩;
     ⟨1#8⟩, ⟨1#8⟩, ⟨1#8⟩, ⟨0#8⟩]

/-- `binMatrix` applied column by column. -/
def binMixColumns (a : SquareIdx 4 → GF256) : SquareIdx 4 → GF256 :=
  fun i => binMatrix.mulVec (fun r => a (r, i.2)) i.1

theorem binMatrix_transpose : binMatrixᵀ = binMatrix := by decide +kernel

/-- `binMatrix * binMatrix = 1`, checked by the kernel: `binMatrix = J + 1` for the all-ones
matrix `J`, and `J * J = 4 • J = 0` in characteristic `2`. -/
theorem binMatrix_mul_self : binMatrix * binMatrix = 1 := by decide +kernel

/-- The transpose of the inverse of `binMatrix` is `binMatrix` itself: the matrix is symmetric
and an involution. -/
theorem binMatrix_inv_transpose : binMatrix⁻¹ᵀ = binMatrix := by
  rw [Matrix.transpose_nonsing_inv, binMatrix_transpose,
    Matrix.inv_eq_right_inv binMatrix_mul_self]

/-- `binMixColumns` is its own trace adjoint. -/
theorem binMixColumns_isAdjoint :
    IsAdjoint tracePairing.pi tracePairing.pi binMixColumns binMixColumns := by
  have h := isAdjoint_colMatrix (Col := Fin 4) trace binMatrix
  rw [binMatrix_transpose] at h
  exact h

/-- The state with one active byte, `1` at position `(0, 0)`. -/
def e00 : SquareIdx 4 → GF256 := fun i => if i = (0, 0) then ⟨1#8⟩ else 0

theorem e00_ne_zero : e00 ≠ 0 := fun h => by
  have h0 := congrFun h (0, 0)
  revert h0
  decide +kernel

theorem weight_e00 : weight e00 = 1 := by decide +kernel

theorem weight_binMixColumns_e00 : weight (binMixColumns e00) = 3 := by decide +kernel

/-- **`binMixColumns` fails the branch hypothesis of `aesSpec`**: one active byte becomes three,
`1 + 3 < 5`. -/
theorem binMixColumns_not_isColBranchBound : ¬ IsColBranchBound (sqCol 4) binMixColumns 5 :=
  fun h => by
    have := branch_le_weight_add h e00_ne_zero
    rw [weight_e00, weight_binMixColumns_e00] at this
    omega

/-- **`binMixColumns` fails the branch hypothesis of `elpCount_two_round_bound`.** -/
theorem binMixColumns_not_isBranchBound : ¬ isBranchBound id binMixColumns 5 := fun h => by
  have := h e00 e00_ne_zero
  rw [colWeight_id, colWeight_id, weight_e00, weight_binMixColumns_e00] at this
  omega

/-- `binMatrix` is not MDS: an MDS `4 × 4` matrix has branch number at least `5`
(`isMDS_branch_bound`), and `binMatrix` sends a vector of weight `1` to one of weight `3`. -/
theorem binMatrix_not_isMDS : ¬ IsMDS binMatrix := fun h => by
  have hb := isMDS_branch_bound h ![⟨1#8⟩, 0, 0, 0] (by decide +kernel)
  revert hb
  decide +kernel

/-! ### The branch number `5` cannot be raised -/

theorem weight_aesLinT_e00 : weight (aesLinT e00) = 4 := by decide +kernel

theorem weight_mixColumnsT_e00 : weight (mixColumnsT e00) = 4 := by decide +kernel

/-- `6` is not a branch-number lower bound of the backward map `aesLinT`: `1 + 4 < 6`. -/
theorem aesLinT_not_isBranchBound_six : ¬ isBranchBound id aesLinT 6 := fun h => by
  have := h e00 e00_ne_zero
  rw [colWeight_id, colWeight_id, weight_e00, weight_aesLinT_e00] at this
  omega

/-- `6` is not a linear branch-number lower bound of `MixColumns ∘ ShiftRows`. -/
theorem aesLin_not_isLinBranchBound_six : ¬ IsLinBranchBound sign₂ tracePairing aesLin 6 := by
  rw [isLinBranchBound_iff tracePairing_separating (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    aesLin_isAdjoint]
  exact aesLinT_not_isBranchBound_six

/-- `6` is not a linear branch-number lower bound of `MixColumns`. -/
theorem aesMixColumns_not_isLinBranchBound_six :
    ¬ IsLinBranchBound sign₂ tracePairing aesMixColumns 6 := by
  rw [isLinBranchBound_iff tracePairing_separating (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    aesMixColumns_isAdjoint]
  intro h
  have := h e00 e00_ne_zero
  rw [colWeight_id, colWeight_id, weight_e00, weight_mixColumnsT_e00] at this
  omega

/-! ### Masks and states move through different maps -/

/-- **The forward mask map is not the state map**: `aesMaskSpec.lin e00 ≠ aesLinSpec.lin e00`. -/
theorem maskSpec_lin_ne : aesMaskSpec.lin e00 ≠ aesLinSpec.lin e00 := by
  rw [aesMaskSpec_lin_apply, aesLinSpec_lin_apply]
  decide +kernel

/-! ### The nonzero-mask hypotheses are needed -/

section ZeroMasks

variable {X : Type*} [AddCommGroup X] [Fintype X]

/-- The zero trail has `|trailCorr| = |X| ^ r`, when every `lamT n` fixes the zero mask. -/
theorem natAbs_trailCorr_zero_masks (P : Pairing X (ZMod 2)) {lamT : ℕ → X → X}
    (hlam : ∀ n, lamT n 0 = 0) (γ : ℕ → X → X) (r : ℕ) :
    (trailCorr sign₂ P lamT γ r (fun _ => 0)).natAbs = Fintype.card X ^ r := by
  rw [trailCorr, natAbs_prod_range]
  simp only [hlam, walsh_zero_zero, Int.natAbs_natCast, Finset.prod_const, Finset.card_range]

/-- At the zero masks the count is `|X| ^ r · |X| ^ 2`, for every map. -/
theorem elpCount_zero_masks (P : Pairing X (ZMod 2)) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (r : ℕ) : elpCount P lam γ r 0 0 = Fintype.card X ^ r * Fintype.card X ^ 2 := by
  rw [elpCount]
  simp only [walsh_zero_zero, Int.natAbs_natCast, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

/-- `C · 2 ^ e > C` for `C > 0` and `e > 0`. -/
theorem not_mul_two_pow_le {C e : ℕ} (hC : 0 < C) (he : 0 < e) : ¬ C * 2 ^ e ≤ C := fun h => by
  have h2 : C * 1 < C * 2 ^ e := Nat.mul_lt_mul_of_pos_left (Nat.one_lt_two_pow (by omega)) hC
  omega

/-- The zero trail violates the bound `|trailCorr| · 2 ^ e ≤ |X| ^ r` for every `e > 0`. -/
theorem not_natAbs_trailCorr_zero_masks_le (P : Pairing X (ZMod 2)) {lamT : ℕ → X → X}
    (hlam : ∀ n, lamT n 0 = 0) (γ : ℕ → X → X) (r e : ℕ) (he : 0 < e) :
    ¬ (trailCorr sign₂ P lamT γ r (fun _ => 0)).natAbs * 2 ^ e ≤ Fintype.card X ^ r := by
  rw [natAbs_trailCorr_zero_masks P hlam γ r]
  exact not_mul_two_pow_le (pow_pos Fintype.card_pos r) he

/-- The zero masks violate the bound `elpCount r 0 0 · 2 ^ e ≤ |X| ^ (r + 2)` for every
`e > 0`. -/
theorem not_elpCount_zero_masks_le (P : Pairing X (ZMod 2)) (lam : ℕ → X ≃+ X)
    (γ : ℕ → X → X) (r n : ℕ) (hn : r + 2 = n) (e : ℕ) (he : 0 < e) :
    ¬ elpCount P lam γ r 0 0 * 2 ^ e ≤ Fintype.card X ^ n := by
  rw [elpCount_zero_masks, ← pow_add, hn]
  exact not_mul_two_pow_le (pow_pos Fintype.card_pos n) he

/-- Some trail violates the bound `|trailCorr| · 2 ^ e ≤ |X| ^ r` when `e > 0`: the zero trail. -/
theorem not_forall_natAbs_trailCorr_le (P : Pairing X (ZMod 2)) {lamT : ℕ → X → X}
    (hlam : ∀ n, lamT n 0 = 0) (γ : ℕ → X → X) (r e : ℕ) (he : 0 < e) :
    ¬ ∀ T : ℕ → X, (trailCorr sign₂ P lamT γ r T).natAbs * 2 ^ e ≤ Fintype.card X ^ r :=
  fun h => not_natAbs_trailCorr_zero_masks_le P hlam γ r e he (h _)

/-- Some pair of masks violates the bound `elpCount r u v · 2 ^ e ≤ |X| ^ (r + 2)` when `e > 0`:
the zero masks. -/
theorem not_forall_elpCount_le (P : Pairing X (ZMod 2)) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (r n : ℕ) (hn : r + 2 = n) (e : ℕ) (he : 0 < e) :
    ¬ ∀ u v : X, elpCount P lam γ r u v * 2 ^ e ≤ Fintype.card X ^ n :=
  fun h => not_elpCount_zero_masks_le P lam γ r n hn e he (h 0 0)

end ZeroMasks

/-- **The hypothesis `T 0 ≠ 0` of `AES.four_round_correlation` is needed**: without it the bound
fails at the zero trail, which has `|trailCorr| = |X| ^ 4`. -/
theorem four_round_correlation_needs_h0 :
    ¬ ∀ T : ℕ → SquareIdx 4 → GF256,
      (trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox) 4
        T).natAbs * 2 ^ 75 ≤ Fintype.card (SquareIdx 4 → GF256) ^ 4 :=
  not_forall_natAbs_trailCorr_le tracePairing.pi
    (fun _ => aesLin_isAdjoint.map_zero tracePairing_separating.pi) _ 4 75 (by norm_num)

/-- **The hypothesis `u ≠ 0` of `AES.two_round_elp` is needed**: without it the bound fails at the
zero masks, where `elpCount 2 0 0 = |X| ^ 2 · |X| ^ 2`. -/
theorem two_round_elp_needs_hu :
    ¬ ∀ u v : SquareIdx 4 → GF256,
      elpCount tracePairing.pi (fun _ => aesLin) (fun _ => bricklayer fun _ => sbox) 2 u v
        * 2 ^ 24 ≤ Fintype.card (SquareIdx 4 → GF256) ^ 4 :=
  not_forall_elpCount_le tracePairing.pi _ _ 2 4 rfl 24 (by norm_num)

end Linear.Checks
