/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.AESSbox
import WideTrail.Linear.Hull
import WideTrail.Differential.AESProb
import WideTrail.Algebra.Transpose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# AES: linear trails and the two-round linear hull, under the trace pairing

The keyed rounds are those of `Differential/AESProb.lean`: `Scheduled.run (fun _ => aesLin)
(fun _ => bricklayer fun _ => sbox) r k`, whose round `n` maps `x` to
`MixColumns (ShiftRows (SubBytes (x + k n)))`, with the real S-box `AES.sbox` and the real
`MixColumns` matrix `aesMatrix`. Masks are paired with states by the bundle sum of the trace
pairing `GF256.tracePairing`, `⟨u, x⟩ = ∑ᵢ trace (uᵢ * xᵢ)`. The trace pairing is chosen for AES
because under it the adjoint of a `GF(2⁸)`-matrix is its field transpose; it is not *the* pairing
of the type `GF256`, and the bit pairing is not treated here.

## Masks through the linear layer

* `aesInvMatrixT = circ(0e, 09, 0d, 0b)` satisfies `aesMatrixᵀ * aesInvMatrixT = 1` and
  `aesInvMatrixT * aesMatrixᵀ = 1` (both checked by the kernel), so it is the transpose of the
  inverse of the `MixColumns` matrix (`aesInvMatrixT_eq`).
* `mixColumnsT` applies `aesMatrixᵀ` column by column; it is a trace adjoint of `aesMixColumns`
  (`aesMixColumns_isAdjoint`). `aesLinT = ShiftRows⁻¹ ∘ mixColumnsT` is a trace adjoint of
  `aesLin = MixColumns ∘ ShiftRows` (`aesLin_isAdjoint`), and the only one (`aesLinT_unique`).
* **The mask convention.** Masks are propagated forward through the inverse of the adjoint, as
  fixed in `Masks.lean`. The forward mask map is the linear layer of the wide-trail
  specification `aesMaskSpec = aesSpec id mixColumnsInvT …`: its `lin` is
  `mixColumnsInvT ∘ ShiftRows`, with the same `ShiftRows` as `aesLinSpec`
  (`aesMaskSpec_disp`, `aesLinSpec_disp`) and `MixColumns` replaced by `mixColumnsInvT`, which
  applies `aesInvMatrixT` column by column (`aesMaskSpec_lin_apply`, `aesLinSpec_lin_apply`
  for the two maps). `aesLinT` and `aesMaskSpec.lin` are inverse to each other
  (`aesLinT_maskSpec`, `maskSpec_aesLinT`), and the forward mask map keeps the pairing:
  `⟨aesMaskSpec.lin w, aesLin y⟩ = ⟨w, y⟩` (`dot_maskSpec_aesLin`). The backward reading,
  through `aesLinT`, is equivalent (`maskTrail_iff_backward`).

## Branch numbers

* `aesMatrix_transpose_isMDS`: `aesMatrixᵀ` is MDS (`isMDS_transpose_iff` and
  `aesMatrix_isMDS`).
* `mixColumnsT_isColBranchBound`, `mixColumnsInvT_isColBranchBound`: every column active on
  either side of `mixColumnsT`, or of `mixColumnsInvT`, carries at least `5` active bytes across
  input and output (for `mixColumnsInvT`, apply the MDS bound of `aesMatrixᵀ` to its output).
* `mixColumnsT_isBranchBound`, `aesLinT_isBranchBound`: the backward maps have branch number at
  least `5`.
* `aesMixColumns_isLinBranchBound`, `aesLin_isLinBranchBound`: the linear branch numbers of
  `MixColumns` and of `MixColumns ∘ ShiftRows`, defined through correlations
  (`IsLinBranchBound`), are at least `5` (`isLinBranchBound_iff`).

## Trails

* `walsh_run_expansion`: the fixed-key expansion `walsh_run_eq_sum_trails` for these rounds: for
  every key vector `k`, `|X| ^ r · walsh (run (r + 1) k) u v` is the sum over the trails `T_d`
  from `u` to `v` of `trailPhase k T_d · trailCorr T_d`, with `trailCorr` read through `aesLinT`.
* `isTrail_of_corr_ne_zero`: a trail with a nonzero correlation is an `aesMaskSpec.IsTrail`.
* `rounds_correlation`: with the S-box linearity bound `32` (`AES.sbox_isLinearityBound`) and
  `32 · 2³ ≤ 256`, every `r`-round trail with a nonzero input mask has
  `|trailCorr| · 2 ^ (3 A) ≤ |X| ^ r`, where `A = r / 4 · 25 + (if 2 ≤ r % 4 then 5 else 0)` is
  the activity lower bound of `IsTrail.bound_rounds` (`trailCorr_le_of_spec`). At the AES round
  counts:

  | rounds | active S-boxes, at least | trail correlation, at most in absolute value |
  | ------ | ------------------------ | -------------------------------------------- |
  | 4      | 25                       | `2⁻⁷⁵`                                       |
  | 10     | 55                       | `2⁻¹⁶⁵`                                      |
  | 12     | 75                       | `2⁻²²⁵`                                      |
  | 14     | 80                       | `2⁻²⁴⁰`                                      |

  These are `four_round_correlation`, `ten_round_correlation`, `twelve_round_correlation` and
  `fourteen_round_correlation`; the trail correlation is `trailCorr / |X| ^ r`. The four-round
  row is the bound the designers state for four-round linear trails (no correlation above
  `2⁻⁷⁵`, Rijndael proposal §8.2.2), here for the rounds modelled above and under the trace
  pairing. The designers state it for bit masks. The two pairings differ by a bytewise
  relabelling of masks through `GF256.phi` (`walsh_maskRelabel`), but `phi` is not shown to be
  a bijection, so the transfer to bit masks is not proved here.
  `four_round_contribution` restates the four-round bound for one summand of the fixed-key
  expansion, under any key vector.

## The linear hull

* `two_round_elp`: for every nonzero input mask `u` and every output mask `v`,
  `elpCount 2 u v · 2²⁴ ≤ |X| ^ 4`: the squared correlation over two rounds, averaged over an
  additional independent uniform key per round, is at most `2⁻²⁴ = (32 / 256) ^ (2 (5 - 1))`.
  It is `elpCount_two_round_bound` with the S-box bound `32` and the branch number `5` of the
  backward map `aesLinT`.
* `rounds_elp`: the same bound `2⁻²⁴` over any `R ≥ 2` rounds (`elpCount_bound_of_two_rounds`).

`elpCount` is the natural-number count of `Hull.lean` (as the differential counts are): divided
by `|X| ^ R · |X| ^ 2` it is the expected linear probability, so each hull bound is stated as an
inequality between natural numbers.

As context only: Keliher and Sui give the exact maximum two-round expected linear probability of
AES as `109,953,193 / 2⁵⁴ ≈ 1.638 · 2⁻²⁸` (IACR ePrint 2005/321, abstract). That value is not
proved here; it shows how coarse `2⁻²⁴` is.

## What is not claimed

* A trail bound bounds one trail: one summand of the fixed-key expansion, the same in magnitude
  for every key vector. It is not a bound on the correlation of AES for a fixed key, a scheduled
  key or fixed round constants, which is a signed sum over all trails from `u` to `v`.
* The active S-box counts are lower bounds from `IsTrail.bound_rounds`; neither they nor the
  trail bounds are claimed to be attained.
* The hull bounds average over an additional independent uniform key per round. Nothing is said
  about the AES key schedule. Only two rounds are charged, and `2⁻²⁴` is not close to the exact
  two-round maximum above.
* The rounds are modelled as in `Differential/AESProb.lean`: every round has `MixColumns`, there
  is no final round without `MixColumns` and no final whitening key.
* The bit pairing is not treated: the bit-pairing linear approximation table of the S-box is not
  computed or certified, and no bound on the bit-pairing correlations of AES is derived. In
  particular the designers' four-round bound for bit masks is not proved. Rijndael with a
  256-bit block is not treated. Nothing here is a statement about the data or time complexity
  of a linear attack, or about the security of AES.
-/

set_option autoImplicit false
-- The exponents here are 24 to 240; `rw` would otherwise emit a notice for declining to
-- evaluate `2 ^ 165` as a numeral, which it should decline to do.
set_option exponentiation.threshold 1000

namespace AES

open Linear GF256
open scoped Matrix

/-! ### `MixColumns`, its transpose and its transposed inverse -/

/-- The transpose of the inverse of the `MixColumns` matrix, `circ(0e, 09, 0d, 0b)`
(`aesInvMatrixT_eq`). -/
def aesInvMatrixT : Matrix (Fin 4) (Fin 4) GF256 :=
  !![⟨0x0e#8⟩, ⟨0x09#8⟩, ⟨0x0d#8⟩, ⟨0x0b#8⟩;
     ⟨0x0b#8⟩, ⟨0x0e#8⟩, ⟨0x09#8⟩, ⟨0x0d#8⟩;
     ⟨0x0d#8⟩, ⟨0x0b#8⟩, ⟨0x0e#8⟩, ⟨0x09#8⟩;
     ⟨0x09#8⟩, ⟨0x0d#8⟩, ⟨0x0b#8⟩, ⟨0x0e#8⟩]

/-- `aesMatrixᵀ * aesInvMatrixT = 1`, checked by the kernel. -/
theorem transpose_mul_invT : aesMatrixᵀ * aesInvMatrixT = 1 := by decide +kernel

/-- `aesInvMatrixT * aesMatrixᵀ = 1`, checked by the kernel. -/
theorem invT_mul_transpose : aesInvMatrixT * aesMatrixᵀ = 1 := by decide +kernel

/-- `aesInvMatrixT` is the transpose of the inverse of the `MixColumns` matrix. -/
theorem aesInvMatrixT_eq : aesInvMatrixT = aesMatrix⁻¹ᵀ := by
  rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv transpose_mul_invT]

/-- `aesMatrixᵀ` applied column by column: the trace adjoint of `MixColumns`
(`aesMixColumns_isAdjoint`). -/
def mixColumnsT (a : SquareIdx 4 → GF256) : SquareIdx 4 → GF256 :=
  fun i => aesMatrixᵀ.mulVec (fun r => a (r, i.2)) i.1

/-- `aesInvMatrixT` applied column by column: the mixing layer of the forward mask map. -/
def mixColumnsInvT (a : SquareIdx 4 → GF256) : SquareIdx 4 → GF256 :=
  fun i => aesInvMatrixT.mulVec (fun r => a (r, i.2)) i.1

theorem mixColumnsT_mixColumnsInvT (a : SquareIdx 4 → GF256) :
    mixColumnsT (mixColumnsInvT a) = a := by
  funext i
  change aesMatrixᵀ.mulVec (aesInvMatrixT.mulVec (fun r => a (r, i.2))) i.1 = a i
  rw [Matrix.mulVec_mulVec, transpose_mul_invT, Matrix.one_mulVec]

theorem mixColumnsInvT_mixColumnsT (a : SquareIdx 4 → GF256) :
    mixColumnsInvT (mixColumnsT a) = a := by
  funext i
  change aesInvMatrixT.mulVec (aesMatrixᵀ.mulVec (fun r => a (r, i.2))) i.1 = a i
  rw [Matrix.mulVec_mulVec, invT_mul_transpose, Matrix.one_mulVec]

theorem mixColumnsT_zero : mixColumnsT 0 = 0 := by
  funext i
  change aesMatrixᵀ.mulVec 0 i.1 = 0
  rw [Matrix.mulVec_zero]
  rfl

/-- **The field transpose of `MixColumns` is a trace adjoint of it**:
`⟨v, MixColumns y⟩ = ⟨mixColumnsT v, y⟩` for the bundle sum of the trace pairing. -/
theorem aesMixColumns_isAdjoint :
    IsAdjoint tracePairing.pi tracePairing.pi aesMixColumns mixColumnsT :=
  isAdjoint_colMatrix trace aesMatrix

/-! ### Branch numbers -/

/-- The transpose of the `MixColumns` matrix is MDS. -/
theorem aesMatrix_transpose_isMDS : IsMDS aesMatrixᵀ :=
  isMDS_transpose_iff.mpr aesMatrix_isMDS

/-- Every column active on either side of `mixColumnsT` carries at least `5` active bytes across
input and output. -/
theorem mixColumnsT_isColBranchBound : IsColBranchBound (sqCol 4) mixColumnsT 5 := by
  intro a ξ hpos
  rw [localWeight_sqCol_eq_weight, localWeight_sqCol_eq_weight] at hpos ⊢
  have heq : (fun r => mixColumnsT a (r, ξ)) = aesMatrixᵀ.mulVec (fun r => a (r, ξ)) := rfl
  rw [heq] at hpos ⊢
  exact isMDS_branch_bound aesMatrix_transpose_isMDS (fun r => a (r, ξ)) hpos

/-- Every column active on either side of `mixColumnsInvT` carries at least `5` active bytes
across input and output: the column `y` and its image `x = aesInvMatrixT y` satisfy
`y = aesMatrixᵀ x`, and `aesMatrixᵀ` is MDS. -/
theorem mixColumnsInvT_isColBranchBound : IsColBranchBound (sqCol 4) mixColumnsInvT 5 := by
  intro a ξ hpos
  rw [localWeight_sqCol_eq_weight, localWeight_sqCol_eq_weight] at hpos ⊢
  have heq : (fun r => mixColumnsInvT a (r, ξ))
      = aesInvMatrixT.mulVec (fun r => a (r, ξ)) := rfl
  rw [heq] at hpos ⊢
  have hx : aesMatrixᵀ.mulVec (aesInvMatrixT.mulVec (fun r => a (r, ξ)))
      = fun r => a (r, ξ) := by
    rw [Matrix.mulVec_mulVec, transpose_mul_invT, Matrix.one_mulVec]
  have h := isMDS_branch_bound aesMatrix_transpose_isMDS
    (aesInvMatrixT.mulVec (fun r => a (r, ξ))) (by rw [hx]; omega)
  rw [hx] at h
  omega

theorem mixColumnsInvT_nondegenerate : NonDegenerate mixColumnsInvT := fun a ha => by
  rw [← mixColumnsT_mixColumnsInvT a, ha, mixColumnsT_zero]

/-- `mixColumnsT` has branch number at least `5`. -/
theorem mixColumnsT_isBranchBound : isBranchBound id mixColumnsT 5 := fun a ha => by
  rw [colWeight_id, colWeight_id]
  exact branch_le_weight_add mixColumnsT_isColBranchBound ha

/-- **The linear branch number of `MixColumns` is at least `5`**, under the trace pairing: every
pair of masks `(u, v) ≠ (0, 0)` at which `MixColumns` has a nonzero Walsh value has at least `5`
active bytes across `u` and `v`. -/
theorem aesMixColumns_isLinBranchBound :
    IsLinBranchBound sign₂ tracePairing aesMixColumns 5 :=
  (isLinBranchBound_iff tracePairing_separating (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    aesMixColumns_isAdjoint 5).mpr mixColumnsT_isBranchBound

/-! ### The mask specification -/

/-- The wide-trail specification of the forward mask map: `ShiftRows`, then `mixColumnsInvT`. The
`sbox` field is the placeholder `id`, as in `aesLinSpec`: support preservation by the S-box layer
is derived from bijectivity (`isTrail_of_corr_ne_zero`), not read from this field. -/
def aesMaskSpec : WideTrailSpec (SquareIdx 4) (Fin 4) GF256 :=
  aesSpec id mixColumnsInvT (fun _ => rfl) mixColumnsInvT_isColBranchBound
    mixColumnsInvT_nondegenerate

@[simp] theorem aesMaskSpec_fourRoundBound : aesMaskSpec.fourRoundBound = 25 := rfl

@[simp] theorem aesMaskSpec_branch : aesMaskSpec.branch = 5 := rfl

/-- The mask specification uses the AES `ShiftRows`. -/
theorem aesMaskSpec_disp : aesMaskSpec.disp = rowShiftPerm 4 := rfl

/-- The state specification `aesLinSpec` uses the same `ShiftRows`. -/
theorem aesLinSpec_disp : aesLinSpec.disp = rowShiftPerm 4 := rfl

/-- The forward mask map: `ShiftRows`, then `mixColumnsInvT`. -/
theorem aesMaskSpec_lin_apply (b : SquareIdx 4 → GF256) :
    aesMaskSpec.lin b = mixColumnsInvT (transpose (rowShiftPerm 4) b) := rfl

/-- The state map of `aesLinSpec`: `ShiftRows`, then `MixColumns`. -/
theorem aesLinSpec_lin_apply (b : SquareIdx 4 → GF256) :
    aesLinSpec.lin b = aesMixColumns (transpose (rowShiftPerm 4) b) := rfl

/-- The backward mask map: `mixColumnsT`, then `ShiftRows⁻¹`. It is the trace adjoint of
`aesLin` (`aesLin_isAdjoint`). -/
def aesLinT (w : SquareIdx 4 → GF256) : SquareIdx 4 → GF256 :=
  transpose (rowShiftPerm 4).symm (mixColumnsT w)

/-- **`aesLinT` is a trace adjoint of `aesLin = MixColumns ∘ ShiftRows`**:
`⟨v, aesLin y⟩ = ⟨aesLinT v, y⟩`. A permutation of bundles has its inverse as an adjoint
(`isAdjoint_transpose`), and adjoints compose in the reverse order (`IsAdjoint.comp`). -/
theorem aesLin_isAdjoint : IsAdjoint tracePairing.pi tracePairing.pi aesLin aesLinT := by
  intro v y
  rw [aesLin_apply]
  exact (IsAdjoint.comp (isAdjoint_transpose tracePairing (rowShiftPerm 4))
    aesMixColumns_isAdjoint) v y

/-- `aesLinT` is the only trace adjoint of `aesLin`: the trace pairing is separating. -/
theorem aesLinT_unique {Lt : (SquareIdx 4 → GF256) → (SquareIdx 4 → GF256)}
    (h : IsAdjoint tracePairing.pi tracePairing.pi aesLin Lt) : Lt = aesLinT :=
  h.unique tracePairing_separating.pi aesLin_isAdjoint

/-- `aesLinT` undoes the forward mask map. -/
theorem aesLinT_maskSpec (b : SquareIdx 4 → GF256) : aesLinT (aesMaskSpec.lin b) = b := by
  rw [aesMaskSpec_lin_apply, aesLinT, mixColumnsT_mixColumnsInvT]
  funext i
  simp [transpose]

/-- The forward mask map undoes `aesLinT`. -/
theorem maskSpec_aesLinT (w : SquareIdx 4 → GF256) : aesMaskSpec.lin (aesLinT w) = w := by
  rw [aesMaskSpec_lin_apply, aesLinT]
  have h : transpose (rowShiftPerm 4) (transpose (rowShiftPerm 4).symm (mixColumnsT w))
      = mixColumnsT w := by
    funext i
    simp [transpose]
  rw [h, mixColumnsInvT_mixColumnsT]

/-- **Masks move contragrediently to states**: `⟨aesMaskSpec.lin w, aesLin y⟩ = ⟨w, y⟩`. -/
theorem dot_maskSpec_aesLin (w y : SquareIdx 4 → GF256) :
    tracePairing.pi.dot (aesMaskSpec.lin w) (aesLin y) = tracePairing.pi.dot w y := by
  rw [aesLin_isAdjoint, aesLinT_maskSpec]

/-- **The backward map `aesLinT` has branch number at least `5`.** `ShiftRows⁻¹` moves no
activity, and `mixColumnsT` has branch number at least `5`. -/
theorem aesLinT_isBranchBound : isBranchBound id aesLinT 5 := fun a ha => by
  rw [colWeight_id, colWeight_id, aesLinT, (supportPerm_transpose _).weight_eq]
  exact branch_le_weight_add mixColumnsT_isColBranchBound ha

/-- **The linear branch number of `MixColumns ∘ ShiftRows` is at least `5`**, under the trace
pairing. -/
theorem aesLin_isLinBranchBound : IsLinBranchBound sign₂ tracePairing aesLin 5 :=
  (isLinBranchBound_iff tracePairing_separating (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    aesLin_isAdjoint 5).mpr aesLinT_isBranchBound

/-- **The backward reading of a mask trail.** `T` is a trail of the mask specification exactly
when, at every round `n < r`, the S-box output mask `aesLinT (T (n + 1))` has the support of the
S-box input mask `T n`. -/
theorem maskTrail_iff_backward (T : ℕ → SquareIdx 4 → GF256) (r : ℕ) :
    aesMaskSpec.IsTrail T r
      ↔ ∀ n < r, activePattern (aesLinT (T (n + 1))) = activePattern (T n) :=
  Linear.isTrail_iff_backward aesMaskSpec (Function.LeftInverse.injective maskSpec_aesLinT)
    aesLinT_maskSpec T r

/-! ### Trails -/

theorem sbox_bijective : Function.Bijective sbox := sboxEquiv.bijective

/-- `32 · 2³ ≤ 256`: the S-box linearity bound `32` clears a factor `2³` per active S-box. -/
theorem sbox_clears : 32 * 2 ^ 3 ≤ Fintype.card GF256 := by
  rw [card_gf256]
  norm_num

/-- **The fixed-key expansion for AES.** For every key vector `k`,
`|X| ^ r · walsh (run (r + 1) k) u v = ∑_d trailPhase k T_d · trailCorr T_d` over the trails
`T_d = throughTrail u d v`, with the trail correlations read through the trace adjoint
`aesLinT`. -/
theorem walsh_run_expansion (r : ℕ) (k : Fin (r + 1) → SquareIdx 4 → GF256)
    (u v : SquareIdx 4 → GF256) :
    (Fintype.card (SquareIdx 4 → GF256) : ℤ) ^ r
        * walsh sign₂ tracePairing.pi tracePairing.pi
            (Scheduled.run (fun _ => aesLin) (fun _ => bricklayer fun _ => sbox) (r + 1) k) u v
      = ∑ d : Fin r → SquareIdx 4 → GF256,
          trailPhase sign₂ tracePairing.pi (r + 1) k (Scheduled.throughTrail u d v)
            * trailCorr sign₂ tracePairing.pi (fun _ => aesLinT)
                (fun _ => bricklayer fun _ => sbox) (r + 1) (Scheduled.throughTrail u d v) :=
  walsh_run_eq_sum_trails tracePairing_separating.pi (fun _ => aesLin) (fun _ => aesLinT)
    (fun _ => aesLin_isAdjoint) _ r k u v

/-- **A trail with a nonzero correlation is a trail of the mask specification.** -/
theorem isTrail_of_corr_ne_zero {r : ℕ} {T : ℕ → SquareIdx 4 → GF256}
    (h : trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox)
      r T ≠ 0) :
    aesMaskSpec.IsTrail T r :=
  Linear.isTrail_of_trailCorr_ne_zero tracePairing_separating aesMaskSpec (s := fun _ _ => sbox)
    (fun _ _ _ => sbox_bijective) (fun _ _ => aesLinT_maskSpec) h

/-- **Every round count**: an `r`-round linear trail with a nonzero input mask has
`|trailCorr| · 2 ^ (3 A) ≤ |X| ^ r` for `A = r / 4 · 25 + (if 2 ≤ r % 4 then 5 else 0)`, the
activity lower bound of `IsTrail.bound_rounds`: its correlation is at most `2 ^ (-3 A)` in
absolute value. One trail, not the correlation of AES for a fixed key. -/
theorem rounds_correlation (r : ℕ) {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox)
        r T).natAbs * 2 ^ (3 * (r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0)))
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ r := by
  have h := trailCorr_le_of_spec tracePairing_separating aesMaskSpec (s := fun _ => sbox)
    (fun _ => sbox_bijective) (fun _ => sbox_isLinearityBound) sbox_clears aesLinT_maskSpec
    (r := r) h0
  rwa [aesMaskSpec_fourRoundBound, aesMaskSpec_branch] at h

/-- **Four rounds of AES: every linear trail with a nonzero input mask has correlation at most
`2⁻⁷⁵` in absolute value.** At least `25` active S-boxes, each with correlation at most `2⁻³`.
This bounds one trail, not the correlation of AES for a fixed key. -/
theorem four_round_correlation {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox)
        4 T).natAbs * 2 ^ 75
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 4 := by
  have h := trailCorr_le_of_spec tracePairing_separating aesMaskSpec (s := fun _ => sbox)
    (fun _ => sbox_bijective) (fun _ => sbox_isLinearityBound) sbox_clears aesLinT_maskSpec
    (r := 4) h0
  have he : 3 * (4 / 4 * aesMaskSpec.fourRoundBound
      + (if 2 ≤ 4 % 4 then aesMaskSpec.branch else 0)) = 75 := by
    rw [aesMaskSpec_fourRoundBound, aesMaskSpec_branch]
    decide
  rwa [he] at h

/-- **Ten rounds (the round count of AES-128): every linear trail with a nonzero input mask has
correlation at most `2⁻¹⁶⁵` in absolute value.** At least `55` active S-boxes. One trail. -/
theorem ten_round_correlation {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox)
        10 T).natAbs * 2 ^ 165
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 10 := by
  have h := trailCorr_le_of_spec tracePairing_separating aesMaskSpec (s := fun _ => sbox)
    (fun _ => sbox_bijective) (fun _ => sbox_isLinearityBound) sbox_clears aesLinT_maskSpec
    (r := 10) h0
  have he : 3 * (10 / 4 * aesMaskSpec.fourRoundBound
      + (if 2 ≤ 10 % 4 then aesMaskSpec.branch else 0)) = 165 := by
    rw [aesMaskSpec_fourRoundBound, aesMaskSpec_branch]
    decide
  rwa [he] at h

/-- **Twelve rounds (the round count of AES-192): at most `2⁻²²⁵`.** At least `75` active
S-boxes. One trail. -/
theorem twelve_round_correlation {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox)
        12 T).natAbs * 2 ^ 225
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 12 := by
  have h := trailCorr_le_of_spec tracePairing_separating aesMaskSpec (s := fun _ => sbox)
    (fun _ => sbox_bijective) (fun _ => sbox_isLinearityBound) sbox_clears aesLinT_maskSpec
    (r := 12) h0
  have he : 3 * (12 / 4 * aesMaskSpec.fourRoundBound
      + (if 2 ≤ 12 % 4 then aesMaskSpec.branch else 0)) = 225 := by
    rw [aesMaskSpec_fourRoundBound, aesMaskSpec_branch]
    decide
  rwa [he] at h

/-- **Fourteen rounds (the round count of AES-256): at most `2⁻²⁴⁰`.** At least `80` active
S-boxes. One trail. -/
theorem fourteen_round_correlation {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox)
        14 T).natAbs * 2 ^ 240
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 14 := by
  have h := trailCorr_le_of_spec tracePairing_separating aesMaskSpec (s := fun _ => sbox)
    (fun _ => sbox_bijective) (fun _ => sbox_isLinearityBound) sbox_clears aesLinT_maskSpec
    (r := 14) h0
  have he : 3 * (14 / 4 * aesMaskSpec.fourRoundBound
      + (if 2 ≤ 14 % 4 then aesMaskSpec.branch else 0)) = 240 := by
    rw [aesMaskSpec_fourRoundBound, aesMaskSpec_branch]
    decide
  rwa [he] at h

/-- **One summand of the four-round fixed-key expansion**: under every key vector `k`, the
contribution `trailPhase k T · trailCorr T` of a trail with a nonzero input mask is at most
`2⁻⁷⁵ · |X| ^ 4` in absolute value. This bounds one summand; the fixed-key correlation is the
signed sum of all of them. -/
theorem four_round_contribution (k : Fin 4 → SquareIdx 4 → GF256) {T : ℕ → SquareIdx 4 → GF256}
    (h0 : T 0 ≠ 0) :
    (trailPhase sign₂ tracePairing.pi 4 k T
        * trailCorr sign₂ tracePairing.pi (fun _ => aesLinT) (fun _ => bricklayer fun _ => sbox)
          4 T).natAbs * 2 ^ 75
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 4 := by
  rw [natAbs_trailPhase_mul]
  exact four_round_correlation h0

/-! ### The linear hull -/

/-- The arithmetic of the hull bound: `(32 / 256) ^ (2 (5 - 1)) = 2⁻²⁴`. -/
theorem mul_two_pow_24_le {E C : ℕ}
    (h : E * Fintype.card GF256 ^ (2 * (5 - 1)) ≤ 32 ^ (2 * (5 - 1)) * C) :
    E * 2 ^ 24 ≤ C := by
  rw [card_gf256] at h
  have h' : E * 2 ^ 24 * 2 ^ 40 ≤ C * 2 ^ 40 := by
    calc E * 2 ^ 24 * 2 ^ 40 = E * 256 ^ (2 * (5 - 1)) := by norm_num [mul_assoc]
      _ ≤ 32 ^ (2 * (5 - 1)) * C := h
      _ = C * 2 ^ 40 := by norm_num [mul_comm]
  exact Nat.le_of_mul_le_mul_right h' (by positivity)

/-- **The two-round linear hull bound for AES**: for every nonzero input mask `u` and every
output mask `v`, `elpCount 2 u v · 2²⁴ ≤ |X| ^ 4`. The squared correlation of `(u, v)` over two
rounds, averaged over an additional independent uniform key per round, is at most `2⁻²⁴`. It
says nothing about one fixed key. -/
theorem two_round_elp {u : SquareIdx 4 → GF256} (hu : u ≠ 0) (v : SquareIdx 4 → GF256) :
    elpCount tracePairing.pi (fun _ => aesLin) (fun _ => bricklayer fun _ => sbox) 2 u v
        * 2 ^ 24
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 4 :=
  mul_two_pow_24_le (elpCount_two_round_bound tracePairing_separating (fun _ => aesLin)
    (fun _ => aesLinT) (fun _ => aesLin_isAdjoint) (fun _ _ => sbox)
    (fun _ _ _ => sbox_bijective) (fun _ _ _ => sbox_isLinearityBound) aesLinT_isBranchBound
    hu v)

/-- **The hull bound over `R ≥ 2` rounds**: `elpCount R u v · 2²⁴ ≤ |X| ^ (R + 2)` for every
nonzero `u`. The expected linear probability over `R` rounds, in the same independent-key model,
is at most `2⁻²⁴`; only two rounds are charged. -/
theorem rounds_elp (R : ℕ) (hR : 2 ≤ R) {u : SquareIdx 4 → GF256} (hu : u ≠ 0)
    (v : SquareIdx 4 → GF256) :
    elpCount tracePairing.pi (fun _ => aesLin) (fun _ => bricklayer fun _ => sbox) R u v
        * 2 ^ 24
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ (R + 2) :=
  mul_two_pow_24_le (elpCount_bound_of_two_rounds tracePairing_separating (fun _ => aesLin)
    (fun _ => aesLinT) (fun _ => aesLin_isAdjoint) (fun _ => bricklayer fun _ => sbox)
    (fun _ _ => sbox) R 0 (by omega) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ _ _ => rfl) (fun _ _ _ _ => sbox_bijective) (fun _ _ _ _ => sbox_isLinearityBound)
    aesLinT_isBranchBound hu v)

end AES
