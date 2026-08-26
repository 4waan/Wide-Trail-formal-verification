/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.AES
import WideTrail.Layer2.GF256
import WideTrail.Layer2.MDS
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormDet

/-!
# The real AES `MixColumns`, unconditionally

`AES.lean` states `aes_four_round`/`aes128_ten_round` as an implication: *given* that
MixColumns has branch number `5`, the bound holds. That hypothesis was left free precisely
because closing it needs a concrete field and a minor enumeration — which `WideTrail.GF256`
and `WideTrail.MDS` now supply. This file plugs in the real matrix and discharges it, turning
the AES bound from conditional to unconditional (modulo the S-box, which stays abstract:
`PreserveSupport` is free for any bricklayer of invertible S-boxes, and nothing about the
concrete AES S-box is used anywhere in the wide-trail argument).

Verifying `aesMatrix_isMDS` ran into two independent Mathlib limitations, discovered by
testing directly rather than assumed:

* `Matrix.det`'s general definition (a sum over `Equiv.Perm`) does not reduce under `decide`
  at all once `n ≥ 3` — not a speed problem, a `did not reduce to isTrue or isFalse` one, the
  same flavor of obstacle as `GaloisField`'s. `Matrix.det_fin_three` (an explicit six-term
  formula) sidesteps it; `Finset.orderIsoOfFin` — the natural way to turn "3 of these 4
  indices" into a submatrix selector — turns out to have the *same* problem independently,
  even for a single, fully concrete instance.
* Even after both are avoided, brute-force enumeration over all injective `Fin 3 → Fin 4`
  pairs (`4096` of them) still stalls `decide` outright — the enumeration itself, not the
  arithmetic, confirmed by timing the same check with trivial arithmetic swapped in.

So the order-`3` case is handled the way one would by hand: every injective `r : Fin 3 → Fin
4` is `Fin.succAbove m` (the canonical embedding omitting `m`) composed with some permutation
of `Fin 3` (`factor3`, itself decided over the *much* smaller `Fin 4 × Perm (Fin 3)` space).
Determinant is invariant up to sign under such row/column permutations
(`Matrix.det_permute`/`det_permute'`), so checking nonsingularity reduces to the `16` canonical
minors `minors3_ne_zero`. Order `4` is handled the same way, reducing to the single matrix
`aesMatrix` itself (`det4_ne_zero`, via the `eval_det` normalizer, which unlike `decide` *can*
evaluate a concrete determinant of this order).
-/

set_option autoImplicit false

open GF256

/-- The AES `MixColumns` matrix over `GF(2⁸)`: the circulant with first row `[2,3,1,1]`. -/
def aesMatrix : Matrix (Fin 4) (Fin 4) GF256 :=
  !![⟨2#8⟩, ⟨3#8⟩, ⟨1#8⟩, ⟨1#8⟩;
     ⟨1#8⟩, ⟨2#8⟩, ⟨3#8⟩, ⟨1#8⟩;
     ⟨1#8⟩, ⟨1#8⟩, ⟨2#8⟩, ⟨3#8⟩;
     ⟨3#8⟩, ⟨1#8⟩, ⟨1#8⟩, ⟨2#8⟩]

set_option maxHeartbeats 1000000 in
-- the 16-case enumeration below needs more room than the defaults
set_option maxRecDepth 4000 in
/-- The `16` order-`3` minors of `aesMatrix`, indexed by which row and which column are
omitted: all nonzero. `det_fin_three` turns the determinant into a concrete six-term formula
(avoiding the reduction wall in `Matrix.det`'s general definition); the remaining `4 × 4`
enumeration is small enough for `decide` outright. -/
theorem minors3_ne_zero :
    ∀ m m' : Fin 4, (aesMatrix.submatrix (Fin.succAbove m) (Fin.succAbove m')).det ≠ 0 := by
  intro m m'
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  revert m m'
  decide

/-- The sole order-`4` "minor" — `aesMatrix` itself. `decide` cannot evaluate a `4×4`
determinant at all (same reduction wall), so this goes through `eval_det`, Mathlib's
determinant normal-form tactic, instead. -/
theorem det4_ne_zero : aesMatrix.det ≠ 0 := by
  simp only [aesMatrix]
  eval_det
  decide

/-- Every injective `Fin 3 → Fin 4` factors as the canonical embedding omitting some `m`,
composed with a permutation of `Fin 3`. Decided over `Fin 4 × Perm (Fin 3)` (`24` values),
not over the `4096`-element space of injective-function pairs that stalls `decide` directly. -/
theorem factor3 : ∀ r : Fin 3 → Fin 4, Function.Injective r →
    ∃ (m : Fin 4) (σ : Equiv.Perm (Fin 3)), r = Fin.succAbove m ∘ σ := by decide

/-- `Equiv.Perm.sign`, cast down to `GF(2⁸)`, is never zero: it is always `±1`, and neither is
zero in any field. -/
theorem sign_cast_ne_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : GF256) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **The MDS property of AES `MixColumns`**, stated first over raw injective functions
(`aesMatrix_isMDS'`) where the row/column permutation argument above applies directly, then
transported to the `Finset`-indexed `IsMDS` (`aesMatrix_isMDS`) by instantiating at the
canonical order-embeddings, which are themselves injective. -/
theorem aesMatrix_isMDS' : ∀ (k : ℕ) (r c : Fin k → Fin 4), Function.Injective r →
    Function.Injective c → (aesMatrix.submatrix r c).det ≠ 0 := by
  have hk4 : ∀ (r c : Fin 4 → Fin 4), Function.Injective r → Function.Injective c →
      (aesMatrix.submatrix r c).det ≠ 0 := by
    intro r c hr hc
    have hrbij : Function.Bijective r := (Fintype.bijective_iff_injective_and_card r).mpr ⟨hr, rfl⟩
    have hcbij : Function.Bijective c := (Fintype.bijective_iff_injective_and_card c).mpr ⟨hc, rfl⟩
    have heq : aesMatrix.submatrix r c
        = (aesMatrix.submatrix (Equiv.ofBijective r hrbij) id).submatrix
            id (Equiv.ofBijective c hcbij) := by
      rw [Matrix.submatrix_submatrix]; rfl
    rw [heq, Matrix.det_permute', Matrix.det_permute]
    exact mul_ne_zero (sign_cast_ne_zero _) (mul_ne_zero (sign_cast_ne_zero _) det4_ne_zero)
  have hk3 : ∀ (r c : Fin 3 → Fin 4), Function.Injective r → Function.Injective c →
      (aesMatrix.submatrix r c).det ≠ 0 := by
    intro r c hr hc
    obtain ⟨m, σ, hreq⟩ := factor3 r hr
    obtain ⟨m', τ, hceq⟩ := factor3 c hc
    have heq : aesMatrix.submatrix r c
        = (aesMatrix.submatrix (Fin.succAbove m) (Fin.succAbove m')).submatrix σ τ := by
      rw [hreq, hceq, Matrix.submatrix_submatrix]
    have heq2 : (aesMatrix.submatrix (Fin.succAbove m) (Fin.succAbove m')).submatrix σ τ
        = ((aesMatrix.submatrix (Fin.succAbove m) (Fin.succAbove m')).submatrix σ id).submatrix
            id τ := by
      rw [Matrix.submatrix_submatrix]; rfl
    rw [heq, heq2, Matrix.det_permute', Matrix.det_permute]
    exact mul_ne_zero (sign_cast_ne_zero _)
      (mul_ne_zero (sign_cast_ne_zero _) (minors3_ne_zero m m'))
  intro k r c hr hc
  have hk : k ≤ 4 := by simpa using Fintype.card_le_of_injective r hr
  interval_cases k
  · revert r c hr hc; decide
  · revert r c hr hc; decide
  · revert r c hr hc; decide
  · exact hk3 r c hr hc
  · exact hk4 r c hr hc

theorem aesMatrix_isMDS : IsMDS aesMatrix := by
  intro k Row Col hRow hCol
  exact aesMatrix_isMDS' k _ _
    (fun a b hab => (Row.orderIsoOfFin hRow).injective (Subtype.ext hab))
    (fun a b hab => (Col.orderIsoOfFin hCol).injective (Subtype.ext hab))

/-- AES `MixColumns`: apply `aesMatrix` to each column independently. -/
def aesMixColumns (a : SquareIdx 4 → GF256) : SquareIdx 4 → GF256 :=
  fun i => aesMatrix.mulVec (fun r => a (r, i.2)) i.1

theorem localWeight_sqCol_eq_weight {K : Type*} [Zero K] [DecidableEq K] (ξ : Fin 4)
    (s : SquareIdx 4 → K) : localWeight (sqCol 4) ξ s = weight (fun r => s (r, ξ)) := by
  have himg : (activePattern s).filter (fun i => sqCol 4 i = ξ)
      = (activePattern (fun r => s (r, ξ))).image (fun r => (r, ξ)) := by
    ext ⟨r, c⟩
    simp only [Finset.mem_filter, mem_activePattern, sqCol, Finset.mem_image]
    constructor
    · rintro ⟨hne, rfl⟩; exact ⟨r, hne, rfl⟩
    · rintro ⟨r', hne, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      exact ⟨hne, rfl⟩
  rw [localWeight, himg,
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq .. |>.mp h).1)]
  rfl

theorem aesMixColumns_isColBranchBound : IsColBranchBound (sqCol 4) aesMixColumns 5 := by
  intro a ξ hpos
  rw [localWeight_sqCol_eq_weight, localWeight_sqCol_eq_weight] at hpos ⊢
  have heq : (fun r => aesMixColumns a (r, ξ)) = aesMatrix.mulVec (fun r => a (r, ξ)) := rfl
  rw [heq] at hpos ⊢
  exact isMDS_branch_bound aesMatrix_isMDS (fun r => a (r, ξ)) hpos

theorem aesMixColumns_nondegenerate : NonDegenerate aesMixColumns := by
  intro a ha
  funext ⟨r, c⟩
  have hcol : (fun r' => a (r', c)) = 0 := by
    apply isMDS_injective aesMatrix_isMDS
    rw [Matrix.mulVec_zero]
    funext r'
    exact congrFun ha (r', c)
  exact congrFun hcol r

/-- **25 active S-boxes in four rounds, unconditionally.** `aes_four_round` specialized to the
real `GF(2⁸)` and the real `MixColumns` matrix: no hypothesis about branch number remains, only
the free `PreserveSupport` fact about whichever bijective S-box layer is used. -/
theorem aes_four_round_concrete (sbox : (SquareIdx 4 → GF256) → (SquareIdx 4 → GF256))
    (hsbox : PreserveSupport sbox) {a : SquareIdx 4 → GF256} (ha : a ≠ 0) (n : ℕ) :
    25 ≤ weight ((aesSpec sbox aesMixColumns hsbox aesMixColumns_isColBranchBound
        aesMixColumns_nondegenerate).trail a n)
      + weight ((aesSpec sbox aesMixColumns hsbox aesMixColumns_isColBranchBound
        aesMixColumns_nondegenerate).trail a (n + 1))
      + weight ((aesSpec sbox aesMixColumns hsbox aesMixColumns_isColBranchBound
        aesMixColumns_nondegenerate).trail a (n + 2))
      + weight ((aesSpec sbox aesMixColumns hsbox aesMixColumns_isColBranchBound
        aesMixColumns_nondegenerate).trail a (n + 3)) :=
  aes_four_round sbox aesMixColumns hsbox aesMixColumns_isColBranchBound
    aesMixColumns_nondegenerate ha n

/-- **50 active S-boxes over the ten rounds of AES-128, unconditionally.** -/
theorem aes128_ten_round_concrete (sbox : (SquareIdx 4 → GF256) → (SquareIdx 4 → GF256))
    (hsbox : PreserveSupport sbox) {a : SquareIdx 4 → GF256} (ha : a ≠ 0) :
    50 ≤ (aesSpec sbox aesMixColumns hsbox aesMixColumns_isColBranchBound
      aesMixColumns_nondegenerate).trailWeight a 10 :=
  aes128_ten_round sbox aesMixColumns hsbox aesMixColumns_isColBranchBound
    aesMixColumns_nondegenerate ha
