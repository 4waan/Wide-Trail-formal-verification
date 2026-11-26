/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.MDS4
import WideTrail.Algebra.BlockCirculant
import WideTrail.Algebra.DiagPlusOnes
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Transposes of the Poseidon2 linear layers

In linear (correlation) cryptanalysis a mask is carried through a linear map `x ↦ A x` by the
transpose: an output mask `v` corresponds to the input mask `Aᵀ v`. The linear branch number of
`A` is therefore the differential branch number of `Aᵀ`, that is, the best `b` with
`isBranchBound id (Aᵀ *ᵥ ·) b`. This identification is the standard definition (Daemen and
Rijmen); correlations are not formalised in this library, so it is used here as a definition,
not proved.

This file proves:

* `IsMDS.transpose`, `isMDS_transpose_iff`: a square matrix is MDS exactly when its transpose
  is. Every square submatrix of `Mᵀ` is the transpose of a square submatrix of `M` (rows and
  columns exchanged), and has the same determinant.
* `Poseidon2.m4_transpose`: the transpose of Plonky3's `MDSMat4`, `m4 = circ(2, 3, 1, 1)`, is
  `circ(2, 1, 1, 3)`. `Poseidon2.m4_transpose_isMDS_iff`: it is MDS under exactly the
  hypothesis that makes `m4` MDS, that `2, 3, 5, 7, 11, 17` (`m4Primes`) are nonzero in `K`;
  `Poseidon2.m4_transpose_isBranchBound`: it then has branch number at least `5`.
* `mulVec_dotProduct_transpose`: `(A x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ y)`.
* `BlockCirculant.blockMix_dotProduct`: if `N` and `N'` are adjoint for `dotProduct`, so are
  `blockMix N` and `blockMix N'`. With `N = A` and `N' = Aᵀ`
  (`BlockCirculant.blockMix_mulVecLin_dotProduct`) this says that the transpose of
  `circ(2A, A, …, A)` is `circ(2Aᵀ, Aᵀ, …, Aᵀ)`; `BlockCirculant.blockMix_conj_dotProduct`
  states the same after relabelling coordinates.
* `Poseidon2.blockMix_m4_sixteen_dotProduct`: on a flat state `Fin 16 → K` with blocks of four
  consecutive coordinates, the transpose of `circ(2 m4, m4, m4, m4)` is
  `circ(2 m4ᵀ, m4ᵀ, m4ᵀ, m4ᵀ)`. The left-hand map is the external layer of
  `WideTrail.Poseidon2.Plonky3` (`Poseidon2.Plonky3.external_apply`).
  `Poseidon2.isBranchBound_blockMix_m4_transpose_sixteen`: under the `m4Primes` hypothesis the
  transposed layer has branch number at least `8`.
* `Poseidon2.diagPlusOnes_isSymm`, `Poseidon2.toLin'_transpose_diagPlusOnes`: the internal
  matrix `c • (diag d + J)` is symmetric, so the map of its transpose is `diagPlusOnes c d`
  itself. `Poseidon2.diagPlusOnes_dotProduct` (`WideTrail.Algebra.DiagPlusOnes`) states the same
  fact as self-adjointness for `dotProduct`.

## Conclusion

Read with the definition above, the lower bounds this library proves for the differential branch
numbers of the width-sixteen Plonky3 linear layers (SP1's KoalaBear and BabyBear instances,
`WideTrail.Poseidon2.Plonky3`) also hold for their linear branch numbers, under the same
hypotheses: `5` for `M4`, `8` for the external layer. The internal layer `c • (diag d + J)` is its
own transpose, so every statement about it as a linear map (its branch number, and the inactive
spaces `Hades.inactiveSpace` of `WideTrail.Hades`) applies unchanged to the map that carries
masks.

## What is not claimed

No correlation, linear trail, linear hull or linear-attack bound is proved here, and nothing is
said about the correlations of any S-box. The branch numbers are lower bounds; they are not shown
to be attained. How masks propagate through whole rounds, and the identification of the linear
branch number with the differential branch number of the transpose, are not formalised.
-/

set_option autoImplicit false

open Matrix

/-! ### MDS matrices and their transposes -/

section MDS

variable {K : Type*} [Field K] {n : ℕ}

/-- **The transpose of an MDS matrix is MDS.** The square submatrix of `Mᵀ` on rows `Row` and
columns `Col` is the transpose of the square submatrix of `M` on rows `Col` and columns `Row`,
and has the same determinant. -/
theorem IsMDS.transpose {M : Matrix (Fin n) (Fin n) K} (hM : IsMDS M) : IsMDS Mᵀ := by
  intro k Row Col hRow hCol
  rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
  exact hM k Col Row hCol hRow

/-- A square matrix is MDS exactly when its transpose is. -/
theorem isMDS_transpose_iff {M : Matrix (Fin n) (Fin n) K} : IsMDS Mᵀ ↔ IsMDS M :=
  ⟨fun h => by simpa using h.transpose, IsMDS.transpose⟩

/-- **`A` and `Aᵀ` are adjoint for `dotProduct`:** `(A x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ y)`. -/
theorem mulVec_dotProduct_transpose {m : Type*} [Fintype m] (A : Matrix m m K) (x y : m → K) :
    A *ᵥ x ⬝ᵥ y = x ⬝ᵥ Aᵀ *ᵥ y := by
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

end MDS

/-! ### `MDSMat4` -/

namespace Poseidon2

/-- **The transpose of `m4 = circ(2, 3, 1, 1)` is `circ(2, 1, 1, 3)`**, over any ring. -/
theorem m4_transpose (R : Type*) [Ring R] :
    (m4 R)ᵀ = !![2, 1, 1, 3;
                 3, 2, 1, 1;
                 1, 3, 2, 1;
                 1, 1, 3, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable {K : Type*} [Field K]

/-- `m4ᵀ` is MDS over every field in which `2, 3, 5, 7, 11, 17` are nonzero. -/
theorem m4_transpose_isMDS (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) : IsMDS (m4 K)ᵀ :=
  (m4_isMDS h).transpose

/-- **The criterion for `m4ᵀ` is the criterion for `m4`.** `m4ᵀ` is MDS over `K` if and only if
`2, 3, 5, 7, 11, 17` are all nonzero in `K` (`m4_isMDS_iff`). -/
theorem m4_transpose_isMDS_iff : IsMDS (m4 K)ᵀ ↔ ∀ p ∈ m4Primes, (p : K) ≠ 0 :=
  isMDS_transpose_iff.trans m4_isMDS_iff

/-- Under the `m4Primes` hypothesis, `m4ᵀ` has branch number at least `5`, the bound
`m4_isBranchBound` gives for `m4`. -/
theorem m4_transpose_isBranchBound [DecidableEq K] (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) :
    isBranchBound id (m4 K)ᵀ.mulVec 5 := by
  intro a ha
  rw [colWeight_id, colWeight_id]
  have hpos : 0 < weight a := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact Finset.card_pos.mpr ⟨i, mem_activePattern.mpr hi⟩
  exact isMDS_branch_bound (m4_transpose_isMDS h) a (by omega)

end Poseidon2

/-! ### Block-circulant layers -/

namespace BlockCirculant

variable {B P K : Type*} [Fintype B] [Fintype P] [Field K]

/-- The dot product of two states is the sum of the dot products of their blocks. -/
theorem dotProduct_eq_sum_block (x y : B × P → K) :
    x ⬝ᵥ y = ∑ i, block x i ⬝ᵥ block y i := by
  simp only [dotProduct, Fintype.sum_prod_type]
  rfl

/-- **The adjoint of a block-circulant layer is block-circulant.** If `N u ⬝ᵥ v = u ⬝ᵥ N' v` for
all `u, v`, then `blockMix N x ⬝ᵥ y = x ⬝ᵥ blockMix N' y` for all states `x, y`. Both sides equal
`∑ᵢ xᵢ ⬝ᵥ N' yᵢ + (∑ᵢ xᵢ) ⬝ᵥ N' (∑ᵢ yᵢ)`. -/
theorem blockMix_dotProduct {N N' : (P → K) →ₗ[K] (P → K)}
    (hN : ∀ u v, N u ⬝ᵥ v = u ⬝ᵥ N' v) (x y : B × P → K) :
    blockMix N x ⬝ᵥ y = x ⬝ᵥ blockMix N' y := by
  rw [dotProduct_eq_sum_block, dotProduct_eq_sum_block]
  simp only [block_blockMix, hN, add_dotProduct, dotProduct_add, map_add, Finset.sum_add_distrib]
  congr 1
  rw [← dotProduct_sum, ← sum_dotProduct, ← map_sum, ← blockSum_eq_sum, ← blockSum_eq_sum]

/-- **The transpose of `circ(2A, A, …, A)` is `circ(2Aᵀ, Aᵀ, …, Aᵀ)`**, as a statement about
`dotProduct`. -/
theorem blockMix_mulVecLin_dotProduct (A : Matrix P P K) (x y : B × P → K) :
    blockMix (Matrix.mulVecLin A) x ⬝ᵥ y = x ⬝ᵥ blockMix (Matrix.mulVecLin Aᵀ) y :=
  blockMix_dotProduct (fun u v => mulVec_dotProduct_transpose A u v) x y

/-- `blockMix_dotProduct` after relabelling the coordinates along `e : B × P ≃ Idx`, the form in
which a block-circulant layer acts on a flat state. -/
theorem blockMix_conj_dotProduct {Idx : Type*} [Fintype Idx] (e : B × P ≃ Idx)
    {N N' : (P → K) →ₗ[K] (P → K)} (hN : ∀ u v, N u ⬝ᵥ v = u ⬝ᵥ N' v) (x y : Idx → K) :
    (blockMix N (x ∘ e) ∘ e.symm) ⬝ᵥ y = x ⬝ᵥ (blockMix N' (y ∘ e) ∘ e.symm) := by
  rw [comp_equiv_symm_dotProduct, dotProduct_comp_equiv_symm, blockMix_dotProduct hN]

end BlockCirculant

/-! ### The Poseidon2 layers at width sixteen -/

namespace Poseidon2

open BlockCirculant

variable {K : Type*} [Field K]

/-- **The transpose of the width-sixteen external layer.** On a flat state whose block `i` is
coordinates `4 i, …, 4 i + 3`, the transpose of `circ(2 m4, m4, m4, m4)` is
`circ(2 m4ᵀ, m4ᵀ, m4ᵀ, m4ᵀ)`. The left-hand map is `Poseidon2.Plonky3.external h35`
(`Poseidon2.Plonky3.external_apply`). -/
theorem blockMix_m4_sixteen_dotProduct (x y : Fin 16 → K) :
    (blockMix (B := Fin 4) (Matrix.mulVecLin (m4 K))
        (x ∘ (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16)) ∘
          (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm) ⬝ᵥ y =
      x ⬝ᵥ (blockMix (B := Fin 4) (Matrix.mulVecLin (m4 K)ᵀ)
        (y ∘ (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16)) ∘
          (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm) :=
  blockMix_conj_dotProduct _ (fun u v => mulVec_dotProduct_transpose (m4 K) u v) x y

/-- **Branch number `8` for the transposed external layer.** Under the `m4Primes` hypothesis,
`circ(2 m4ᵀ, m4ᵀ, m4ᵀ, m4ᵀ)` on a flat state has branch number at least `8`: `m4ᵀ` has branch
number at least `5` (`m4_transpose_isBranchBound`) and `1, …, 5` are nonzero
(`m4_natCast_ne_zero_of_le_five`), so `BlockCirculant.isBranchBound_blockMix_sixteen` applies. The
bound is the one `Poseidon2.Plonky3.external_isBranchBound` gives for the external layer itself. -/
theorem isBranchBound_blockMix_m4_transpose_sixteen [DecidableEq K]
    (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) :
    isBranchBound id
      (fun y : Fin 16 → K =>
        blockMix (B := Fin 4) (Matrix.mulVecLin (m4 K)ᵀ)
          (y ∘ (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16)) ∘
          (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm) 8 :=
  isBranchBound_blockMix_sixteen (m4_transpose_isBranchBound h) (m4_natCast_ne_zero_of_le_five h)

/-- **The internal matrix is symmetric.** `(c • (diag d + J))ᵀ = c • (diag d + J)`, with `J` the
all-ones matrix, over any commutative ring and any index type. -/
theorem diagPlusOnes_isSymm {R Idx : Type*} [CommRing R] [DecidableEq Idx] (c : R)
    (d : Idx → R) : (c • (Matrix.diagonal d + Matrix.of fun _ _ => (1 : R))).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_add, Matrix.diagonal_transpose]
  rfl

/-- **The internal layer is its own transpose.** The map of the transposed matrix
`(c • (diag d + J))ᵀ` is `diagPlusOnes c d`. -/
theorem toLin'_transpose_diagPlusOnes {R Idx : Type*} [CommRing R] [Fintype Idx]
    [DecidableEq Idx] (c : R) (d : Idx → R) :
    Matrix.toLin' (c • (Matrix.diagonal d + Matrix.of fun _ _ => (1 : R)))ᵀ =
      diagPlusOnes c d := by
  rw [(diagPlusOnes_isSymm c d).eq, diagPlusOnes_eq_toLin']

end Poseidon2
