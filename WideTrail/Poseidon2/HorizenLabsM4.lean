/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.MDS4

/-!
# The HorizenLabs matrix `M4` over an arbitrary field

The HorizenLabs reference implementation of Poseidon2 (`matmul_m4`, crate `zkhash` `0.2.0`
`src/poseidon2/poseidon2.rs:85-117`), barretenberg's `matrix_multiplication_4x4` and Noir's ACVM
solver mix each block of four coordinates with

  `hlMat4 = [[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]]`,

row `i` giving output coordinate `i` (`hlMat4_mulVec`). This is not Plonky3's `MDSMat4`
(`Poseidon2.m4 = circ(2, 3, 1, 1)` of `WideTrail.Algebra.MDS4`). Every entry is the image of an
integer, so whether `hlMat4` is MDS depends only on the characteristic.

This file proves, for every field `K`:

* `hlMat4_isMDS`: if `2, 3, 5, 7, 11, 13, 19, 23` (the list `hlMat4Primes`) are nonzero in `K`,
  every square submatrix of `hlMat4` is nonsingular; `hlMat4_isMDS_iff`: the condition is also
  necessary;
* `hlMat4_isMDS_of_minors`: the same conclusion from the list `hlMat4Minors` of `21` values
  between `1` and `64`; `natAbs_hlMinor_mem` shows that the absolute value of every square minor of
  `hlMat4` over `ℤ` lies in that list. (That every listed value occurs was computed outside Lean
  and is not used.)
* `hlMat4_det`: `det hlMat4 = -64` over every commutative ring;
* `hlMat4Equiv`: if `2 ≠ 0` in `K`, the map `x ↦ hlMat4 x` is a linear equivalence with the
  explicit inverse `y ↦ 8⁻¹ • hlMat4Inv8 y` (`hlMat4_mul_hlMat4Inv8`, `hlMat4Inv8_mul_hlMat4`);
  `hlMat4TEquiv` is the same for the transpose;
* `hlMat4_isBranchBound`, `hlMat4Equiv_isBranchBound`: under the `hlMat4Primes` hypothesis, the
  branch number of `hlMat4` is at least `5`.

The minors are handled as in `WideTrail.Algebra.MDS4`: every minor over `K` is the image of the
integer minor (`det_submatrix_hlMat4`); orders `1` and `2` are enumerated by `decide`, order `3`
reduces to the `16` minors that delete one row and one column, and order `4` is `eval_det`.

What is not claimed: nothing about any concrete field or permutation here; the BN254 instance is
in `WideTrail.Poseidon2.AztecBN254`.
-/

set_option autoImplicit false

namespace Poseidon2

section Ring

variable (R : Type*) [Ring R]

/-- The HorizenLabs `M4`, over any ring; row `i` gives output coordinate `i`. -/
def hlMat4 : Matrix (Fin 4) (Fin 4) R :=
  !![5, 7, 1, 3;
     4, 6, 1, 1;
     1, 3, 5, 7;
     1, 1, 4, 6]

/-- Eight times the inverse of `hlMat4` (`hlMat4_mul_hlMat4Inv8`); it is `-8⁻¹` times the
adjugate, since `det hlMat4 = -64`. -/
def hlMat4Inv8 : Matrix (Fin 4) (Fin 4) R :=
  !![-1, 3, -6, 7;
     1, -1, 4, -5;
     -6, 7, -1, 3;
     4, -5, 1, -1]

/-- `hlMat4` applied to a vector, coordinate by coordinate. -/
theorem hlMat4_mulVec (x : Fin 4 → R) :
    (hlMat4 R).mulVec x = ![5 * x 0 + 7 * x 1 + x 2 + 3 * x 3, 4 * x 0 + 6 * x 1 + x 2 + x 3,
      x 0 + 3 * x 1 + 5 * x 2 + 7 * x 3, x 0 + x 1 + 4 * x 2 + 6 * x 3] := by
  funext i
  fin_cases i <;>
    simp [hlMat4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, add_assoc]

/-- The transpose of `hlMat4` applied to a vector, coordinate by coordinate. -/
theorem hlMat4_transpose_mulVec (x : Fin 4 → R) :
    (hlMat4 R).transpose.mulVec x = ![5 * x 0 + 4 * x 1 + x 2 + x 3,
      7 * x 0 + 6 * x 1 + 3 * x 2 + x 3, x 0 + x 1 + 5 * x 2 + 4 * x 3,
      3 * x 0 + x 1 + 7 * x 2 + 6 * x 3] := by
  funext i
  fin_cases i <;>
    simp [hlMat4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, add_assoc]

/-- The integer matrix `hlMat4`, cast entrywise into `R`, is `hlMat4` over `R`. -/
theorem hlMat4_map : (hlMat4 ℤ).map (fun a => (a : R)) = hlMat4 R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hlMat4]

/-- `hlMat4 * hlMat4Inv8 = 8`, an identity with integer coefficients, so valid in every ring. -/
theorem hlMat4_mul_hlMat4Inv8 :
    hlMat4 R * hlMat4Inv8 R = (8 : R) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlMat4, hlMat4Inv8, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- `hlMat4Inv8 * hlMat4 = 8`, likewise. -/
theorem hlMat4Inv8_mul_hlMat4 :
    hlMat4Inv8 R * hlMat4 R = (8 : R) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hlMat4, hlMat4Inv8, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

end Ring

/-! ### Minors over `ℤ` -/

/-- A list containing the absolute value of every square minor of `hlMat4` over `ℤ`, of every
order `0` to `4` (`natAbs_hlMinor_mem`). -/
def hlMat4Minors : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 11, 15, 19, 23, 24, 27, 32, 35, 39, 40, 48, 56, 64]

/-- The primes dividing some element of `hlMat4Minors`; `13` divides only `39`. -/
def hlMat4Primes : List ℕ := [2, 3, 5, 7, 11, 13, 19, 23]

/-- Every minor of `hlMat4` over a commutative ring `R` is the integer minor, cast into `R`. -/
theorem det_submatrix_hlMat4 {R : Type*} [CommRing R] {k : ℕ} (r c : Fin k → Fin 4) :
    ((hlMat4 R).submatrix r c).det = (((hlMat4 ℤ).submatrix r c).det : R) := by
  rw [Int.cast_det, ← Matrix.submatrix_map, hlMat4_map]

theorem hlMat4_det_int : (hlMat4 ℤ).det = -64 := by
  simp only [hlMat4]
  eval_det

/-- `det hlMat4 = -64` over every commutative ring. -/
theorem hlMat4_det (R : Type*) [CommRing R] : (hlMat4 R).det = -64 := by
  have h := det_submatrix_hlMat4 (R := R) (id : Fin 4 → Fin 4) id
  rw [Matrix.submatrix_id_id, Matrix.submatrix_id_id, hlMat4_det_int] at h
  rw [h]
  push_cast
  rfl

/-- The `16` minors of order `3`, indexed by the deleted row and the deleted column. -/
theorem natAbs_hlMinor3_mem : ∀ m m' : Fin 4,
    ((hlMat4 ℤ).submatrix (Fin.succAbove m) (Fin.succAbove m')).det.natAbs ∈ hlMat4Minors := by
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  decide

/-- **Every square minor of `hlMat4` over `ℤ` has its absolute value in `hlMat4Minors`**, for
any order `k` and any injective choice of `k` rows and `k` columns. -/
theorem natAbs_hlMinor_mem : ∀ (k : ℕ) (r c : Fin k → Fin 4), Function.Injective r →
    Function.Injective c → ((hlMat4 ℤ).submatrix r c).det.natAbs ∈ hlMat4Minors := by
  intro k r c hr hc
  have hk : k ≤ 4 := by simpa using Fintype.card_le_of_injective r hr
  interval_cases k
  · rw [Matrix.det_isEmpty]
    decide
  · revert r c
    simp only [Matrix.det_unique, Matrix.submatrix_apply]
    decide
  · revert r c hr hc
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply]
    decide
  · obtain ⟨m, σ, rfl⟩ := injective_three_four_factor r hr
    obtain ⟨m', τ, rfl⟩ := injective_three_four_factor c hc
    have heq : (hlMat4 ℤ).submatrix (Fin.succAbove m ∘ σ) (Fin.succAbove m' ∘ τ)
        = ((hlMat4 ℤ).submatrix (Fin.succAbove m) (Fin.succAbove m')).submatrix σ τ := by
      rw [Matrix.submatrix_submatrix]
    rw [heq, natAbs_det_submatrix_perm]
    exact natAbs_hlMinor3_mem m m'
  · have hrbij : Function.Bijective r :=
      (Fintype.bijective_iff_injective_and_card r).mpr ⟨hr, rfl⟩
    have hcbij : Function.Bijective c :=
      (Fintype.bijective_iff_injective_and_card c).mpr ⟨hc, rfl⟩
    have heq : (hlMat4 ℤ).submatrix r c = (hlMat4 ℤ).submatrix (Equiv.ofBijective r hrbij)
        (Equiv.ofBijective c hcbij) := rfl
    rw [heq, natAbs_det_submatrix_perm, hlMat4_det_int]
    decide

/-- Each element of `hlMat4Minors` with a factorisation into elements of `hlMat4Primes`. -/
def hlMat4MinorFactors : List (ℕ × List ℕ) :=
  [(1, []), (2, [2]), (3, [3]), (4, [2, 2]), (5, [5]), (6, [2, 3]), (7, [7]), (8, [2, 2, 2]),
    (11, [11]), (15, [3, 5]), (19, [19]), (23, [23]), (24, [2, 2, 2, 3]), (27, [3, 3, 3]),
    (32, [2, 2, 2, 2, 2]), (35, [5, 7]), (39, [3, 13]), (40, [2, 2, 2, 5]),
    (48, [2, 2, 2, 2, 3]), (56, [2, 2, 2, 7]), (64, [2, 2, 2, 2, 2, 2])]

theorem hlMat4MinorFactors_fst : hlMat4MinorFactors.map Prod.fst = hlMat4Minors := by
  decide

theorem hlMat4MinorFactors_spec :
    ∀ e ∈ hlMat4MinorFactors, e.2.prod = e.1 ∧ ∀ p ∈ e.2, p ∈ hlMat4Primes := by
  decide

/-! ### The MDS criterion over a field -/

section Field

variable {K : Type*} [Field K]

/-- A product of naturals, each nonzero in `K`, is nonzero in `K`. -/
theorem natCast_list_prod_ne_zero {l : List ℕ} (h : ∀ p ∈ l, (p : K) ≠ 0) :
    ((l.prod : ℕ) : K) ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, Nat.cast_mul]
    exact mul_ne_zero (h a (by simp)) (ih fun p hp => h p (by simp [hp]))

/-- Over a field, the hypothesis on `hlMat4Primes` gives the hypothesis on `hlMat4Minors`, by the
factorisations `hlMat4MinorFactors`. -/
theorem hlMat4_minors_ne_zero_of_primes (h : ∀ p ∈ hlMat4Primes, (p : K) ≠ 0) :
    ∀ n ∈ hlMat4Minors, (n : K) ≠ 0 := by
  intro n hn
  rw [← hlMat4MinorFactors_fst] at hn
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
  obtain ⟨hprod, hmem⟩ := hlMat4MinorFactors_spec e he
  rw [← hprod]
  exact natCast_list_prod_ne_zero fun p hp => h p (hmem p hp)

/-- **The minor criterion.** If every element of `hlMat4Minors` is nonzero in `K`, then
`hlMat4` is MDS over `K`. -/
theorem hlMat4_isMDS_of_minors (h : ∀ n ∈ hlMat4Minors, (n : K) ≠ 0) : IsMDS (hlMat4 K) := by
  intro k Row Col hRow hCol
  rw [det_submatrix_hlMat4]
  have hmem := natAbs_hlMinor_mem k (fun i => (Row.orderIsoOfFin hRow i : Fin 4))
    (fun j => (Col.orderIsoOfFin hCol j : Fin 4))
    (fun a b hab => (Row.orderIsoOfFin hRow).injective (Subtype.ext hab))
    (fun a b hab => (Col.orderIsoOfFin hCol).injective (Subtype.ext hab))
  generalize ((hlMat4 ℤ).submatrix (fun i => (Row.orderIsoOfFin hRow i : Fin 4))
      (fun j => (Col.orderIsoOfFin hCol j : Fin 4))).det = d at hmem ⊢
  rcases Int.natAbs_eq d with hd | hd
  · rw [hd, Int.cast_natCast]
    exact h _ hmem
  · rw [hd, Int.cast_neg, Int.cast_natCast]
    exact neg_ne_zero.mpr (h _ hmem)

/-- **`hlMat4` is MDS over every field in which `2, 3, 5, 7, 11, 13, 19, 23` are nonzero.** -/
theorem hlMat4_isMDS (h : ∀ p ∈ hlMat4Primes, (p : K) ≠ 0) : IsMDS (hlMat4 K) :=
  hlMat4_isMDS_of_minors (hlMat4_minors_ne_zero_of_primes h)

/-- A minor of `hlMat4` over `K` whose integer value is `d` makes `d` nonzero in `K`, if
`hlMat4` is MDS over `K`. -/
theorem hlMat4_intCast_ne_zero_of_isMDS (hM : IsMDS (hlMat4 K)) {k : ℕ} {r c : Fin k → Fin 4}
    (hr : StrictMono r) (hc : StrictMono c) {d : ℤ} (hd : ((hlMat4 ℤ).submatrix r c).det = d) :
    (d : K) ≠ 0 := by
  have h := det_submatrix_ne_zero_of_isMDS hM hr hc
  rwa [det_submatrix_hlMat4, hd] at h

/-- **The criterion is exact.** `hlMat4` is MDS over `K` if and only if
`2, 3, 5, 7, 11, 13, 19, 23` are all nonzero in `K`. The witnesses are the order-`2` minor `2`
(rows `0, 1`, columns `0, 1`), the entries `3`, `5` and `7`, and the order-`2` minors `-11`,
`39 = 3 * 13`, `19` and `23`. -/
theorem hlMat4_isMDS_iff : IsMDS (hlMat4 K) ↔ ∀ p ∈ hlMat4Primes, (p : K) ≠ 0 := by
  refine ⟨fun hM => ?_, hlMat4_isMDS⟩
  have h1 : ∀ i : Fin 4, StrictMono (fun _ : Fin 1 => i) := fun _ => Subsingleton.strictMono _
  have h2 : ∀ a b : Fin 4, a < b → StrictMono ![a, b] := fun a b hab =>
    Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; exact hab)
  intro p hp
  simp only [hlMat4Primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact_mod_cast hlMat4_intCast_ne_zero_of_isMDS hM (h2 0 1 (by decide)) (h2 0 1 (by decide))
      (d := 2) (by rw [Matrix.det_fin_two]; decide)
  · exact_mod_cast hlMat4_intCast_ne_zero_of_isMDS hM (h1 0) (h1 3) (d := 3)
      (by rw [Matrix.det_unique]; decide)
  · exact_mod_cast hlMat4_intCast_ne_zero_of_isMDS hM (h1 0) (h1 0) (d := 5)
      (by rw [Matrix.det_unique]; decide)
  · exact_mod_cast hlMat4_intCast_ne_zero_of_isMDS hM (h1 0) (h1 1) (d := 7)
      (by rw [Matrix.det_unique]; decide)
  · have h := hlMat4_intCast_ne_zero_of_isMDS (K := K) hM (h2 0 1 (by decide))
      (h2 1 3 (by decide)) (d := -11) (by rw [Matrix.det_fin_two]; decide)
    rw [Int.cast_neg, neg_ne_zero] at h
    exact_mod_cast h
  · have h := hlMat4_intCast_ne_zero_of_isMDS (K := K) hM (h2 0 3 (by decide))
      (h2 1 3 (by decide)) (d := 39) (by rw [Matrix.det_fin_two]; decide)
    intro h13
    apply h
    rw [show ((39 : ℤ) : K) = 3 * ((13 : ℕ) : K) by push_cast; norm_num, h13, mul_zero]
  · exact_mod_cast hlMat4_intCast_ne_zero_of_isMDS hM (h2 0 3 (by decide)) (h2 0 2 (by decide))
      (d := 19) (by rw [Matrix.det_fin_two]; decide)
  · exact_mod_cast hlMat4_intCast_ne_zero_of_isMDS hM (h2 1 3 (by decide)) (h2 0 3 (by decide))
      (d := 23) (by rw [Matrix.det_fin_two]; decide)

/-! ### `hlMat4` as a linear equivalence -/

/-- Multiplication by a square matrix `A` as a linear equivalence, given a matrix `N` and a
nonzero `c` with `A * N = c • 1` and `N * A = c • 1`; the inverse is `y ↦ c⁻¹ • N y`. -/
def mulVecEquivOfMulEqSmul {n : ℕ} (A N : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0)
    (hAN : A * N = c • (1 : Matrix (Fin n) (Fin n) K))
    (hNA : N * A = c • (1 : Matrix (Fin n) (Fin n) K)) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  { Matrix.mulVecLin A with
    invFun := fun y => c⁻¹ • N.mulVec y
    left_inv := fun x => by
      change c⁻¹ • N.mulVec (A.mulVec x) = x
      rw [Matrix.mulVec_mulVec, hNA, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
    right_inv := fun y => by
      change A.mulVec (c⁻¹ • N.mulVec y) = y
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hAN, Matrix.smul_mulVec, Matrix.one_mulVec,
        smul_smul, inv_mul_cancel₀ hc, one_smul] }

theorem mulVecEquivOfMulEqSmul_apply {n : ℕ} (A N : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) (hAN : A * N = c • (1 : Matrix (Fin n) (Fin n) K))
    (hNA : N * A = c • (1 : Matrix (Fin n) (Fin n) K)) (x : Fin n → K) :
    mulVecEquivOfMulEqSmul A N hc hAN hNA x = A.mulVec x :=
  rfl

theorem mulVecEquivOfMulEqSmul_symm_apply {n : ℕ} (A N : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) (hAN : A * N = c • (1 : Matrix (Fin n) (Fin n) K))
    (hNA : N * A = c • (1 : Matrix (Fin n) (Fin n) K)) (y : Fin n → K) :
    (mulVecEquivOfMulEqSmul A N hc hAN hNA).symm y = c⁻¹ • N.mulVec y :=
  rfl

/-- `8 ≠ 0` in `K` when `2 ≠ 0`. -/
theorem eight_ne_zero_of_two_ne_zero (h2 : (2 : K) ≠ 0) : (8 : K) ≠ 0 := by
  rw [show (8 : K) = 2 * 2 * 2 by norm_num]
  exact mul_ne_zero (mul_ne_zero h2 h2) h2

variable (K) in
/-- **`hlMat4` as a linear equivalence, with an explicit inverse.** Under `2 ≠ 0`, the inverse
is `y ↦ 8⁻¹ • hlMat4Inv8 y` (`hlMat4Equiv_symm_apply`). -/
def hlMat4Equiv (h2 : (2 : K) ≠ 0) : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) :=
  mulVecEquivOfMulEqSmul (hlMat4 K) (hlMat4Inv8 K) (eight_ne_zero_of_two_ne_zero h2)
    (hlMat4_mul_hlMat4Inv8 K) (hlMat4Inv8_mul_hlMat4 K)

theorem hlMat4Equiv_apply (h2 : (2 : K) ≠ 0) (x : Fin 4 → K) :
    hlMat4Equiv K h2 x = (hlMat4 K).mulVec x :=
  rfl

theorem hlMat4Equiv_symm_apply (h2 : (2 : K) ≠ 0) (y : Fin 4 → K) :
    (hlMat4Equiv K h2).symm y = (8 : K)⁻¹ • (hlMat4Inv8 K).mulVec y :=
  rfl

variable (K) in
/-- The transpose of `hlMat4` as a linear equivalence, with the inverse
`y ↦ 8⁻¹ • (hlMat4Inv8)ᵀ y`. It reads the rows of `hlMat4` as columns. -/
def hlMat4TEquiv (h2 : (2 : K) ≠ 0) : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) :=
  mulVecEquivOfMulEqSmul (hlMat4 K).transpose (hlMat4Inv8 K).transpose
    (eight_ne_zero_of_two_ne_zero h2)
    (by rw [← Matrix.transpose_mul, hlMat4Inv8_mul_hlMat4, Matrix.transpose_smul,
      Matrix.transpose_one])
    (by rw [← Matrix.transpose_mul, hlMat4_mul_hlMat4Inv8, Matrix.transpose_smul,
      Matrix.transpose_one])

theorem hlMat4TEquiv_apply (h2 : (2 : K) ≠ 0) (x : Fin 4 → K) :
    hlMat4TEquiv K h2 x = (hlMat4 K).transpose.mulVec x :=
  rfl

/-! ### Branch number -/

variable [DecidableEq K]

/-- **`hlMat4` has branch number at least `5`** over every field in which
`2, 3, 5, 7, 11, 13, 19, 23` are nonzero: every nonzero `x` has at least `5` nonzero coordinates
in `x` and `hlMat4 x` together. -/
theorem hlMat4_isBranchBound (h : ∀ p ∈ hlMat4Primes, (p : K) ≠ 0) :
    isBranchBound id (hlMat4 K).mulVec 5 := by
  intro a ha
  rw [colWeight_id, colWeight_id]
  have hpos : 0 < weight a := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact Finset.card_pos.mpr ⟨i, mem_activePattern.mpr hi⟩
  exact isMDS_branch_bound (hlMat4_isMDS h) a (by omega)

/-- The same bound for the linear equivalence `hlMat4Equiv`. -/
theorem hlMat4Equiv_isBranchBound (h : ∀ p ∈ hlMat4Primes, (p : K) ≠ 0) (h2 : (2 : K) ≠ 0) :
    isBranchBound id (hlMat4Equiv K h2) 5 :=
  hlMat4_isBranchBound h

end Field

end Poseidon2
