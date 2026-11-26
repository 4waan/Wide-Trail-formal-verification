/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.MDS
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormDet

/-!
# The Plonky3 `MDSMat4` matrix over an arbitrary field

Plonky3's `Poseidon2ExternalMatrixGeneral` mixes each block of four coordinates with
`MDSMat4`. Its source comments give the four output coordinates as

  `x0' = 2 x0 + 3 x1 + x2 + x3`, `x1' = x0 + 2 x1 + 3 x2 + x3`,
  `x2' = x0 + x1 + 2 x2 + 3 x3`, `x3' = 3 x0 + x1 + x2 + 2 x3`,

so the matrix is the circulant `m4 = circ(2, 3, 1, 1)` (`m4_mulVec`). The AES
`MixColumns` matrix (`WideTrail.Algebra.AESMix`) has the same pattern, but there `2` and `3`
denote the elements `x` and `x + 1` of `GF(2⁸)`. Here every entry is the image of an
integer in `K`, so whether `m4` is MDS depends only on the characteristic of `K`.

This file proves, for every field `K`:

* `m4_isMDS`: if `2, 3, 5, 7, 11, 17` (the list `m4Primes`) are nonzero in `K`, every
  square submatrix of `m4` is nonsingular;
* `m4_isMDS_iff`: that condition is also necessary, so `m4` is MDS over `K` exactly when
  the characteristic of `K` is none of these six primes;
* `m4_isMDS_of_minors`: the same conclusion from the list `m4Minors` of the ten distinct
  absolute values `1, 2, 3, 4, 5, 7, 8, 11, 17, 35` of the `69` square minors of `m4`
  over `ℤ`; `mem_m4Minors_iff` shows that this list is exactly that set of values;
* `m4Equiv`: if `35 ≠ 0` in `K`, the map `x ↦ m4 x` is a linear equivalence whose inverse
  is the explicit `y ↦ (-35)⁻¹ • m4Adj y`, and `m4Equiv_symm_apply_eq` identifies this with
  `det⁻¹ • adjugate`, since `det m4 = -35` (`m4_det`) and `adjugate m4 = m4Adj`
  (`m4_adjugate`);
* `m4_isBranchBound`, `m4Equiv_isBranchBound`: under the `m4Primes` hypothesis, the branch
  number of `m4` is at least `5`, through `isMDS_branch_bound`.

Every minor over `K` is the image of the corresponding integer minor
(`det_submatrix_m4`), so the work is a finite computation over `ℤ`, done as in
`WideTrail.Algebra.AESMix`: orders `1` and `2` by `decide` over all injective index maps,
order `3` by reduction to the `16` minors obtained by deleting one row and one column
(`Fin.succAbove`), order `4` by `eval_det`.

The branch-bound corollary is proved here from `isMDS_branch_bound` rather than through
`Hades.branch_of_mds`, so that this file does not import the `Hades` layer.

What is not claimed: nothing is said about the full Poseidon2 external layer, which is the
block circulant `circ(2 M4, M4, …, M4)` and is not MDS (see
`WideTrail.Algebra.BlockCirculant`), nor about any concrete field; the instances for
the KoalaBear and BabyBear primes are in `WideTrail.Algebra.Checks.MDS4`. The HorizenLabs
reference implementation uses a different `4 × 4` matrix,
`[[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]]` (`apply_hl_mat4`); nothing here
is about that matrix.
-/

set_option autoImplicit false

namespace Poseidon2

section Ring

variable (R : Type*) [Ring R]

/-- Plonky3's `MDSMat4`: the circulant `circ(2, 3, 1, 1)`, over any ring. -/
def m4 : Matrix (Fin 4) (Fin 4) R :=
  !![2, 3, 1, 1;
     1, 2, 3, 1;
     1, 1, 2, 3;
     3, 1, 1, 2]

/-- The adjugate of `m4` (`m4_adjugate`), written out: the circulant
`circ(4, -3, 11, -17)`. -/
def m4Adj : Matrix (Fin 4) (Fin 4) R :=
  !![4, -3, 11, -17;
     -17, 4, -3, 11;
     11, -17, 4, -3;
     -3, 11, -17, 4]

/-- `m4` applied to a vector, coordinate by coordinate, as in the Plonky3 source comments. -/
theorem m4_mulVec (x : Fin 4 → R) :
    (m4 R).mulVec x = ![2 * x 0 + 3 * x 1 + x 2 + x 3, x 0 + 2 * x 1 + 3 * x 2 + x 3,
      x 0 + x 1 + 2 * x 2 + 3 * x 3, 3 * x 0 + x 1 + x 2 + 2 * x 3] := by
  funext i
  fin_cases i <;>
    simp [m4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, add_assoc]

/-- The integer matrix `m4`, cast entrywise into `R`, is `m4` over `R`. -/
theorem m4_map : (m4 ℤ).map (fun a => (a : R)) = m4 R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m4]

theorem m4Adj_map : (m4Adj ℤ).map (fun a => (a : R)) = m4Adj R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m4Adj]

/-- `m4 * m4Adj = -35`, an identity with integer coefficients, so valid in every ring. -/
theorem m4_mul_m4Adj : m4 R * m4Adj R = (-35 : R) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4, m4Adj, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- `m4Adj * m4 = -35`, likewise. -/
theorem m4Adj_mul_m4 : m4Adj R * m4 R = (-35 : R) • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4, m4Adj, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

end Ring

/-! ### Minors over `ℤ` -/

/-- The distinct absolute values of the square minors of `m4` over `ℤ`, of every order
`1` to `4`. The order-`0` minor is `1` as well. -/
def m4Minors : List ℕ := [1, 2, 3, 4, 5, 7, 8, 11, 17, 35]

/-- The primes dividing some element of `m4Minors`: `4 = 2 * 2`, `8 = 2 * 2 * 2` and
`35 = 5 * 7`, and the remaining entries are `1` or prime. -/
def m4Primes : List ℕ := [2, 3, 5, 7, 11, 17]

/-- Every minor of `m4` over a commutative ring `R` is the integer minor, cast into `R`. -/
theorem det_submatrix_m4 {R : Type*} [CommRing R] {k : ℕ} (r c : Fin k → Fin 4) :
    ((m4 R).submatrix r c).det = (((m4 ℤ).submatrix r c).det : R) := by
  rw [Int.cast_det, ← Matrix.submatrix_map, m4_map]

theorem m4_det_int : (m4 ℤ).det = -35 := by
  simp only [m4]
  eval_det

/-- `det m4 = -35` over every commutative ring. -/
theorem m4_det (R : Type*) [CommRing R] : (m4 R).det = -35 := by
  have h := det_submatrix_m4 (R := R) (id : Fin 4 → Fin 4) id
  rw [Matrix.submatrix_id_id, Matrix.submatrix_id_id, m4_det_int] at h
  rw [h]
  push_cast
  rfl

/-- Permuting the rows and the columns of an integer matrix leaves the absolute value of
its determinant unchanged. -/
theorem natAbs_det_submatrix_perm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ)
    (σ τ : Equiv.Perm (Fin k)) : (A.submatrix σ τ).det.natAbs = A.det.natAbs := by
  have heq : A.submatrix σ τ = (A.submatrix σ id).submatrix id τ := by
    rw [Matrix.submatrix_submatrix]
    rfl
  rw [heq, Matrix.det_permute', Matrix.det_permute]
  simp [Int.natAbs_mul]

/-- Every injective `Fin 3 → Fin 4` is the embedding omitting some `m`, composed with a
permutation of `Fin 3`. -/
theorem injective_three_four_factor : ∀ r : Fin 3 → Fin 4, Function.Injective r →
    ∃ (m : Fin 4) (σ : Equiv.Perm (Fin 3)), r = Fin.succAbove m ∘ σ := by
  decide

/-- The `16` minors of order `3`, indexed by the deleted row and the deleted column. Their
values are `3`, `4`, `11` and `17`. -/
theorem natAbs_minor3_mem : ∀ m m' : Fin 4,
    ((m4 ℤ).submatrix (Fin.succAbove m) (Fin.succAbove m')).det.natAbs ∈ m4Minors := by
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  decide

/-- **Every square minor of `m4` over `ℤ` has its absolute value in `m4Minors`**, for any
order `k` and any injective choice of `k` rows and `k` columns. -/
theorem natAbs_minor_mem : ∀ (k : ℕ) (r c : Fin k → Fin 4), Function.Injective r →
    Function.Injective c → ((m4 ℤ).submatrix r c).det.natAbs ∈ m4Minors := by
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
    have heq : (m4 ℤ).submatrix (Fin.succAbove m ∘ σ) (Fin.succAbove m' ∘ τ)
        = ((m4 ℤ).submatrix (Fin.succAbove m) (Fin.succAbove m')).submatrix σ τ := by
      rw [Matrix.submatrix_submatrix]
    rw [heq, natAbs_det_submatrix_perm]
    exact natAbs_minor3_mem m m'
  · have hrbij : Function.Bijective r :=
      (Fintype.bijective_iff_injective_and_card r).mpr ⟨hr, rfl⟩
    have hcbij : Function.Bijective c :=
      (Fintype.bijective_iff_injective_and_card c).mpr ⟨hc, rfl⟩
    have heq : (m4 ℤ).submatrix r c = (m4 ℤ).submatrix (Equiv.ofBijective r hrbij)
        (Equiv.ofBijective c hcbij) := rfl
    rw [heq, natAbs_det_submatrix_perm, m4_det_int]
    decide

/-- Every element of `m4Minors` is the absolute value of some square minor of `m4`, with
rows and columns listed in increasing order. -/
theorem exists_minor_of_mem : ∀ n ∈ m4Minors, ∃ (k : ℕ) (r c : Fin k → Fin 4),
    StrictMono r ∧ StrictMono c ∧ ((m4 ℤ).submatrix r c).det.natAbs = n := by
  have key : ∀ {k : ℕ} (r c : Fin k → Fin 4), StrictMono r → StrictMono c → ∀ n : ℕ,
      ((m4 ℤ).submatrix r c).det.natAbs = n → ∃ (k : ℕ) (r c : Fin k → Fin 4),
        StrictMono r ∧ StrictMono c ∧ ((m4 ℤ).submatrix r c).det.natAbs = n :=
    fun r c hr hc _ hn => ⟨_, r, c, hr, hc, hn⟩
  have h2 : ∀ a b : Fin 4, a < b → StrictMono ![a, b] := fun a b hab =>
    Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; exact hab)
  intro n hn
  simp only [m4Minors, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key (fun _ : Fin 1 => 0) (fun _ => 2) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _) 1 (by rw [Matrix.det_unique]; decide)
  · exact key (fun _ : Fin 1 => 0) (fun _ => 0) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _) 2 (by rw [Matrix.det_unique]; decide)
  · exact key (fun _ : Fin 1 => 0) (fun _ => 1) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _) 3 (by rw [Matrix.det_unique]; decide)
  · exact key _ _ (Fin.strictMono_succAbove 0) (Fin.strictMono_succAbove 0) 4
      (by rw [Matrix.det_fin_three]; decide)
  · exact key _ _ (h2 0 1 (by decide)) (h2 0 2 (by decide)) 5
      (by rw [Matrix.det_fin_two]; decide)
  · exact key _ _ (h2 0 1 (by decide)) (h2 1 2 (by decide)) 7
      (by rw [Matrix.det_fin_two]; decide)
  · exact key _ _ (h2 0 2 (by decide)) (h2 1 3 (by decide)) 8
      (by rw [Matrix.det_fin_two]; decide)
  · exact key _ _ (Fin.strictMono_succAbove 0) (Fin.strictMono_succAbove 2) 11
      (by rw [Matrix.det_fin_three]; decide)
  · exact key _ _ (Fin.strictMono_succAbove 0) (Fin.strictMono_succAbove 1) 17
      (by rw [Matrix.det_fin_three]; decide)
  · exact key id id strictMono_id strictMono_id 35
      (by rw [Matrix.submatrix_id_id, m4_det_int]; decide)

/-- **`m4Minors` is exactly the set of absolute values of the square minors of `m4`** over
`ℤ`, of orders `0` to `4`. -/
theorem mem_m4Minors_iff (n : ℕ) : n ∈ m4Minors ↔ ∃ (k : ℕ) (r c : Fin k → Fin 4),
    StrictMono r ∧ StrictMono c ∧ ((m4 ℤ).submatrix r c).det.natAbs = n := by
  constructor
  · exact exists_minor_of_mem n
  · rintro ⟨k, r, c, hr, hc, rfl⟩
    exact natAbs_minor_mem k r c hr.injective hc.injective

/-! ### The MDS criterion over a field -/

section Field

variable {K : Type*} [Field K]

/-- Over a field, the hypothesis on `m4Primes` gives the hypothesis on `m4Minors`, since
`4`, `8` and `35` factor into elements of `m4Primes`. -/
theorem minors_ne_zero_of_primes (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) :
    ∀ n ∈ m4Minors, (n : K) ≠ 0 := by
  have hp : ∀ p ∈ m4Primes, (p : K) ≠ 0 := h
  simp only [m4Primes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hp
  obtain ⟨h2, h3, h5, h7, h11, h17⟩ := hp
  intro n hn
  simp only [m4Minors, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact h2
  · exact h3
  · rw [show ((4 : ℕ) : K) = (2 : ℕ) * (2 : ℕ) by norm_num]
    exact mul_ne_zero h2 h2
  · exact h5
  · exact h7
  · rw [show ((8 : ℕ) : K) = (2 : ℕ) * (2 : ℕ) * (2 : ℕ) by norm_num]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  · exact h11
  · exact h17
  · rw [show ((35 : ℕ) : K) = (5 : ℕ) * (7 : ℕ) by norm_num]
    exact mul_ne_zero h5 h7

/-- Conversely, every element of `m4Primes` occurs in `m4Minors`, so the two hypotheses are
equivalent. -/
theorem primes_ne_zero_of_minors (h : ∀ n ∈ m4Minors, (n : K) ≠ 0) :
    ∀ p ∈ m4Primes, (p : K) ≠ 0 :=
  fun p hp => h p (by revert p; decide)

/-- `35 ≠ 0` in `K`, the hypothesis of `m4Equiv`, follows from the `m4Primes` hypothesis. -/
theorem thirtyFive_ne_zero_of_primes (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) : (35 : K) ≠ 0 := by
  have h35 := minors_ne_zero_of_primes h 35 (by decide)
  exact_mod_cast h35

/-- **The minor criterion.** If every element of `m4Minors` is nonzero in `K`, then `m4`
is MDS over `K`: each minor over `K` is `±n` for some `n ∈ m4Minors` (`natAbs_minor_mem`,
`det_submatrix_m4`). -/
theorem m4_isMDS_of_minors (h : ∀ n ∈ m4Minors, (n : K) ≠ 0) : IsMDS (m4 K) := by
  intro k Row Col hRow hCol
  rw [det_submatrix_m4]
  have hmem := natAbs_minor_mem k (fun i => (Row.orderIsoOfFin hRow i : Fin 4))
    (fun j => (Col.orderIsoOfFin hCol j : Fin 4))
    (fun a b hab => (Row.orderIsoOfFin hRow).injective (Subtype.ext hab))
    (fun a b hab => (Col.orderIsoOfFin hCol).injective (Subtype.ext hab))
  generalize ((m4 ℤ).submatrix (fun i => (Row.orderIsoOfFin hRow i : Fin 4))
      (fun j => (Col.orderIsoOfFin hCol j : Fin 4))).det = d at hmem ⊢
  rcases Int.natAbs_eq d with hd | hd
  · rw [hd, Int.cast_natCast]
    exact h _ hmem
  · rw [hd, Int.cast_neg, Int.cast_natCast]
    exact neg_ne_zero.mpr (h _ hmem)

/-- **`m4` is MDS over every field in which `2, 3, 5, 7, 11, 17` are nonzero**, that is,
over every field whose characteristic is none of these primes. -/
theorem m4_isMDS (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) : IsMDS (m4 K) :=
  m4_isMDS_of_minors (minors_ne_zero_of_primes h)

/-- An MDS matrix has every minor with increasingly ordered rows and columns nonzero. This
only unfolds `IsMDS` at the images of `r` and `c`. -/
theorem det_submatrix_ne_zero_of_isMDS {n : ℕ} {M : Matrix (Fin n) (Fin n) K} (hM : IsMDS M)
    {k : ℕ} {r c : Fin k → Fin n} (hr : StrictMono r) (hc : StrictMono c) :
    (M.submatrix r c).det ≠ 0 := by
  have hRow : (Finset.univ.image r).card = k := by
    rw [Finset.card_image_of_injective _ hr.injective, Finset.card_univ, Fintype.card_fin]
  have hCol : (Finset.univ.image c).card = k := by
    rw [Finset.card_image_of_injective _ hc.injective, Finset.card_univ, Fintype.card_fin]
  have hr' : (fun i => ((Finset.univ.image r).orderIsoOfFin hRow i : Fin n)) = r := by
    funext i
    rw [Finset.coe_orderIsoOfFin_apply]
    exact (congrFun (Finset.orderEmbOfFin_unique hRow
      (fun x => Finset.mem_image_of_mem r (Finset.mem_univ x)) hr) i).symm
  have hc' : (fun j => ((Finset.univ.image c).orderIsoOfFin hCol j : Fin n)) = c := by
    funext j
    rw [Finset.coe_orderIsoOfFin_apply]
    exact (congrFun (Finset.orderEmbOfFin_unique hCol
      (fun x => Finset.mem_image_of_mem c (Finset.mem_univ x)) hc) j).symm
  have h := hM k _ _ hRow hCol
  rwa [hr', hc'] at h

/-- A minor of `m4` over `K` whose integer value is `d` makes `d` nonzero in `K`, if `m4`
is MDS over `K`. -/
theorem intCast_ne_zero_of_isMDS (hM : IsMDS (m4 K)) {k : ℕ} {r c : Fin k → Fin 4}
    (hr : StrictMono r) (hc : StrictMono c) {d : ℤ} (hd : ((m4 ℤ).submatrix r c).det = d) :
    (d : K) ≠ 0 := by
  have h := det_submatrix_ne_zero_of_isMDS hM hr hc
  rwa [det_submatrix_m4, hd] at h

/-- **The criterion is exact.** `m4` is MDS over `K` if and only if `2, 3, 5, 7, 11, 17` are
all nonzero in `K`. For each of these primes `p` some minor of `m4` over `ℤ` equals `p`:
the entries `2` and `3`, the order-`2` minors `5` and `7`, and the order-`3` minors `11`
and `17`. -/
theorem m4_isMDS_iff : IsMDS (m4 K) ↔ ∀ p ∈ m4Primes, (p : K) ≠ 0 := by
  refine ⟨fun hM => ?_, m4_isMDS⟩
  have h1 : ∀ i : Fin 4, StrictMono (fun _ : Fin 1 => i) := fun _ => Subsingleton.strictMono _
  have h2 : ∀ a b : Fin 4, a < b → StrictMono ![a, b] := fun a b hab =>
    Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; exact hab)
  intro p hp
  simp only [m4Primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact_mod_cast intCast_ne_zero_of_isMDS hM (h1 0) (h1 0) (d := 2)
      (by rw [Matrix.det_unique]; decide)
  · exact_mod_cast intCast_ne_zero_of_isMDS hM (h1 0) (h1 1) (d := 3)
      (by rw [Matrix.det_unique]; decide)
  · exact_mod_cast intCast_ne_zero_of_isMDS hM (h2 0 1 (by decide)) (h2 0 2 (by decide))
      (d := 5) (by rw [Matrix.det_fin_two]; decide)
  · exact_mod_cast intCast_ne_zero_of_isMDS hM (h2 0 1 (by decide)) (h2 1 2 (by decide))
      (d := 7) (by rw [Matrix.det_fin_two]; decide)
  · exact_mod_cast intCast_ne_zero_of_isMDS hM (Fin.strictMono_succAbove 0)
      (Fin.strictMono_succAbove 2) (d := 11) (by rw [Matrix.det_fin_three]; decide)
  · exact_mod_cast intCast_ne_zero_of_isMDS hM (Fin.strictMono_succAbove 0)
      (Fin.strictMono_succAbove 1) (d := 17) (by rw [Matrix.det_fin_three]; decide)

/-! ### `m4` as a linear equivalence -/

/-- `adjugate m4 = m4Adj` over every commutative ring. Over `ℤ`, `m4 * adjugate m4` and
`m4 * m4Adj` are both `-35`, and multiplying their difference by `m4Adj` on the left
shows that `-35` times it is zero; the general case is the image of the integer one. -/
theorem m4_adjugate (R : Type*) [CommRing R] : (m4 R).adjugate = m4Adj R := by
  have hint : (m4 ℤ).adjugate = m4Adj ℤ := by
    have h1 : m4Adj ℤ * (m4 ℤ * (m4 ℤ).adjugate) = m4Adj ℤ * (m4 ℤ * m4Adj ℤ) := by
      rw [Matrix.mul_adjugate, m4_det_int, m4_mul_m4Adj]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, m4Adj_mul_m4, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul] at h1
    exact smul_right_injective _ (by norm_num) h1
  have h := RingHom.map_adjugate (Int.castRingHom R) (m4 ℤ)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hint] at h
  simp only [Int.coe_castRingHom, m4_map, m4Adj_map] at h
  exact h.symm

/-- `det m4 ≠ 0` in `K` exactly when `35 ≠ 0` in `K`. -/
theorem m4_det_ne_zero_iff : (m4 K).det ≠ 0 ↔ (35 : K) ≠ 0 := by
  rw [m4_det, neg_ne_zero]

variable (K) in
/-- **`m4` as a linear equivalence, with an explicit inverse.** Under `35 ≠ 0`, that is
`det m4 ≠ 0`, the inverse is `y ↦ (-35)⁻¹ • m4Adj y`, which is `det⁻¹ • adjugate`
(`m4Equiv_symm_apply_eq`). -/
def m4Equiv (h35 : (35 : K) ≠ 0) : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) :=
  { Matrix.mulVecLin (m4 K) with
    invFun := fun y => (-35 : K)⁻¹ • (m4Adj K).mulVec y
    left_inv := fun x => by
      change (-35 : K)⁻¹ • (m4Adj K).mulVec ((m4 K).mulVec x) = x
      rw [Matrix.mulVec_mulVec, m4Adj_mul_m4, Matrix.smul_mulVec, Matrix.one_mulVec,
        smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h35), one_smul]
    right_inv := fun y => by
      change (m4 K).mulVec ((-35 : K)⁻¹ • (m4Adj K).mulVec y) = y
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, m4_mul_m4Adj, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h35), one_smul] }

theorem m4Equiv_apply (h35 : (35 : K) ≠ 0) (x : Fin 4 → K) :
    m4Equiv K h35 x = (m4 K).mulVec x :=
  rfl

theorem m4Equiv_toLinearMap (h35 : (35 : K) ≠ 0) :
    (m4Equiv K h35).toLinearMap = Matrix.mulVecLin (m4 K) :=
  rfl

theorem m4Equiv_symm_apply (h35 : (35 : K) ≠ 0) (y : Fin 4 → K) :
    (m4Equiv K h35).symm y = (-35 : K)⁻¹ • (m4Adj K).mulVec y :=
  rfl

/-- The inverse of `m4Equiv` is `det⁻¹ • adjugate`. -/
theorem m4Equiv_symm_apply_eq (h35 : (35 : K) ≠ 0) (y : Fin 4 → K) :
    (m4Equiv K h35).symm y = ((m4 K).det)⁻¹ • (m4 K).adjugate.mulVec y := by
  rw [m4_det, m4_adjugate]
  rfl

/-! ### Branch number -/

variable [DecidableEq K]

/-- **`m4` has branch number at least `5`** over every field in which
`2, 3, 5, 7, 11, 17` are nonzero: every nonzero `x` has at least `5` nonzero coordinates
in `x` and `m4 x` together. -/
theorem m4_isBranchBound (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) :
    isBranchBound id (m4 K).mulVec 5 := by
  intro a ha
  rw [colWeight_id, colWeight_id]
  have hpos : 0 < weight a := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact Finset.card_pos.mpr ⟨i, mem_activePattern.mpr hi⟩
  exact isMDS_branch_bound (m4_isMDS h) a (by omega)

/-- The same bound for the linear equivalence `m4Equiv`. The hypothesis `h35` only names the
equivalence; it follows from `h` by `thirtyFive_ne_zero_of_primes`. -/
theorem m4Equiv_isBranchBound (h : ∀ p ∈ m4Primes, (p : K) ≠ 0) (h35 : (35 : K) ≠ 0) :
    isBranchBound id (m4Equiv K h35) 5 :=
  m4_isBranchBound h

end Field

end Poseidon2
