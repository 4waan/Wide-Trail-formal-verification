/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Propagation.Activity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Block-circulant layers and their branch number

A state is indexed by `B × P`: block `i : B`, position `c : P`. Given a linear map
`N` on one block, `blockMix N` replaces block `i` by `N (x_i + ∑ⱼ xⱼ)`. In matrix
form this is the block circulant `circ(2N, N, …, N)`, the shape of the Poseidon2
external ("MDS-light") layer at widths `8, 12, …, 24`, where `N` is the `4 × 4` matrix
`M4`. (At width four Poseidon2 uses `M4` itself.)

Write `t = |B|` and `k = |P|`. The main theorem, `isBranchBound_blockMix`, says:
if `N` has branch number `k + 1` and the integers `1, …, t + 1` are nonzero in `K`,
then `blockMix N` has branch number at least `min (t + k) (2 * (k + 1))`, counting
nonzero coordinates of the whole state. For `t = k = 4` this is `8`
(`isBranchBound_blockMix_fin_four`, and `isBranchBound_blockMix_sixteen` for the same
map on a flat state `Fin 16 → K` with blocks of four consecutive coordinates).

The proof splits on the block sum `s = ∑ⱼ xⱼ`.

* If `s = 0`, at least two blocks are nonzero and each costs `k + 1` on its own,
  because block `i` of the output is `N xᵢ`.
* If `s ≠ 0`, let `w = |supp s|`, let `Q` be the blocks with `xᵢ = -s` and `P'` the
  rest. Blocks in `Q` cost `w` and map to zero. A block in `P'` costs at least
  `k + 1 - mᵢ`, where `mᵢ` counts positions of `supp s` at which `xᵢ` vanishes.
  At a position `c ∈ supp s` the blocks of `P'` sum to `(|Q| + 1) s_c ≠ 0`, so not all
  of them vanish there; summing over `c` gives `∑ mᵢ ≤ w (|P'| - 1)`. The resulting
  bound `|Q| w + |P'| (k + 1) - w (|P'| - 1)` exceeds `t + k` by
  `|Q| (w - 1) + (|P'| - 1) (k - w) ≥ 0`.

`blockMixEquiv` packages `blockMix N` as a linear equivalence when `N` is one and
`t + 1` is nonzero in `K`, with the explicit inverse `blockMixInv`.

What is not claimed: nothing here says that `M4`, or any other concrete matrix, has
branch number `k + 1` over any concrete field; that is a hypothesis. The bound is a
lower bound; `WideTrail.Algebra.Checks.BlockCirculant` shows it is attained in one
small instance and fails in one small instance where `t + 1 = 0` in `K`. The hypothesis
on `1, …, t + 1` is only used at `|Q| + 1`; the checks show it cannot be dropped at
`t + 1`, and nothing is claimed about whether the smaller values are needed. The theorem
counts coordinates over the whole state, not active blocks.
-/

set_option autoImplicit false

namespace BlockCirculant

open Finset

section Mix

variable {B P K : Type*} [Fintype B] [Field K]

/-- Block `i` of a state indexed by `B × P`. -/
def block (x : B × P → K) (i : B) : P → K := fun c => x (i, c)

/-- The sum of all blocks, position by position. -/
def blockSum (x : B × P → K) : P → K := fun c => ∑ j, x (j, c)

theorem blockSum_add (x y : B × P → K) : blockSum (x + y) = blockSum x + blockSum y := by
  funext c
  simp only [blockSum, Pi.add_apply, Finset.sum_add_distrib]

theorem blockSum_smul (a : K) (x : B × P → K) : blockSum (a • x) = a • blockSum x := by
  funext c
  simp only [blockSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The block circulant `circ(2N, N, …, N)`: block `i` of the output is
`N (xᵢ + ∑ⱼ xⱼ)`. -/
def blockMix (N : (P → K) →ₗ[K] (P → K)) : (B × P → K) →ₗ[K] (B × P → K) where
  toFun x ic := N (block x ic.1 + blockSum x) ic.2
  map_add' x y := by
    funext ic
    have h : block (x + y) ic.1 + blockSum (x + y) =
        (block x ic.1 + blockSum x) + (block y ic.1 + blockSum y) := by
      rw [blockSum_add]
      funext c
      simp only [block, Pi.add_apply]
      ring
    simp only [h, map_add, Pi.add_apply]
  map_smul' a x := by
    funext ic
    have h : block (a • x) ic.1 + blockSum (a • x) = a • (block x ic.1 + blockSum x) := by
      rw [blockSum_smul]
      funext c
      simp only [block, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem blockMix_apply (N : (P → K) →ₗ[K] (P → K)) (x : B × P → K) (i : B) (c : P) :
    blockMix N x (i, c) = N (fun c' => x (i, c') + ∑ j, x (j, c')) c := rfl

theorem block_blockMix (N : (P → K) →ₗ[K] (P → K)) (x : B × P → K) (i : B) :
    block (blockMix N x) i = N (block x i + blockSum x) := rfl

/-- The explicit inverse of `blockMix N`: with `zᵢ = N⁻¹ yᵢ` and
`s = (∑ᵢ zᵢ) / (t + 1)`, block `i` of the preimage is `zᵢ - s`. -/
def blockMixInv (N : (P → K) ≃ₗ[K] (P → K)) (y : B × P → K) : B × P → K :=
  fun ic => N.symm (block y ic.1) ic.2 -
    (∑ j, N.symm (block y j) ic.2) / ((Fintype.card B + 1 : ℕ) : K)

theorem blockSum_eq_sum_block (x : B × P → K) (c : P) :
    blockSum x c = ∑ j, block x j c := rfl

/-- `blockMixInv N` is a left inverse of `blockMix N`. -/
theorem blockMixInv_blockMix (N : (P → K) ≃ₗ[K] (P → K))
    (h : ((Fintype.card B + 1 : ℕ) : K) ≠ 0) (x : B × P → K) :
    blockMixInv N (blockMix N.toLinearMap x) = x := by
  have hz : ∀ j, N.symm (block (blockMix N.toLinearMap x) j) = block x j + blockSum x :=
    fun j => by rw [block_blockMix]; simp
  funext ⟨i, c⟩
  have hsum : ∑ j, (block x j + blockSum x) c =
      ((Fintype.card B + 1 : ℕ) : K) * blockSum x c := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← blockSum_eq_sum_block]
    push_cast
    ring
  simp only [blockMixInv, hz, hsum]
  field_simp
  simp only [Pi.add_apply, block]
  ring

/-- `blockMixInv N` is a right inverse of `blockMix N`. -/
theorem blockMix_blockMixInv (N : (P → K) ≃ₗ[K] (P → K))
    (h : ((Fintype.card B + 1 : ℕ) : K) ≠ 0) (y : B × P → K) :
    blockMix N.toLinearMap (blockMixInv N y) = y := by
  funext ⟨i, c⟩
  have h' : ((Fintype.card B : K) + 1) ≠ 0 := by exact_mod_cast h
  have hs : blockSum (blockMixInv N y) = fun c' =>
      (∑ j, N.symm (block y j) c') / ((Fintype.card B + 1 : ℕ) : K) := by
    funext c'
    simp only [blockSum, blockMixInv, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hz : block (blockMixInv N y) i + blockSum (blockMixInv N y) = N.symm (block y i) := by
    rw [hs]
    funext c'
    simp only [block, blockMixInv, Pi.add_apply]
    ring
  rw [blockMix_apply]
  change N (block (blockMixInv N y) i + blockSum (blockMixInv N y)) c = y (i, c)
  rw [hz, LinearEquiv.apply_symm_apply]
  rfl

/-- `blockMix N` as a linear equivalence, for `N` invertible and `t + 1 ≠ 0` in `K`.
The inverse is `blockMixInv N`. -/
def blockMixEquiv (N : (P → K) ≃ₗ[K] (P → K)) (h : ((Fintype.card B + 1 : ℕ) : K) ≠ 0) :
    (B × P → K) ≃ₗ[K] (B × P → K) :=
  { blockMix N.toLinearMap with
    invFun := blockMixInv N
    left_inv := blockMixInv_blockMix N h
    right_inv := blockMix_blockMixInv N h }

theorem blockMixEquiv_apply (N : (P → K) ≃ₗ[K] (P → K))
    (h : ((Fintype.card B + 1 : ℕ) : K) ≠ 0) (x : B × P → K) :
    blockMixEquiv N h x = blockMix N.toLinearMap x := rfl

theorem blockMixEquiv_symm_apply (N : (P → K) ≃ₗ[K] (P → K))
    (h : ((Fintype.card B + 1 : ℕ) : K) ≠ 0) (y : B × P → K) :
    (blockMixEquiv N h).symm y = blockMixInv N y := rfl

/-- If the block sum vanishes, a nonzero state has two distinct nonzero blocks: a single
nonzero block would equal the block sum. -/
theorem exists_two_blocks {x : B × P → K} (hx : x ≠ 0) (hs : blockSum x = 0) :
    ∃ i j, i ≠ j ∧ block x i ≠ 0 ∧ block x j ≠ 0 := by
  obtain ⟨⟨i, c⟩, hic⟩ : ∃ ic, x ic ≠ 0 := Function.ne_iff.mp hx
  have hi : block x i ≠ 0 := fun h => hic (congrFun h c)
  by_contra hcon
  push Not at hcon
  have hsum : blockSum x = block x i := by
    funext c'
    rw [blockSum_eq_sum_block, Finset.sum_eq_single i]
    · intro j _ hji
      exact congrFun (hcon i j (Ne.symm hji) hi) c'
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  exact hi (hsum ▸ hs)

/-! ### Counting -/

variable [Fintype P] [DecidableEq K]

/-- The weight of a state is the sum of the weights of its blocks. -/
theorem weight_eq_sum_block (x : B × P → K) : weight x = ∑ i, weight (block x i) := by
  simp only [weight, activePattern, Finset.card_filter]
  rw [Fintype.sum_prod_type]
  rfl

/-- Adding `v` to `u` can only activate positions of `supp v` at which `u` vanishes. -/
theorem weight_add_le (u v : P → K) :
    weight (u + v) ≤ weight u + #{c ∈ activePattern v | u c = 0} := by
  classical
  unfold weight
  calc #(activePattern (u + v))
      ≤ #(activePattern u ∪ {c ∈ activePattern v | u c = 0}) := by
        apply Finset.card_le_card
        intro c hc
        rw [mem_activePattern, Pi.add_apply] at hc
        rw [Finset.mem_union, Finset.mem_filter, mem_activePattern, mem_activePattern]
        by_cases hu : u c = 0
        · rw [hu, zero_add] at hc
          exact Or.inr ⟨hc, hu⟩
        · exact Or.inl hu
    _ ≤ _ := Finset.card_union_le _ _

theorem weight_neg (v : P → K) : weight (-v) = weight v := by
  simp [weight, activePattern]

/-- **The case `∑ⱼ xⱼ = 0`.** Block `i` of the output is `N xᵢ`, and at least two blocks
are nonzero, so the weight is at least `2 (k + 1)`. -/
theorem le_weight_of_blockSum_eq_zero [DecidableEq P] {N : (P → K) →ₗ[K] (P → K)}
    (hN : isBranchBound id N (Fintype.card P + 1)) {x : B × P → K} (hx : x ≠ 0)
    (hs : blockSum x = 0) :
    2 * (Fintype.card P + 1) ≤ weight x + weight (blockMix N x) := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_blocks hx hs
  have key : ∀ l, block x l ≠ 0 →
      Fintype.card P + 1 ≤ weight (block x l) + weight (block (blockMix N x) l) := by
    intro l hl
    have h := hN (block x l) hl
    rw [colWeight_id, colWeight_id] at h
    rwa [block_blockMix, hs, add_zero]
  rw [weight_eq_sum_block, weight_eq_sum_block, ← Finset.sum_add_distrib]
  have hi' := key i hi
  have hj' := key j hj
  calc 2 * (Fintype.card P + 1)
      ≤ (weight (block x i) + weight (block (blockMix N x) i)) +
        (weight (block x j) + weight (block (blockMix N x) j)) := by omega
    _ = ∑ l ∈ {i, j}, (weight (block x l) + weight (block (blockMix N x) l)) := by
        rw [Finset.sum_pair hij]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-! ### The case `∑ⱼ xⱼ ≠ 0` -/

/-- The blocks `i` with `xᵢ + ∑ⱼ xⱼ = 0`. Their output block is `N 0 = 0`. -/
def cancelled (x : B × P → K) : Finset B := {i | block x i + blockSum x = 0}

/-- The remaining blocks, those with `xᵢ + ∑ⱼ xⱼ ≠ 0`. -/
def uncancelled (x : B × P → K) : Finset B := {i | block x i + blockSum x ≠ 0}

theorem card_cancelled_add_card_uncancelled (x : B × P → K) :
    #(cancelled x) + #(uncancelled x) = Fintype.card B := by
  rw [cancelled, uncancelled, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- A cancelled block is `-∑ⱼ xⱼ`, so it has the weight of the block sum. -/
theorem weight_block_of_mem_cancelled {x : B × P → K} {i : B} (hi : i ∈ cancelled x) :
    weight (block x i) = weight (blockSum x) := by
  rw [cancelled, Finset.mem_filter] at hi
  rw [eq_neg_of_add_eq_zero_left hi.2, weight_neg]

/-- An uncancelled block costs at least `k + 1`, less the number of positions of
`supp (∑ⱼ xⱼ)` at which it vanishes. -/
theorem le_weight_block_of_mem_uncancelled [DecidableEq P] {N : (P → K) →ₗ[K] (P → K)}
    (hN : isBranchBound id N (Fintype.card P + 1)) {x : B × P → K} {i : B}
    (hi : i ∈ uncancelled x) :
    Fintype.card P + 1 ≤ weight (block x i) + weight (block (blockMix N x) i) +
      #{c ∈ activePattern (blockSum x) | block x i c = 0} := by
  rw [uncancelled, Finset.mem_filter] at hi
  have h1 := hN _ hi.2
  rw [colWeight_id, colWeight_id] at h1
  have h2 := weight_add_le (block x i) (blockSum x)
  rw [block_blockMix]
  omega

/-- At each position the uncancelled blocks sum to `(|Q| + 1)` times the block sum,
where `Q` is the set of cancelled blocks. -/
theorem sum_uncancelled (x : B × P → K) (c : P) :
    ∑ i ∈ uncancelled x, x (i, c) = ((#(cancelled x) + 1 : ℕ) : K) * blockSum x c := by
  have h1 := Finset.sum_filter_add_sum_filter_not (univ : Finset B)
    (fun i => block x i + blockSum x = 0) (fun i => x (i, c))
  have h2 : ∑ i ∈ cancelled x, x (i, c) = ∑ _i ∈ cancelled x, -blockSum x c :=
    Finset.sum_congr rfl fun i hi => by
      rw [cancelled, Finset.mem_filter] at hi
      have h := congrFun hi.2 c
      simp only [Pi.add_apply, Pi.zero_apply, block] at h
      linear_combination h
  change ∑ i ∈ cancelled x, x (i, c) + ∑ i ∈ uncancelled x, x (i, c) = blockSum x c at h1
  rw [h2, Finset.sum_const, nsmul_eq_mul] at h1
  push_cast
  linear_combination h1

/-- At a position `c` of `supp (∑ⱼ xⱼ)`, some uncancelled block is nonzero. This is where
`|Q| + 1 ≠ 0` in `K` is used. -/
theorem card_uncancelled_zero_lt
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card B + 1 → (n : K) ≠ 0)
    (x : B × P → K) {c : P} (hc : blockSum x c ≠ 0) :
    #{i ∈ uncancelled x | block x i c = 0} + 1 ≤ #(uncancelled x) := by
  have hq : #(cancelled x) ≤ Fintype.card B := Finset.card_le_univ _
  have hne : ((#(cancelled x) + 1 : ℕ) : K) ≠ 0 := hchar _ (by omega) (by omega)
  have hsum : ∑ i ∈ uncancelled x, x (i, c) ≠ 0 := by
    rw [sum_uncancelled]
    exact mul_ne_zero hne hc
  obtain ⟨i, hi, hxi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨i, hi, hxi⟩)

/-- Summed over the uncancelled blocks, the deficits `mᵢ` total at most
`w (|P'| - 1)`, where `w = |supp (∑ⱼ xⱼ)|` and `P'` is the set of uncancelled blocks. -/
theorem sum_deficit_le (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card B + 1 → (n : K) ≠ 0)
    (x : B × P → K) :
    ∑ i ∈ uncancelled x, #{c ∈ activePattern (blockSum x) | block x i c = 0} +
      weight (blockSum x) ≤ weight (blockSum x) * #(uncancelled x) := by
  have hswap : ∑ i ∈ uncancelled x, #{c ∈ activePattern (blockSum x) | block x i c = 0} =
      ∑ c ∈ activePattern (blockSum x), #{i ∈ uncancelled x | block x i c = 0} := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap, weight]
  calc ∑ c ∈ activePattern (blockSum x), #{i ∈ uncancelled x | block x i c = 0} +
        #(activePattern (blockSum x))
      = ∑ c ∈ activePattern (blockSum x), (#{i ∈ uncancelled x | block x i c = 0} + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ _c ∈ activePattern (blockSum x), #(uncancelled x) :=
        Finset.sum_le_sum fun c hc =>
          card_uncancelled_zero_lt hchar x (mem_activePattern.mp hc)
    _ = #(activePattern (blockSum x)) * #(uncancelled x) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **The case `∑ⱼ xⱼ ≠ 0`.** The weight is at least `t + k`. -/
theorem le_weight_of_blockSum_ne_zero [DecidableEq P] {N : (P → K) →ₗ[K] (P → K)}
    (hN : isBranchBound id N (Fintype.card P + 1))
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card B + 1 → (n : K) ≠ 0)
    {x : B × P → K} (hs : blockSum x ≠ 0) :
    Fintype.card B + Fintype.card P ≤ weight x + weight (blockMix N x) := by
  set f : B → ℕ := fun i => weight (block x i) + weight (block (blockMix N x) i)
  have htot : weight x + weight (blockMix N x) =
      ∑ i ∈ cancelled x, f i + ∑ i ∈ uncancelled x, f i := by
    rw [weight_eq_sum_block, weight_eq_sum_block, ← Finset.sum_add_distrib]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hQ : #(cancelled x) * weight (blockSum x) ≤ ∑ i ∈ cancelled x, f i := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => by
      have h := weight_block_of_mem_cancelled hi
      change weight (blockSum x) ≤ weight (block x i) + weight (block (blockMix N x) i)
      omega
  have hR : #(uncancelled x) * (Fintype.card P + 1) ≤ ∑ i ∈ uncancelled x, f i +
      ∑ i ∈ uncancelled x, #{c ∈ activePattern (blockSum x) | block x i c = 0} := by
    rw [← Finset.sum_add_distrib, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => le_weight_block_of_mem_uncancelled hN hi
  have hm := sum_deficit_le hchar x
  have hQR := card_cancelled_add_card_uncancelled x
  have hw1 : 1 ≤ weight (blockSum x) :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (mt activePattern_eq_empty.mp hs))
  have hwk : weight (blockSum x) ≤ Fintype.card P := Finset.card_le_univ _
  rw [htot]
  generalize ∑ i ∈ cancelled x, f i = X at hQ ⊢
  generalize ∑ i ∈ uncancelled x, f i = A at hR ⊢
  generalize ∑ i ∈ uncancelled x, #{c ∈ activePattern (blockSum x) | block x i c = 0} = M
    at hR hm
  generalize weight (blockSum x) = w at hQ hm hw1 hwk
  generalize #(cancelled x) = q at hQ hQR
  generalize #(uncancelled x) = p at hR hm hQR
  generalize Fintype.card P = k at hR hwk ⊢
  rw [← hQR]
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, k = w' + 1 + a := ⟨k - (w' + 1), by omega⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := by
    rcases p with _ | p'
    · omega
    · exact ⟨p', rfl⟩
  nlinarith [Nat.zero_le (q * w'), Nat.zero_le (p' * a)]

/-- **Branch number of `circ(2N, N, …, N)`.** Let `t = |B|` and `k = |P|`. If `N` has
branch number `k + 1` and `1, …, t + 1` are nonzero in `K`, then every nonzero state
`x` has at least `min (t + k) (2 (k + 1))` nonzero coordinates in `x` and
`blockMix N x` together.

The two terms of the `min` come from the two cases of the proof: `t + k` when the block
sum is nonzero, `2 (k + 1)` when it is zero. Only the first case uses the hypothesis on
`1, …, t + 1`. -/
theorem isBranchBound_blockMix [DecidableEq B] [DecidableEq P] {N : (P → K) →ₗ[K] (P → K)}
    (hN : isBranchBound id N (Fintype.card P + 1))
    (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ Fintype.card B + 1 → (n : K) ≠ 0) :
    isBranchBound id (blockMix (B := B) N)
      (min (Fintype.card B + Fintype.card P) (2 * (Fintype.card P + 1))) := by
  intro x hx
  rw [colWeight_id, colWeight_id]
  by_cases hs : blockSum x = 0
  · exact le_trans (min_le_right _ _) (le_weight_of_blockSum_eq_zero hN hx hs)
  · exact le_trans (min_le_left _ _) (le_weight_of_blockSum_ne_zero hN hchar hs)

/-- **Four blocks of four.** The Poseidon2 external layer shape for width `16`: if `N`
has branch number `5` and `1, …, 5` are nonzero in `K`, then `circ(2N, N, N, N)` has
branch number at least `8`. -/
theorem isBranchBound_blockMix_fin_four {N : (Fin 4 → K) →ₗ[K] (Fin 4 → K)}
    (hN : isBranchBound id N 5) (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ 5 → (n : K) ≠ 0) :
    isBranchBound id (blockMix (B := Fin 4) N) 8 := by
  have h := isBranchBound_blockMix (B := Fin 4) (N := N) (by simpa using hN)
    (by simpa using hchar)
  simpa using h

end Mix

/-! ### Reindexing

A concrete permutation acts on a flat state such as `Fin 16 → K`, not on `B × P → K`.
Branch bounds with respect to `id` only count nonzero coordinates, so they transfer
along any bijection of index sets; for blocks of consecutive coordinates the bijection
is `finProdFinEquiv`, which sends `(i, c)` to `c + k * i`. -/

section Reindex

variable {Idx Idx' K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [Fintype Idx']

/-- Relabelling coordinates does not change the weight. -/
theorem weight_comp_equiv (e : Idx' ≃ Idx) (x : Idx → K) : weight (x ∘ e) = weight x :=
  Finset.card_equiv e fun i => by simp

/-- A branch bound with respect to `id` is unchanged by relabelling coordinates. -/
theorem isBranchBound_conj [DecidableEq Idx] [DecidableEq Idx'] (e : Idx' ≃ Idx)
    {psi : (Idx → K) → (Idx → K)} {b : ℕ} (h : isBranchBound id psi b) :
    isBranchBound id (fun y => psi (y ∘ e.symm) ∘ e) b := by
  intro y hy
  have hy' : y ∘ e.symm ≠ 0 := by
    intro h0
    apply hy
    funext i
    simpa using congrFun h0 (e i)
  have h' := h (y ∘ e.symm) hy'
  rw [colWeight_id, colWeight_id] at h' ⊢
  rwa [weight_comp_equiv, ← weight_comp_equiv e.symm y]

end Reindex

/-- **Four blocks of four, on a flat state.** `isBranchBound_blockMix_fin_four` for a state
`Fin 16 → K` whose block `i` is coordinates `4 i, …, 4 i + 3`: coordinate `4 i + c` of the
output is coordinate `(i, c)` of `blockMix N`. -/
theorem isBranchBound_blockMix_sixteen {K : Type*} [Field K] [DecidableEq K]
    {N : (Fin 4 → K) →ₗ[K] (Fin 4 → K)}
    (hN : isBranchBound id N 5) (hchar : ∀ n : ℕ, 1 ≤ n → n ≤ 5 → (n : K) ≠ 0) :
    isBranchBound id
      (fun y : Fin 16 → K =>
        blockMix (B := Fin 4) N (y ∘ (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16)) ∘
          (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm) 8 :=
  isBranchBound_conj (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm
    (isBranchBound_blockMix_fin_four hN hchar)

end BlockCirculant

/-! ### The evaluation order of the Plonky3 code

Plonky3's `mds_light_permutation` (`p3-poseidon2` `0.4.3-succinct`, `src/matrix.rs:110-139`)
does not form `xᵢ + ∑ⱼ xⱼ`. It applies the block map to every block first and then adds,
at each position, the sum of those images over all blocks. By linearity of `N` this is
the same map. -/

namespace BlockCirculant

variable {B P K : Type*} [Fintype B] [Field K]

/-- A finite sum of functions, evaluated at one point. -/
private theorem sum_fun_apply (f : B → P → K) (c : P) : (∑ j, f j) c = ∑ j, f j c :=
  map_sum (Pi.evalAddMonoidHom (fun _ : P => K) c) f Finset.univ

/-- The block sum as a sum of blocks, as functions. -/
theorem blockSum_eq_sum (x : B × P → K) : blockSum x = ∑ j, block x j := by
  funext c
  rw [sum_fun_apply]
  rfl

/-- **Map each block, then add the sum of the images.** Block `i` of `blockMix N x` is
`N xᵢ + ∑ⱼ N xⱼ`. -/
theorem block_blockMix_eq_add_sum (N : (P → K) →ₗ[K] (P → K)) (x : B × P → K) (i : B) :
    block (blockMix N x) i = N (block x i) + ∑ j, N (block x j) := by
  rw [block_blockMix, map_add, blockSum_eq_sum, map_sum]

/-- `block_blockMix_eq_add_sum`, one coordinate at a time. -/
theorem blockMix_apply_eq_add_sum (N : (P → K) →ₗ[K] (P → K)) (x : B × P → K) (i : B)
    (c : P) : blockMix N x (i, c) = N (block x i) c + ∑ j, N (block x j) c := by
  have h := congrFun (block_blockMix_eq_add_sum N x i) c
  rw [Pi.add_apply, sum_fun_apply] at h
  exact h

end BlockCirculant

/-! ### States whose blocks sum to zero

The proof of `isBranchBound_blockMix` splits on the block sum `s = ∑ⱼ xⱼ`. This section isolates
the case `s = 0`. For such a state, block `i` of `blockMix N x` is `N xᵢ`
(`blockMix_of_blockSum_eq_zero`): the layer applies `N` to each block separately and mixes
nothing between blocks. For every state the block sum of the output is `(t + 1) • N s`
(`blockSum_blockMix`). So the states with `s = 0` form a subspace, `blockSumZero`, that
`blockMix N` maps into itself (`blockMix_mem_blockSumZero`); when `N` is injective and `t + 1 ≠ 0`
in `K`, a state lies in it exactly when its image does (`blockMix_mem_blockSumZero_iff`). Its
dimension is `(t - 1) k` (`finrank_blockSumZero`).

Why this subspace is singled out: recent round-skipping work on Poseidon2 (IACR ePrint 2026/306)
exploits the structure of the linear-layer matrices; the zero-block-sum subspace is one
structural property of the external matrix, and no claim is made here about which properties
that work uses. Its authors state that their attacks do not mean that the primitive falls short
of its claimed security level. Nothing here is a statement about any attack: these are facts
about the linear map `blockMix N` alone. They say nothing about the S-box layer, which in a full
round acts on every coordinate and need not keep a state in `blockSumZero`, and nothing about any
concrete parameter set. -/

namespace BlockCirculant

variable {B P K : Type*} [Fintype B] [Field K]

/-- **No mixing between blocks when the block sum vanishes.** If `∑ⱼ xⱼ = 0`, block `i` of
`blockMix N x` is `N xᵢ`. -/
theorem blockMix_of_blockSum_eq_zero (N : (P → K) →ₗ[K] (P → K)) {x : B × P → K}
    (hs : blockSum x = 0) (i : B) : block (blockMix N x) i = N (block x i) := by
  rw [block_blockMix, hs, add_zero]

/-- `blockMix_of_blockSum_eq_zero` for the whole state: if `∑ⱼ xⱼ = 0`, coordinate `(i, c)` of
`blockMix N x` is coordinate `c` of `N xᵢ`. -/
theorem blockMix_eq_of_blockSum_eq_zero (N : (P → K) →ₗ[K] (P → K)) {x : B × P → K}
    (hs : blockSum x = 0) : blockMix N x = fun ic => N (block x ic.1) ic.2 := by
  funext ⟨i, c⟩
  exact congrFun (blockMix_of_blockSum_eq_zero N hs i) c

/-- **The block sum of the output.** For every state, `∑ᵢ (blockMix N x)ᵢ = (t + 1) • N s` with
`s = ∑ⱼ xⱼ`: output block `i` is `N (xᵢ + s)`, and the inputs `xᵢ + s` sum to `s + t s`. -/
theorem blockSum_blockMix (N : (P → K) →ₗ[K] (P → K)) (x : B × P → K) :
    blockSum (blockMix N x) = ((Fintype.card B + 1 : ℕ) : K) • N (blockSum x) := by
  have h : ∑ i, (block x i + blockSum x) = ((Fintype.card B + 1 : ℕ) : K) • blockSum x := by
    rw [Finset.sum_add_distrib, ← blockSum_eq_sum, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul, succ_nsmul, add_comm]
  rw [blockSum_eq_sum]
  simp only [block_blockMix]
  rw [← map_sum, h, map_smul]

/-- The block sum `x ↦ ∑ⱼ xⱼ` as a linear map. -/
def blockSumLinear : (B × P → K) →ₗ[K] (P → K) where
  toFun := blockSum
  map_add' := blockSum_add
  map_smul' := blockSum_smul

theorem blockSumLinear_apply (x : B × P → K) : blockSumLinear x = blockSum x := rfl

/-- The states whose blocks sum to zero: the kernel of `blockSumLinear`. -/
def blockSumZero : Submodule K (B × P → K) := LinearMap.ker blockSumLinear

theorem mem_blockSumZero {x : B × P → K} : x ∈ blockSumZero ↔ blockSum x = 0 :=
  LinearMap.mem_ker

/-- **`blockMix N` maps `blockSumZero` into itself**, for every linear `N` and every field:
the block sum of the output is `(t + 1) • N 0 = 0`. -/
theorem blockMix_mem_blockSumZero (N : (P → K) →ₗ[K] (P → K)) {x : B × P → K}
    (hx : x ∈ blockSumZero) : blockMix N x ∈ blockSumZero := by
  rw [mem_blockSumZero] at hx ⊢
  rw [blockSum_blockMix, hx, map_zero, smul_zero]

/-- If `N` is injective and `t + 1 ≠ 0` in `K`, then `blockMix N x` lies in `blockSumZero`
exactly when `x` does. Without `t + 1 ≠ 0` the forward direction can fail
(`Checks.flat_not_mem_blockSumZero`). -/
theorem blockMix_mem_blockSumZero_iff {N : (P → K) →ₗ[K] (P → K)} (hN : Function.Injective N)
    (h : ((Fintype.card B + 1 : ℕ) : K) ≠ 0) (x : B × P → K) :
    blockMix N x ∈ blockSumZero ↔ x ∈ blockSumZero := by
  rw [mem_blockSumZero, mem_blockSumZero, blockSum_blockMix, smul_eq_zero, map_eq_zero_iff N hN]
  exact or_iff_right h

/-- **Dimension.** `blockSumZero` has dimension `(t - 1) k`. For `t ≥ 1` it is the kernel of
the surjective map `blockSumLinear` onto `P → K`, so rank–nullity gives `t k - k`; for `t = 0`
both sides are `0`. -/
theorem finrank_blockSumZero [Fintype P] :
    Module.finrank K (blockSumZero (B := B) (P := P) (K := K)) =
      (Fintype.card B - 1) * Fintype.card P := by
  classical
  have hrn := LinearMap.finrank_range_add_finrank_ker (blockSumLinear (B := B) (P := P) (K := K))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] at hrn
  rcases isEmpty_or_nonempty B with hB | ⟨⟨i₀⟩⟩
  · rw [Fintype.card_eq_zero, zero_mul] at hrn
    rw [Fintype.card_eq_zero, Nat.zero_sub, zero_mul]
    exact (Nat.eq_zero_of_add_eq_zero hrn).2
  · have htop : LinearMap.range (blockSumLinear (B := B) (P := P) (K := K)) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro v
      refine ⟨fun ic => if ic.1 = i₀ then v ic.2 else 0, ?_⟩
      funext c
      simp [blockSumLinear_apply, blockSum]
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hrn
    rw [Nat.sub_mul, one_mul]
    exact Nat.eq_sub_of_add_eq' hrn

end BlockCirculant
