/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Activity

/-!
# Columns, local weights and the column-wise branch bound (Lemma 1)

Section 5.1 of Daemen and Rijmen groups the bundles into *columns* by a partition `Ξ` of the
index space, and takes `θ` to be a bricklayer map whose component maps act one per
column. This file records the counting content of that structure.

The pivot is `localWeight col ξ s`, the number of active bundles of `s` inside the single
column `ξ`. Two facts do all the work:

* `weight_eq_sum_localWeight`: bundle weight is the sum over columns of local weights,
  because the columns are the fibers of `col` and hence partition the support;
* `IsColBranchBound`: for every column that is active on either side of `θ`, the
  input-plus-output local weight in that column is at least `B`.

Lemma 1 is then a two-line counting argument: sum the per-column bound over any set of
columns known to be active. Note that `IsColBranchBound` is stated symmetrically, which
is what lets `lemma_one_in` and `lemma_one_out` both hold. Theorem 2 needs the
output-indexed form for its first round and the input-indexed form for its third.

`isColBranchBound_of_columnLocal` discharges the worry that `IsColBranchBound` is an
invented hypothesis: it is implied by the genuinely structural facts that `θ` is
column-local, fixes `0`, and has component branch number `B`.
-/

set_option autoImplicit false
-- `Fintype Col` below is used inside proofs (to sum over all columns) but not in the
-- statements, which this linter flags; `Finite Col` plus `Fintype.ofFinite` would obscure
-- the counting arguments for no gain.
set_option linter.unusedFintypeInType false

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Col]
variable {col : Idx → Col} {θ : (Idx → K) → (Idx → K)} {B : Nat}

/-- The number of active bundles of `s` lying inside the single α-set `ξ`. -/
def localWeight (col : Idx → Col) (ξ : Col) (s : Idx → K) : Nat :=
  ((activePattern s).filter (fun i => col i = ξ)).card

theorem mem_activeCols {s : Idx → K} {ξ : Col} :
    ξ ∈ activeCols col s ↔ 0 < localWeight col ξ s := by
  simp only [activeCols, localWeight, Finset.card_pos, Finset.mem_image,
    Finset.filter_nonempty_iff]

theorem localWeight_eq_zero {ξ : Col} {s : Idx → K} :
    localWeight col ξ s = 0 ↔ ∀ i, col i = ξ → s i = 0 := by
  rw [localWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi
    by_contra hne
    exact h (mem_activePattern.mpr hne) hi
  · intro h i hi hcol
    exact (mem_activePattern.mp hi) (h i hcol)

/-- The columns are the fibers of `col`, so they partition the support: bundle weight is
the sum of the local weights. -/
theorem weight_eq_sum_localWeight [Fintype Col] (col : Idx → Col) (s : Idx → K) :
    weight s = ∑ ξ : Col, localWeight col ξ s :=
  Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (col i))

/-- Every column that is active on either side of `θ` carries at least `B` active bundles,
counted across the input and the output of `θ` together.

This is the branch number of the component map of the bricklayer `θ` on that column,
transcribed so that no restriction operator is needed. It is stated symmetrically in the
input and the output, which is exactly the symmetry Definitions 3 and 4 of the paper
already have. -/
def IsColBranchBound (col : Idx → Col) (θ : (Idx → K) → (Idx → K)) (B : Nat) : Prop :=
  ∀ (a : Idx → K) (ξ : Col),
    0 < localWeight col ξ a + localWeight col ξ (θ a) →
    B ≤ localWeight col ξ a + localWeight col ξ (θ a)

/-- The counting core of Lemma 1: any set of columns that is active on one side of `θ`
contributes `B` active bundles each, and these contributions live in disjoint columns so
they simply add. -/
theorem card_mul_le_weight_add [Fintype Col] (h : IsColBranchBound col θ B)
    (a : Idx → K) {S : Finset Col}
    (hS : ∀ ξ ∈ S, 0 < localWeight col ξ a + localWeight col ξ (θ a)) :
    S.card * B ≤ weight a + weight (θ a) := by
  calc S.card * B
      = ∑ _ξ ∈ S, B := (Finset.sum_const_nat (fun _ _ => rfl)).symm
    _ ≤ ∑ ξ ∈ S, (localWeight col ξ a + localWeight col ξ (θ a)) :=
        Finset.sum_le_sum (fun ξ hξ => h a ξ (hS ξ hξ))
    _ ≤ ∑ ξ : Col, (localWeight col ξ a + localWeight col ξ (θ a)) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = weight a + weight (θ a) := by
        rw [Finset.sum_add_distrib, ← weight_eq_sum_localWeight, ← weight_eq_sum_localWeight]

/-- **Lemma 1**, output-indexed. `N` is the number of active columns *after* `θ`. -/
theorem lemma_one_out [Fintype Col] (h : IsColBranchBound col θ B) (a : Idx → K) :
    colWeight col (θ a) * B ≤ weight a + weight (θ a) :=
  card_mul_le_weight_add h a (fun _ hξ => by have := mem_activeCols.mp hξ; omega)

/-- **Lemma 1**, input-indexed. `N` is the number of active columns *before* `θ`. -/
theorem lemma_one_in [Fintype Col] (h : IsColBranchBound col θ B) (a : Idx → K) :
    colWeight col a * B ≤ weight a + weight (θ a) :=
  card_mul_le_weight_add h a (fun _ hξ => by have := mem_activeCols.mp hξ; omega)

theorem one_le_colWeight {s : Idx → K} (hs : s ≠ 0) : 1 ≤ colWeight col s := by
  rw [colWeight, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun h => hs (activePattern_eq_empty.mp h))
  exact ⟨col i, Finset.mem_image_of_mem col hi⟩

/-- A `γθ` round already forces `B(θ)` active bundles over two rounds, recovering
Theorem 1 for the column construction without going through `isBranchBound`. -/
theorem branch_le_weight_add [Fintype Col] (h : IsColBranchBound col θ B)
    {a : Idx → K} (ha : a ≠ 0) : B ≤ weight a + weight (θ a) :=
  le_trans (by simpa using Nat.mul_le_mul_right B (one_le_colWeight (col := col) ha))
    (lemma_one_in h a)

/-! ### Soundness of the hypothesis

`IsColBranchBound` is not an extra assumption smuggled in: it follows from `θ` being a
genuine column-wise bricklayer whose component maps have branch number `B`. -/

/-- `θ` acts independently on each column: its output at `i` depends only on the inputs
lying in `i`'s own column. -/
def IsColumnLocal (col : Idx → Col) (θ : (Idx → K) → (Idx → K)) : Prop :=
  ∀ (a b : Idx → K) (i : Idx), (∀ j, col j = col i → a j = b j) → θ a i = θ b i

/-- Each component map of `θ` has branch number at least `B`, in the direction the
definition of a branch number actually states: a nonzero input restricted to a column
forces `B` active bundles across that column. -/
def HasComponentBranch (col : Idx → Col) (θ : (Idx → K) → (Idx → K)) (B : Nat) : Prop :=
  ∀ (a : Idx → K) (ξ : Col), 0 < localWeight col ξ a →
    B ≤ localWeight col ξ a + localWeight col ξ (θ a)

theorem isColBranchBound_of_columnLocal (hloc : IsColumnLocal col θ) (hzero : θ 0 = 0)
    (hbr : HasComponentBranch col θ B) : IsColBranchBound col θ B := by
  intro a ξ hpos
  rcases Nat.eq_zero_or_pos (localWeight col ξ a) with hz | hp
  · -- The column is dead at the input, so column-locality kills it at the output too,
    -- contradicting `hpos`.
    exfalso
    have hzero_out : localWeight col ξ (θ a) = 0 := by
      refine localWeight_eq_zero.mpr (fun i hi => ?_)
      have : θ a i = θ 0 i :=
        hloc a 0 i (fun j hj => localWeight_eq_zero.mp hz j (hj.trans hi))
      rw [this, hzero]
      rfl
    omega
  · exact hbr a ξ hp
