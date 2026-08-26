/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Wide trail: active patterns, bundle weights and branch numbers

A difference pattern (or a selection pattern) is a state `Idx → K`. Every wide-trail
counting argument only ever looks at the *support* of such a pattern: the S-box layer
costs probability at position `i` exactly when the pattern there is nonzero, and it
costs nothing where the pattern is zero. So `K` needs no arithmetic beyond a
distinguished `0`, and the whole development is stated over an arbitrary `[Zero K]`.

This file sets up:

* `activePattern` and `weight`: the support and the *bundle weight* `w_b`;
* `activeCols` and `colWeight`: the image of the support under a partition map, and the
  *α-weight* `w_α` of Daemen and Rijmen §4.1;
* `isBranchBound`: a branch number used as a lower bound rather than as a `min`,
  which keeps the statements junk-free (an `⨅` over `ℕ` would need a nonemptiness
  side condition that no theorem here actually uses);
* `PreserveSupport`: the *only* property of the S-box layer `γ` and of the key
  addition `σ[k]` that any propagation theorem uses;
* `two_round`: Theorem 1 of the paper.

-/

set_option autoImplicit false

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Col]

/-- The set of active positions of a pattern (the positions where it is nonzero). -/
def activePattern (s : Idx → K) : Finset Idx := Finset.univ.filter (fun i => s i ≠ 0)

/-- Bundle weight `w_b`: the number of active S-boxes in this pattern. -/
def weight (s : Idx → K) : Nat := (activePattern s).card

/-- The set of active α-sets of a pattern, for the partition encoded by `col`.
`Finset.image` dedups, so two active positions in the same α-set are counted once. -/
def activeCols (col : Idx → Col) (s : Idx → K) : Finset Col := (activePattern s).image col

/-- Weight relative to a partition, `w_α`. The partition is encoded by its quotient map
`col : Idx → Col`, so an α-set is a fiber of `col`. -/
def colWeight (col : Idx → Col) (s : Idx → K) : Nat := (activeCols col s).card

/-- `B` is a branch number lower bound for `psi` with respect to the partition `col`:
every nonzero pattern has at least `B` active α-sets counted across the input and the
output together. Definitions 3 and 4 of the paper differ only in how `psi` is obtained
from the cipher, so a single predicate covers the differential and the linear case. -/
def isBranchBound (col : Idx → Col) (psi : (Idx → K) → (Idx → K)) (B : Nat) : Prop :=
  ∀ a ≠ 0, B ≤ colWeight col a + colWeight col (psi a)

/-- The only property of the S-box layer that the propagation arguments use: an
invertible bricklayer map cannot move activity between positions, because at each
position it sends a zero difference to a zero difference and a nonzero one to a
nonzero one. A key addition `σ[k]` satisfies this too, which is why keys never
appear below. -/
def PreserveSupport (γ : (Idx → K) → (Idx → K)) : Prop :=
  ∀ a, activePattern (γ a) = activePattern a

@[simp] theorem mem_activePattern {s : Idx → K} {i : Idx} :
    i ∈ activePattern s ↔ s i ≠ 0 := by
  simp [activePattern]

@[simp] theorem activePattern_eq_empty {s : Idx → K} :
    activePattern s = ∅ ↔ s = 0 := by
  simp [Finset.eq_empty_iff_forall_notMem, funext_iff]

@[simp] theorem colWeight_id [DecidableEq Idx] {s : Idx → K} :
    colWeight id s = weight s := by
  simp [colWeight, activeCols, weight]

theorem weight_eq_of_preservesSupport {γ : (Idx → K) → (Idx → K)}
    (h : PreserveSupport γ) (a : Idx → K) : weight (γ a) = weight a := by
  simp [weight, h a]

theorem colWeight_eq_of_preservesSupport {γ : (Idx → K) → (Idx → K)}
    (h : PreserveSupport γ) (col : Idx → Col) (a : Idx → K) :
    colWeight col (γ a) = colWeight col a := by
  simp [colWeight, activeCols, h a]

theorem ne_zero_of_preservesSupport {γ : (Idx → K) → (Idx → K)}
    (h : PreserveSupport γ) {a : Idx → K} (ha : a ≠ 0) : γ a ≠ 0 := by
  intro hγ
  refine ha (activePattern_eq_empty.mp ?_)
  rw [← h a, hγ]
  simp

theorem preserveSupport_comp {γ δ : (Idx → K) → (Idx → K)}
    (hγ : PreserveSupport γ) (hδ : PreserveSupport δ) : PreserveSupport (γ ∘ δ) :=
  fun a => by simp only [Function.comp_apply, hγ (δ a), hδ a]

/-- **Theorem 1 (Two-Round Propagation Theorem).**
In a `γλ` round the S-box layer and the key addition cannot change the active pattern,
so the number of active bundles across two rounds is governed entirely by `λ`, and is
bounded below by its branch number. -/
theorem two_round [DecidableEq Idx] {γ lam : (Idx → K) → (Idx → K)} {B : Nat}
    (hγ : PreserveSupport γ) (hlam : isBranchBound id lam B)
    {a : Idx → K} (ha : a ≠ 0) :
    B ≤ weight a + weight (lam (γ a)) := by
  have h := hlam (γ a) (ne_zero_of_preservesSupport hγ ha)
  rw [colWeight_id, colWeight_id, weight_eq_of_preservesSupport hγ] at h
  exact h
