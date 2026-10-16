/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Schedule
import WideTrail.Algebra.MDS

/-!
# Activity contributed by full outer rounds

Disjoint pairs of full rounds each cost a branch bound. A remaining odd round
costs one because distinct executions stay distinct. Apply this independently
to the prefix and suffix; no pair crosses the middle computation.
-/

set_option autoImplicit false

namespace Hades

/-- Pair a finite sequence without discarding its odd final element. -/
theorem pair_sum_bound (w : Nat → Nat) (B length : Nat) :
    (∀ j < length, 1 ≤ w j) →
    (∀ j, j + 1 < length → B ≤ w j + w (j + 1)) →
    length / 2 * B + length % 2 ≤ ∑ j ∈ Finset.range length, w j := by
  induction length using Nat.twoStepInduction with
  | zero => simp
  | one =>
    intro hpos _
    simpa using hpos 0 (by omega)
  | more n ih _ =>
    intro hpos hpair
    have h := ih (fun j hj => hpos j (by omega)) (fun j hj => hpair j (by omega))
    have hp := hpair n (by omega)
    have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
    have hmod : (n + 2) % 2 = n % 2 := by omega
    rw [hdiv, hmod, Nat.add_mul, one_mul, Finset.sum_range_succ, Finset.sum_range_succ]
    omega

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- Adjacent full rounds charge the branch bound of the first mixing layer. -/
theorem fullRound_pair (rounds : Nat → RoundSpec Idx K) {x y : Idx → K} (hxy : x ≠ y)
    (n B : Nat) (hfull : (rounds n).mask = Finset.univ)
    (hnext : (rounds (n + 1)).mask = Finset.univ)
    (hbranch : isBranchBound id (rounds n).lin B) :
    B ≤ sboxWeight (rounds n).mask (differenceTrace rounds x y n)
      + sboxWeight (rounds (n + 1)).mask (differenceTrace rounds x y (n + 1)) := by
  have hs := nonlinearDifference_support rounds x y n
  have hb := ne_zero_congr hs (differenceTrace_ne_zero rounds hxy n)
  have h := hbranch _ hb
  rw [colWeight_id, colWeight_id, weight_congr hs, ← differenceTrace_succ] at h
  simpa [hfull, hnext] using h

/-- A shifted window consisting entirely of full rounds. The last linear layer
of the window needs no branch hypothesis. -/
theorem fullWindow_bound (rounds : Nat → RoundSpec Idx K) {x y : Idx → K} (hxy : x ≠ y)
    (start length B : Nat)
    (hfull : ∀ j < length, (rounds (start + j)).mask = Finset.univ)
    (hbranch : ∀ j, j + 1 < length → isBranchBound id (rounds (start + j)).lin B) :
    length / 2 * B + length % 2 ≤
      scheduledWeight rounds (differenceTrace rounds x y) start length := by
  apply pair_sum_bound
  · intro j hj
    simpa [hfull j hj] using one_le_weight (differenceTrace_ne_zero rounds hxy (start + j))
  · intro j hj
    have h := fullRound_pair rounds hxy (start + j) B
      (hfull j (by omega)) (by simpa [Nat.add_assoc] using hfull (j + 1) hj) (hbranch j hj)
    simpa [Nat.add_assoc] using h

/-- The two full blocks contribute independently, for any bijective middle
rounds and fixed additions. No assumption is made about middle-round diffusion. -/
theorem outerRound_bound (rounds : Nat → RoundSpec Idx K) {x y : Idx → K} (hxy : x ≠ y)
    (r m s B : Nat)
    (hprefix : ∀ j < r, (rounds j).mask = Finset.univ)
    (hsuffix : ∀ j < s, (rounds (r + m + j)).mask = Finset.univ)
    (hbprefix : ∀ j, j + 1 < r → isBranchBound id (rounds j).lin B)
    (hbsuffix : ∀ j, j + 1 < s → isBranchBound id (rounds (r + m + j)).lin B) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 ≤
      scheduledWeight rounds (differenceTrace rounds x y) 0 (r + m + s) := by
  have hp := fullWindow_bound rounds hxy 0 r B (by simpa using hprefix)
    (by simpa using hbprefix)
  have hs := fullWindow_bound rounds hxy (r + m) s B hsuffix hbsuffix
  have hsplit := scheduledWeight_add rounds (differenceTrace rounds x y) 0 (r + m) s
  have hsplit' := scheduledWeight_add rounds (differenceTrace rounds x y) 0 r m
  simp only [zero_add] at hsplit hsplit'
  rw [Nat.add_mul]
  omega

/-- Instantiate the activity theorem with the full/partial/full constructor. -/
theorem hades_bound (r m s B : Nat) (mask : Finset Idx)
    (boxes : Nat → Idx → K ≃ K) (linear : Nat → (Idx → K) ≃ₗ[K] (Idx → K))
    (values : Nat → Idx → K) {x y : Idx → K} (hxy : x ≠ y)
    (hbprefix : ∀ j, j + 1 < r → isBranchBound id (linear j) B)
    (hbsuffix : ∀ j, j + 1 < s → isBranchBound id (linear (r + m + j)) B) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 ≤
      scheduledWeight (hadesSchedule r m s mask boxes linear values)
        (differenceTrace (hadesSchedule r m s mask boxes linear values) x y) 0 (r + m + s) := by
  apply outerRound_bound _ hxy r m s B
  · intro j hj
    exact hadesMask_prefix r m s mask hj
  · intro j hj
    exact hadesMask_suffix r m s mask hj
  · exact hbprefix
  · exact hbsuffix

/-- Convert the algebra layer's MDS result to the branch predicate used here. -/
theorem branch_of_mds {t : Nat} {M : Matrix (Fin t) (Fin t) K} (hM : IsMDS M)
    (L : (Fin t → K) ≃ₗ[K] (Fin t → K)) (hL : ∀ a, L a = M.mulVec a) :
    isBranchBound id L (t + 1) := by
  intro a ha
  rw [colWeight_id, colWeight_id, hL]
  exact isMDS_branch_bound hM a (by have := one_le_weight ha; omega)

/-- Whole-state MDS mixing supplies `B = t + 1`. Only transitions inside the
outer blocks need to agree with the matrix. -/
theorem hades_mds_bound {t : Nat} (r m s : Nat) (mask : Finset (Fin t))
    (boxes : Nat → Fin t → K ≃ K) (linear : Nat → (Fin t → K) ≃ₗ[K] (Fin t → K))
    (values : Nat → Fin t → K) {M : Matrix (Fin t) (Fin t) K} (hM : IsMDS M)
    (hprefix : ∀ j, j + 1 < r → ∀ a, linear j a = M.mulVec a)
    (hsuffix : ∀ j, j + 1 < s → ∀ a, linear (r + m + j) a = M.mulVec a)
    {x y : Fin t → K} (hxy : x ≠ y) :
    (r / 2 + s / 2) * (t + 1) + r % 2 + s % 2 ≤
      scheduledWeight (hadesSchedule r m s mask boxes linear values)
        (differenceTrace (hadesSchedule r m s mask boxes linear values) x y) 0 (r + m + s) :=
  hades_bound r m s (t + 1) mask boxes linear values hxy
    (fun j hj => branch_of_mds hM (linear j) (hprefix j hj))
    (fun j hj => branch_of_mds hM (linear (r + m + j)) (hsuffix j hj))

/-- Symmetric HADES has equal numbers of full rounds on its two sides. -/
theorem symmetric_bound (r m B : Nat) (mask : Finset Idx)
    (boxes : Nat → Idx → K ≃ K) (linear : Nat → (Idx → K) ≃ₗ[K] (Idx → K))
    (values : Nat → Idx → K) {x y : Idx → K} (hxy : x ≠ y)
    (hbprefix : ∀ j, j + 1 < r → isBranchBound id (linear j) B)
    (hbsuffix : ∀ j, j + 1 < r → isBranchBound id (linear (r + m + j)) B) :
    (r / 2 + r / 2) * B + r % 2 + r % 2 ≤
      scheduledWeight (hadesSchedule r m r mask boxes linear values)
        (differenceTrace (hadesSchedule r m r mask boxes linear values) x y) 0 (r + m + r) :=
  hades_bound r m r B mask boxes linear values hxy hbprefix hbsuffix

end Hades
