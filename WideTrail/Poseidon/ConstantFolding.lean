/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Schedule

/-!
# Folding round constants through the linear layers

Implementations of the original Poseidon often add, in a partial round, only the constant of
the S-box coordinate, and push the constants of the other coordinates forward through the linear
layer into the constants of later rounds (the "optimised" or compressed constants). This file
proves, for arbitrary scheduled rounds, that such a rewriting does not change the computed
function.

The masked S-box layer acts as the identity off its mask, so adding a vector `e` that is zero on
the mask commutes with it (`maskedEquiv_add_of_eq_zero`). Hence a round with constant `c' + e`
is the round with constant `c'` followed by adding `L e`, where `L` is the round's linear layer
(`RoundSpec.apply_add_of_eq_zero`), and `L e` can be absorbed into the next round's constant.

## Results

* `execute_eq_add_of_fold`: let two schedules `rounds` and `rounds'` agree in masks, S-boxes and
  linear layers in the first `N` rounds, and let `δ : ℕ → (Idx → K)` be offsets with `δ 0 = 0`
  such that, for every `n < N`, `e n = constant n + δ n - constant' n` is zero on the mask of
  round `n` and `δ (n + 1) = lin n (e n)`. Then for every input `x` and every `n ≤ N`, the state
  of `rounds` after `n` rounds is the state of `rounds'` plus `δ n`.
* `execute_eq_of_fold`: if moreover `δ N = 0`, the two schedules compute the same function in
  `N` rounds.
* `hadesSchedule_execute_eq_of_fold`: the same for two `Hades.hadesSchedule`s that differ only
  in their tables of constants.

## What is not claimed

This is a statement about the functions computed. It says nothing about any particular
compressed table, which must be checked separately, and nothing about the independent-key
model: adding a key to every coordinate of every round is not preserved by the rewriting.
-/

set_option autoImplicit false

namespace Poseidon

variable {Idx K : Type*} [DecidableEq Idx] [Field K]

/-- **The masked layer commutes with adding a vector that is zero on the mask.** -/
theorem maskedEquiv_add_of_eq_zero (mask : Finset Idx) (s : Idx → K ≃ K) (y e : Idx → K)
    (he : ∀ i ∈ mask, e i = 0) :
    Hades.maskedEquiv mask s (y + e) = Hades.maskedEquiv mask s y + e := by
  funext i
  simp only [Hades.maskedEquiv_apply, Hades.maskedBricklayer_apply, Pi.add_apply]
  by_cases hi : i ∈ mask
  · rw [if_pos hi, if_pos hi, he i hi, add_zero, add_zero]
  · rw [if_neg hi, if_neg hi]

/-- **One folding step.** If `e` is zero on the mask of `R`, applying `R` to `y + e` is applying
it to `y` and then adding `R.lin e`. -/
theorem RoundSpec.apply_add_of_eq_zero (R : Hades.RoundSpec Idx K) (y e : Idx → K)
    (he : ∀ i ∈ R.mask, e i = 0) : R.apply (y + e) = R.apply y + R.lin e := by
  simp only [Hades.RoundSpec.apply]
  rw [add_right_comm, maskedEquiv_add_of_eq_zero R.mask R.sbox _ e he, map_add]

/-- **Constant folding.** Let `rounds` and `rounds'` agree in masks, S-boxes and linear layers
in the first `N` rounds, and let `δ` be offsets with `δ 0 = 0` such that, for every `n < N`,
`e n = (rounds n).constant + δ n - (rounds' n).constant` is zero on the mask of round `n` and
`δ (n + 1) = (rounds n).lin (e n)`. Then after every `n ≤ N` rounds, the state of `rounds` is
the state of `rounds'` plus `δ n`, for every input. -/
theorem execute_eq_add_of_fold (rounds rounds' : ℕ → Hades.RoundSpec Idx K)
    (δ : ℕ → Idx → K) (N : ℕ) (hmask : ∀ n < N, (rounds' n).mask = (rounds n).mask)
    (hsbox : ∀ n < N, (rounds' n).sbox = (rounds n).sbox)
    (hlin : ∀ n < N, (rounds' n).lin = (rounds n).lin) (h0 : δ 0 = 0)
    (hzero : ∀ n < N, ∀ i ∈ (rounds n).mask,
      ((rounds n).constant + δ n - (rounds' n).constant) i = 0)
    (hnext : ∀ n < N,
      δ (n + 1) = (rounds n).lin ((rounds n).constant + δ n - (rounds' n).constant))
    (x : Idx → K) {n : ℕ} (hn : n ≤ N) :
    Hades.execute rounds x n = Hades.execute rounds' x n + δ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hlt : n < N := by omega
    rw [Hades.execute_succ, Hades.execute_succ, ih (by omega)]
    set y := Hades.execute rounds' x n
    set e := (rounds n).constant + δ n - (rounds' n).constant
    have hsplit : y + δ n + (rounds n).constant = (y + (rounds' n).constant) + e := by
      simp only [e]
      abel
    have happly : (rounds n).apply (y + δ n) = (rounds' n).apply y + (rounds n).lin e := by
      simp only [Hades.RoundSpec.apply]
      rw [hsplit, maskedEquiv_add_of_eq_zero (rounds n).mask (rounds n).sbox _ e
        (hzero n hlt), map_add, hmask n hlt, hsbox n hlt, hlin n hlt]
    rw [happly, hnext n hlt]

/-- **Constant folding, whole schedule.** Under the hypotheses of `execute_eq_add_of_fold` and
`δ N = 0`, the two schedules compute the same function in `N` rounds. -/
theorem execute_eq_of_fold (rounds rounds' : ℕ → Hades.RoundSpec Idx K) (δ : ℕ → Idx → K)
    (N : ℕ) (hmask : ∀ n < N, (rounds' n).mask = (rounds n).mask)
    (hsbox : ∀ n < N, (rounds' n).sbox = (rounds n).sbox)
    (hlin : ∀ n < N, (rounds' n).lin = (rounds n).lin) (h0 : δ 0 = 0) (hN : δ N = 0)
    (hzero : ∀ n < N, ∀ i ∈ (rounds n).mask,
      ((rounds n).constant + δ n - (rounds' n).constant) i = 0)
    (hnext : ∀ n < N,
      δ (n + 1) = (rounds n).lin ((rounds n).constant + δ n - (rounds' n).constant))
    (x : Idx → K) : Hades.execute rounds x N = Hades.execute rounds' x N := by
  rw [execute_eq_add_of_fold rounds rounds' δ N hmask hsbox hlin h0 hzero hnext x le_rfl, hN,
    add_zero]

/-- **Constant folding for HADES schedules.** Two `Hades.hadesSchedule`s with the same masks,
S-boxes and linear layers and constant tables `table` and `table'` compute the same function in
`N` rounds, if offsets `δ` with `δ 0 = 0` and `δ N = 0` satisfy, for every `n < N`: the vector
`table n + δ n - table' n` is zero on the mask of round `n`, and `δ (n + 1)` is its image under
`linear n`. -/
theorem hadesSchedule_execute_eq_of_fold [Fintype Idx] (r m s : ℕ) (mask : Finset Idx)
    (boxes : ℕ → Idx → K ≃ K) (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K))
    (table table' : ℕ → Idx → K) (δ : ℕ → Idx → K) (N : ℕ) (h0 : δ 0 = 0)
    (hN : δ N = 0)
    (hzero : ∀ n < N, ∀ i ∈ Hades.hadesMask r m s mask n, (table n + δ n - table' n) i = 0)
    (hnext : ∀ n < N, δ (n + 1) = linear n (table n + δ n - table' n)) (x : Idx → K) :
    Hades.execute (Hades.hadesSchedule r m s mask boxes linear table) x N =
      Hades.execute (Hades.hadesSchedule r m s mask boxes linear table') x N :=
  execute_eq_of_fold (Hades.hadesSchedule r m s mask boxes linear table)
    (Hades.hadesSchedule r m s mask boxes linear table') δ N (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) h0 hN hzero hnext x

end Poseidon
