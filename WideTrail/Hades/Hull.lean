/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Probability
import WideTrail.Differential.Hull

/-!
# Differentials of scheduled rounds in the additional-independent-key model

`Probability.lean` bounds the key count of one trail through the HADES rounds. This file bounds a
differential, the sum over all trails from an input difference `a` to an output difference `b`,
in the same model: round `n` is `x ↦ lin n (maskedSbox n (x + k n + constant n))`, with fixed
round constants and an additional independent uniform key `k n` per round.

`diffKeyCount rounds R a b x` is `Scheduled.diffKeyCount` for the rounds' maps `roundGamma` and
linear layers: the number of key vectors `k : Fin R → (Idx → K)` under which the pair
`(x, x + a)` has output difference `b` after `R` rounds. Divided by `|Idx → K| ^ R` it is the
key-averaged probability of the differential `(a, b)`; it does not depend on `x`
(`Scheduled.diffKeyCount_const`).

## Results

* `diffKeyCount_bound_of_two_full_rounds`: if rounds `j` and `j + 1` of the first `R` are full
  (every coordinate an S-box), their S-boxes have differential uniformity at most `u`, and the
  linear layer of round `j` has branch number at least `B`, then for `a ≠ 0`,
  `diffKeyCount rounds R a b x * |K| ^ (B - 1) ≤ u ^ (B - 1) * |Idx → K| ^ R`. Every round is
  bijective (`roundGamma_bijective`), which is all the other rounds contribute.
* `hades_differential_bound`: the same for a `hadesSchedule` with at least two full rounds at
  the start, charging rounds `0` and `1`.

The proof is `Scheduled.diffKeyCount_bound_of_two_rounds`: the fixed constant is absorbed by
`diffCount_addKey`, and a full masked layer has bricklayer counts (`diffCount_roundGamma_of_full`).

## What is not claimed

The bound concerns the key-averaged differential over an additional independent uniform key per
round. It says nothing about the permutation with its fixed round constants. Only two full
rounds are charged; the trail bound `hades_probability_exact` charges more S-boxes, but for one
trail only. Partial rounds are not charged here.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Hades

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K] [Fintype K]

/-- The number of key vectors `k : Fin R → (Idx → K)` under which the input pair `(x, x + a)` has
output difference `b` after the first `R` rounds of `rounds`, each round adding its fixed
constant and an additional key `k n` before its masked S-box layer. -/
def diffKeyCount (rounds : ℕ → RoundSpec Idx K) (R : ℕ) (a b x : Idx → K) : ℕ :=
  Scheduled.diffKeyCount (fun n => (rounds n).lin.toAddEquiv) (fun n => roundGamma (rounds n))
    R a b x

omit [Fintype Idx] [DecidableEq K] [Fintype K] in
/-- The nonlinear part of a round, the fixed constant then the masked S-box layer, is
bijective. -/
theorem roundGamma_bijective (R : RoundSpec Idx K) : Function.Bijective (roundGamma R) :=
  (maskedEquiv R.mask R.sbox).bijective.comp (Equiv.addRight R.constant).bijective

/-- A full round has bricklayer differential counts: the fixed constant does not change them
(`diffCount_addKey`), and every coordinate is an S-box. -/
theorem diffCount_roundGamma_of_full (R : RoundSpec Idx K) (hR : R.mask = Finset.univ)
    (a b : Idx → K) :
    diffCount (roundGamma R) a b = ∏ i, diffCount (R.sbox i) (a i) (b i) := by
  rw [show diffCount (roundGamma R) a b =
      diffCount (maskedBricklayer R.mask (fun i => R.sbox i)) a b from diffCount_addKey _ _ _ _,
    diffCount_masked, hR]
  simp

/-- **Two full rounds bound the differential.** If rounds `j` and `j + 1` of the first `R` are
full, their S-boxes have differential uniformity at most `u`, and the linear layer of round `j`
has branch number at least `B`, then for every nonzero input difference `a`,
`diffKeyCount rounds R a b x * |K| ^ (B - 1) ≤ u ^ (B - 1) * |Idx → K| ^ R`. This concerns the
differential averaged over an additional independent uniform key per round, not the fixed round
constants alone. -/
theorem diffKeyCount_bound_of_two_full_rounds (rounds : ℕ → RoundSpec Idx K) (R j B : ℕ)
    (hj : j + 2 ≤ R) (hfull : ∀ n, j ≤ n → n < j + 2 → (rounds n).mask = Finset.univ) {u : ℕ}
    (hu : ∀ n, j ≤ n → n < j + 2 → ∀ i, IsDiffUniform ((rounds n).sbox i) u)
    (hB : isBranchBound id (rounds j).lin B) {a : Idx → K} (ha : a ≠ 0) (b x : Idx → K) :
    diffKeyCount rounds R a b x * Fintype.card K ^ (B - 1)
      ≤ u ^ (B - 1) * Fintype.card (Idx → K) ^ R := by
  have hB' : isBranchBound id (rounds j).lin.toAddEquiv B := by
    rw [LinearEquiv.coe_toAddEquiv]
    exact hB
  exact Scheduled.diffKeyCount_bound_of_two_rounds (fun n => (rounds n).lin.toAddEquiv)
    (fun n => roundGamma (rounds n)) (fun n i => (rounds n).sbox i) R j hj
    (fun n _ => roundGamma_bijective (rounds n))
    (fun n hn hn' => diffCount_roundGamma_of_full (rounds n) (hfull n hn hn'))
    (fun n _ _ i => ((rounds n).sbox i).bijective) hu hB' ha b x

/-- **The differential bound for a HADES schedule.** For a `hadesSchedule` with at least two
full rounds at the start, if the S-boxes of rounds `0` and `1` have differential uniformity at
most `u` and the linear layer of round `0` has branch number at least `B`, then for every
nonzero input difference `a`,
`diffKeyCount * |K| ^ (B - 1) ≤ u ^ (B - 1) * |Idx → K| ^ (r + m + s)`. That is, every
differential with a nonzero input difference has key-averaged probability at most
`(u / |K|) ^ (B - 1)`, in the model with an additional independent uniform key per round. It
says nothing about the fixed round constants alone. -/
theorem hades_differential_bound (r m s B : ℕ) (hr : 2 ≤ r) (mask : Finset Idx)
    (boxes : ℕ → Idx → K ≃ K) (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K)) (values : ℕ → Idx → K)
    {u : ℕ} (hu : ∀ n < 2, ∀ i, IsDiffUniform (boxes n i) u)
    (hB : isBranchBound id (linear 0) B) {a : Idx → K} (ha : a ≠ 0) (b x : Idx → K) :
    diffKeyCount (hadesSchedule r m s mask boxes linear values) (r + m + s) a b x
      * Fintype.card K ^ (B - 1) ≤ u ^ (B - 1) * Fintype.card (Idx → K) ^ (r + m + s) :=
  diffKeyCount_bound_of_two_full_rounds (hadesSchedule r m s mask boxes linear values)
    (r + m + s) 0 B (by omega) (fun n _ hn => hadesMask_prefix r m s mask (by omega))
    (fun n _ hn => hu n hn) hB ha b x

end Hades
