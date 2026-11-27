/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.MiddleBound
import WideTrail.Hades.Checks.Toy

/-!
# Checks for the middle-bound interface

`WideTrail.Hades.MiddleBound` takes a lower bound on the partial rounds as a hypothesis,
`Hades.MiddleBound A mask m μ`. This file checks that the interface reproduces the window
theorems and that the predicate can fail. It imports only `WideTrail.Hades` modules; the
re-derivation of the KoalaBear and BN254 counts through the interface is in
`WideTrail.Poseidon2.Checks.MiddleBound`.

* `outer_middle_bound_via_interface`, `hades_probability_with_middle_exact_via_interface`: the
  window theorems `Hades.IsTrail.outer_middle_bound` and
  `Hades.hades_probability_with_middle_exact`, with their statements unchanged, re-derived from
  `Hades.IsTrail.outer_middle_bound_of`, `Hades.hades_probability_with_middle_bound_exact` and
  `Hades.MiddleBound.of_inactiveSpace` at `μ = m / w`.
* A `ZMod 5` toy (the layer `Hades.Toy.mix`, `x ↦ (x 0 + x 1, x 0 + 2 x 1)`, mask `{0}`):
  `toy_middleBound_two` proves `MiddleBound mix {0} 2 1` from the definition, without
  `inactiveSpace`; `toy_middleBound_four` adds two copies. `toy_not_middleBound_one`,
  `toy_not_middleBound_two`, `toy_not_middleBound_four` exhibit actual executions through `1`,
  `2` and `4` partial rounds charging `0`, `1` and `2` S-boxes, so `MiddleBound mix {0} 1 1`,
  `MiddleBound mix {0} 2 2` and `MiddleBound mix {0} 4 3` fail. `toy_window_four` gets the same
  `2` for four rounds from the window argument. `longBound` charges the schedule with two full
  rounds, four partial rounds and two full rounds at least `6 + 2 = 8` S-boxes for every pair of
  distinct inputs; `longBound_scan` checks the same in the kernel for each of the `600` ordered
  pairs of distinct inputs, without the interface, and `longMinimum` shows that one pair charges
  exactly `8`.
* `zero_map_vacuous`: for a map that no round can have (here `0`), `MiddleBound` holds for every
  `μ`. This is the caveat stated in `WideTrail.Hades.MiddleBound`.

The axiom footprints of the results are pinned at the end of the file.

## What is not claimed

The re-derived window theorems are the existing lower bounds, unchanged; nothing here improves
them. The toy schedules use the toy's constants `Hades.Toy.values`; one execution with those
constants refutes a middle bound, because `MiddleBound` quantifies over all rounds with the given
linear map and mask. The probability statements concern one trail in the model with an additional
independent uniform key per round: not the permutations with their fixed constants, and not a
differential.
-/

set_option autoImplicit false

namespace Hades.MiddleBoundChecks

/-! ### The window theorems are the case `μ = m / w` -/

section Generic

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- `Hades.IsTrail.outer_middle_bound`, with its statement unchanged, from
`Hades.IsTrail.outer_middle_bound_of` and `Hades.MiddleBound.of_inactiveSpace`. -/
theorem outer_middle_bound_via_interface {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K}
    (r m s B w : ℕ) (hT : IsTrail rounds T (r + m + s)) (h0 : T 0 ≠ 0)
    (hp : ∀ j < r, (rounds j).mask = Finset.univ)
    (hs : ∀ j < s, (rounds (r + m + j)).mask = Finset.univ)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (rounds j).lin B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (rounds (r + m + j)).lin B)
    (L : (Idx → K) ≃ₗ[K] (Idx → K)) (mask : Finset Idx)
    (hlin : ∀ j < m, (rounds (r + j)).lin = L)
    (hmask : ∀ j < m, (rounds (r + j)).mask = mask)
    (htriv : inactiveSpace L.toLinearMap mask w = ⊥) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 + m / w ≤ scheduledWeight rounds T 0 (r + m + s) :=
  hT.outer_middle_bound_of r m s B (m / w) h0 hp hs hbp hbs L.toLinearMap mask
    (fun j hj => by rw [hlin j hj]) hmask (MiddleBound.of_inactiveSpace htriv m)

variable [Fintype K]

/-- `Hades.hades_probability_with_middle_exact`, with its statement unchanged, from
`Hades.hades_probability_with_middle_bound_exact` and `Hades.MiddleBound.of_inactiveSpace`. -/
theorem hades_probability_with_middle_exact_via_interface (r m s B w : ℕ) (mask : Finset Idx)
    (boxes : ℕ → Idx → K ≃ K) (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K))
    (values : ℕ → Idx → K) {u : ℕ}
    (hu : ∀ n < r + m + s, ∀ i, IsDiffUniform (boxes n i) u)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (linear j) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (linear (r + m + j)) B)
    (L : (Idx → K) ≃ₗ[K] (Idx → K)) (hmid : ∀ j < m, linear (r + j) = L)
    (htriv : inactiveSpace L.toLinearMap mask w = ⊥)
    {T : ℕ → Idx → K} (h0 : T 0 ≠ 0) (x : Idx → K) :
    keyCount (hadesSchedule r m s mask boxes linear values) (r + m + s) T x
      * Fintype.card K ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + m / w)
      ≤ u ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + m / w)
        * Fintype.card (Idx → K) ^ (r + m + s) :=
  hades_probability_with_middle_bound_exact r m s B (m / w) mask boxes linear values hu hbp hbs
    L.toLinearMap (fun j hj => by rw [hmid j hj]) (MiddleBound.of_inactiveSpace htriv m) h0 x

end Generic

/-! ### A `ZMod 5` toy: a middle bound shown from the definition -/

section Toy

open Hades.Toy

/-- **Two partial rounds charge at least one S-box**, from the definition of `MiddleBound`: if
both rounds were inactive, the first would act as `mix`, so `T 1 0 = T 0 0 + T 0 1 = T 0 1`, and
`T 0 0 = T 1 0 = 0` would force `T 0 = 0`. -/
theorem toy_middleBound_two : MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 2 1 := by
  intro rounds T hT h0 hlin hmask
  by_contra hcon
  have hz : scheduledWeight rounds T 0 2 = 0 := by omega
  simp only [scheduledWeight, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    hmask 0 (by norm_num), hmask 1 (by norm_num), sboxWeight_singleton] at hz
  have hz0 : T 0 0 = 0 := by
    by_contra hne
    simp [hne] at hz
  have hz1 : T 1 0 = 0 := by
    by_contra hne
    simp [hne] at hz
  have hstep := hT.succ_of_inactive (n := 0) (by norm_num) (by
    rw [hmask 0 (by norm_num)]
    intro i hi
    rw [Finset.mem_singleton.mp hi]
    exact hz0)
  have hmix : (rounds 0).lin (T 0) = mix (T 0) :=
    LinearMap.congr_fun (hlin 0 (by norm_num)) (T 0)
  have h10 : T 1 0 = T 0 0 + T 0 1 := by
    rw [hstep, hmix]
    rfl
  apply h0
  funext i
  fin_cases i
  · exact hz0
  · change T 0 1 = 0
    rw [hz0, zero_add, hz1] at h10
    exact h10.symm

/-- Four partial rounds charge at least two S-boxes: two copies of `toy_middleBound_two`. -/
theorem toy_middleBound_four : MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 4 2 :=
  toy_middleBound_two.add toy_middleBound_two

/-- No nonzero difference stays inactive through two consecutive partial rounds with `mix`. -/
theorem toy_inactive_two : inactiveSpace mix.toLinearMap ({0} : Finset (Fin 2)) 2 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  have h0 : a 0 = 0 := by simpa using ha 0 (by norm_num) 0 (by simp)
  have h1 : a 0 + a 1 = 0 := by simpa [mix] using ha 1 (by norm_num) 0 (by simp)
  funext i
  fin_cases i
  · exact h0
  · change a 1 = 0
    rw [h0, zero_add] at h1
    exact h1

/-- The window argument gives the same `4 / 2 = 2` for four rounds. -/
theorem toy_window_four : MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 4 (4 / 2) :=
  MiddleBound.of_inactiveSpace toy_inactive_two 4

/-- Partial rounds only: mask `{0}`, the S-box `cube`, the layer `mix`, the toy's constants. -/
def partialRounds : ℕ → RoundSpec (Fin 2) (ZMod 5) :=
  fun n => ⟨{0}, fun _ => cube, mix, values n⟩

/-- An actual execution: `![0, 0]` and `![0, 1]` charge no S-box in the first partial round. -/
theorem toy_execution_one :
    scheduledWeight partialRounds (differenceTrace partialRounds ![0, 0] ![0, 1]) 0 1 = 0 := by
  decide

/-- An actual execution: `![0, 0]` and `![0, 1]` charge one S-box in two partial rounds. -/
theorem toy_execution_two :
    scheduledWeight partialRounds (differenceTrace partialRounds ![0, 0] ![0, 1]) 0 2 = 1 := by
  decide

/-- An actual execution: `![0, 0]` and `![0, 2]` charge two S-boxes in four partial rounds. -/
theorem toy_execution_four :
    scheduledWeight partialRounds (differenceTrace partialRounds ![0, 0] ![0, 2]) 0 4 = 2 := by
  decide

/-- A middle bound fails as soon as one actual execution charges less. -/
theorem not_middleBound_of_execution {m μ : ℕ} {x y : Fin 2 → ZMod 5} (hxy : x ≠ y)
    (h : scheduledWeight partialRounds (differenceTrace partialRounds x y) 0 m < μ) :
    ¬ MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) m μ := fun hμ =>
  absurd (hμ partialRounds _ (differenceTrace_isTrail partialRounds x y m)
    (differenceTrace_ne_zero partialRounds hxy 0) (fun _ _ => rfl) (fun _ _ => rfl))
    (Nat.not_le.mpr h)

/-- One partial round need not charge anything. -/
theorem toy_not_middleBound_one : ¬ MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 1 1 :=
  not_middleBound_of_execution (x := ![0, 0]) (y := ![0, 1]) (by decide)
    (by rw [toy_execution_one]; norm_num)

/-- `toy_middleBound_two` is the largest bound for two rounds. -/
theorem toy_not_middleBound_two : ¬ MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 2 2 :=
  not_middleBound_of_execution (x := ![0, 0]) (y := ![0, 1]) (by decide)
    (by rw [toy_execution_two]; norm_num)

/-- `toy_middleBound_four` is the largest bound for four rounds. -/
theorem toy_not_middleBound_four : ¬ MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 4 3 :=
  not_middleBound_of_execution (x := ![0, 0]) (y := ![0, 2]) (by decide)
    (by rw [toy_execution_four]; norm_num)

/-- Two full rounds, four partial rounds, two full rounds, over the toy. -/
def longSchedule : ℕ → RoundSpec (Fin 2) (ZMod 5) :=
  hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) values

/-- The charged S-boxes of two executions of `longSchedule`. -/
def longCount (x y : Fin 2 → ZMod 5) : ℕ :=
  scheduledWeight longSchedule (differenceTrace longSchedule x y) 0 8

/-- **Eight active S-boxes**: `6` in the full rounds and `2` from `toy_middleBound_four`. -/
theorem longBound {x y : Fin 2 → ZMod 5} (hxy : x ≠ y) : 8 ≤ longCount x y :=
  outer_middle_bound_of longSchedule hxy 2 4 2 3 2
    (fun _ hj => hadesMask_prefix 2 4 2 _ hj) (fun _ hj => hadesMask_suffix 2 4 2 _ hj)
    (fun _ _ => mix_branch) (fun _ _ => mix_branch) mix.toLinearMap {0} (fun _ _ => rfl)
    (fun _ hj => hadesMask_middle 2 4 2 _ hj) toy_middleBound_four

/-- One pair charges exactly `8`, so `longBound` is attained. -/
theorem longMinimum : longCount ![0, 0] ![2, 2] = 8 := by decide

set_option maxHeartbeats 8000000 in
-- One fifth of the scan, split so that each `decide` stays small.
/-- The scan of `longBound_scan` for first inputs with `x 0 = 0`. -/
theorem longScan0 :
    ∀ b : ZMod 5, ∀ y : Fin 2 → ZMod 5, ![0, b] ≠ y → 8 ≤ longCount ![0, b] y := by
  decide

set_option maxHeartbeats 8000000 in
-- One fifth of the scan, split so that each `decide` stays small.
/-- The scan of `longBound_scan` for first inputs with `x 0 = 1`. -/
theorem longScan1 :
    ∀ b : ZMod 5, ∀ y : Fin 2 → ZMod 5, ![1, b] ≠ y → 8 ≤ longCount ![1, b] y := by
  decide

set_option maxHeartbeats 8000000 in
-- One fifth of the scan, split so that each `decide` stays small.
/-- The scan of `longBound_scan` for first inputs with `x 0 = 2`. -/
theorem longScan2 :
    ∀ b : ZMod 5, ∀ y : Fin 2 → ZMod 5, ![2, b] ≠ y → 8 ≤ longCount ![2, b] y := by
  decide

set_option maxHeartbeats 8000000 in
-- One fifth of the scan, split so that each `decide` stays small.
/-- The scan of `longBound_scan` for first inputs with `x 0 = 3`. -/
theorem longScan3 :
    ∀ b : ZMod 5, ∀ y : Fin 2 → ZMod 5, ![3, b] ≠ y → 8 ≤ longCount ![3, b] y := by
  decide

set_option maxHeartbeats 8000000 in
-- One fifth of the scan, split so that each `decide` stays small.
/-- The scan of `longBound_scan` for first inputs with `x 0 = 4`. -/
theorem longScan4 :
    ∀ b : ZMod 5, ∀ y : Fin 2 → ZMod 5, ![4, b] ≠ y → 8 ≤ longCount ![4, b] y := by
  decide

/-- **`longBound` by an exhaustive scan**: every ordered pair of distinct inputs, executed through
the `8` rounds of `longSchedule` in the kernel, without `MiddleBound`. -/
theorem longBound_scan : ∀ x y : Fin 2 → ZMod 5, x ≠ y → 8 ≤ longCount x y := by
  intro x y hxy
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hxy ⊢
  generalize x 1 = b at hxy ⊢
  generalize x 0 = a at hxy ⊢
  fin_cases a
  · exact longScan0 b y hxy
  · exact longScan1 b y hxy
  · exact longScan2 b y hxy
  · exact longScan3 b y hxy
  · exact longScan4 b y hxy

end Toy

/-! ### The caveat: a map that no round has -/

/-- If no round can have the linear map `A`, `MiddleBound A mask m μ` holds for every `μ` once
`m ≥ 1`. Here `A = 0` on `Fin 2 → ZMod 5`: a linear equivalence is injective, so its linear map
is not `0`. -/
theorem zero_map_vacuous (mask : Finset (Fin 2)) (μ : ℕ) :
    MiddleBound (0 : Module.End (ZMod 5) (Fin 2 → ZMod 5)) mask 1 μ := by
  intro rounds T _ _ hlin _
  exfalso
  have h : (rounds 0).lin (Pi.single 0 1) = 0 := by
    simpa using LinearMap.congr_fun (hlin 0 (by norm_num)) (Pi.single 0 1)
  rw [LinearEquiv.map_eq_zero_iff] at h
  exact absurd (congrFun h 0) (by decide)

end Hades.MiddleBoundChecks

/-- info: 'Hades.MiddleBound.apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.apply

/-- info: 'Hades.MiddleBound.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.add

/-- info: 'Hades.MiddleBound.of_inactiveSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.of_inactiveSpace

/-- info: 'Hades.MiddleBound.smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.smul

/-- info: 'Hades.MiddleBound.diagPlusOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.diagPlusOnes

/-- info: 'Hades.IsTrail.outer_middle_bound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.IsTrail.outer_middle_bound_of

/-- info: 'Hades.outer_middle_bound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.outer_middle_bound_of

/-- info: 'Hades.hades_probability_with_middle_bound_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_probability_with_middle_bound_exact

/-- info: 'Hades.hades_probability_with_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_probability_with_middle_bound

/-- info: 'Hades.MiddleBoundChecks.outer_middle_bound_via_interface' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.outer_middle_bound_via_interface

/--
info: 'Hades.MiddleBoundChecks.hades_probability_with_middle_exact_via_interface' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.hades_probability_with_middle_exact_via_interface

/-- info: 'Hades.MiddleBoundChecks.toy_middleBound_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.toy_middleBound_four

/-- info: 'Hades.MiddleBoundChecks.toy_not_middleBound_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.toy_not_middleBound_four

/-- info: 'Hades.MiddleBoundChecks.longBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.longBound

/-- info: 'Hades.MiddleBoundChecks.longBound_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.longBound_scan

/-- info: 'Hades.MiddleBoundChecks.longMinimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.longMinimum

/-- info: 'Hades.MiddleBoundChecks.zero_map_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBoundChecks.zero_map_vacuous
