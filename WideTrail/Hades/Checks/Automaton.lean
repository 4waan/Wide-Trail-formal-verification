/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Automaton
import WideTrail.Hades.Checks.WindowRelation

/-!
# Checks for forward-space automaton certificates on the `ZMod 5` toy

`WideTrail.Hades.Automaton` proves that an automaton certificate that passes
`Hades.AutomatonCheck.checkAll` gives a middle bound (`MiddleBound.of_automatonCheck`), and that an
explicit trail that passes `Hades.AutomatonCheck.checkHadesTrail` is a trail in the `IsTrail`
model whose charged weight is `AutomatonCheck.trailWeight` (`isTrail_of_checkHadesTrail`,
`scheduledWeight_eq_trailWeight`). This file runs that path away from the BN254 instance, on the
toy layer `Hades.Toy.mix`, `x ↦ (x 0 + x 1, x 0 + 2 x 1)` over `ZMod 5`, with the S-box on
coordinate `0`, the layer of the checks in `WideTrail.Hades.Checks.MiddleBound` and
`WideTrail.Hades.Checks.WindowRelation`.

* `mix_eq_mat`: `mix` acts as the matrix of the table `toyRows = [[1, 1], [1, 2]]`, row `i`
  holding the coefficients of output coordinate `i`.
* `toy_automaton_check`, `toy_middleBound_automaton`: the automaton `toyStates` has two states.
  State `0`, the start, stands for every difference and has potential `1`; it goes to state `1`
  after an inactive round and to itself after an active round. State `1` stands for the multiples
  of `(1, 2)`, the differences on which the functional `(3, 1)` vanishes, and has potential `0`;
  it has no successor after an inactive round (a multiple of `(1, 2)` with coordinate `0` equal
  to `0` is `0`) and goes to state `0` after an active round. `checkAll` accepts it for every
  window `m`, so every trail through `m` consecutive rounds with `mix` and mask `{0}`, from a
  nonzero difference, charges at least `(m + 1 - 1) / 2 = m / 2` S-boxes, the window bound of
  `toy_inactive_two`. For `m = 6` this is the `3` of the relation certificate
  (`toy_middleBound_six`), and `toy_not_middleBound_six_four` shows that `3` is the largest middle
  bound for six rounds.
* `toy_start_pot_pos`: every list of states that passes `checkAll` with the toy table for five
  rounds has start potential at least `1`, since potential `0` would give
  `MiddleBound mix {0} 5 3`, which `toy_not_middleBound_five_three` refutes.
* `toy_isTrail_activity`, `toy_trail_check`, `toy_trail_isTrail`, `toy_trail_weight_general`,
  `toy_activity_attained`: for every constant table, every trail in the `IsTrail` model through
  the `2 + 4 + 2` rounds of `hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) table` (the
  schedule of `longSchedule`), from a nonzero difference, charges at least `8` S-boxes: at least
  `6` in the full rounds and at least `2` in the partial rounds, from the automaton.
  `checkHadesTrail` accepts an explicit trail through these rounds, from a nonzero difference,
  that charges exactly `8`, so `8` is the least charge over all such trails.
* Negative controls. Each table below is `toyStates` with one value changed, and `checkAll`
  returns `false` on it, by `decide +kernel`: one entry of the functional of state `1`
  (`toy_functional_rejected`); one coefficient of its inactive check (`toy_coef_rejected`); the
  start potential lowered to `0`, for five rounds (`toy_low_potential_rejected`); the successor of
  state `0` after an inactive round moved to `2`, which is not a state
  (`toy_out_of_range_rejected`); and the depth of state `1` raised to `6`, for six rounds, which
  would exempt its transitions from the check (`toy_deep_rejected`). The last two are caught only
  by the range check and by the depth check: a model of the checker without that check accepts
  them (this was checked outside Lean and is not a theorem here). `checkAll` also rejects the
  certificate with state `1`, which has a functional, as the start (`toy_start_rejected`), and
  `checkHadesTrail` rejects the trail with one entry changed (`toy_trail_rejected`).

The certificate data were computed outside Lean from the literals of `WideTrail.Hades.Checks.Toy`
(the matrix `!![1, 1; 1, 2]` and `mix`) and the schedule of `longSchedule`; nothing depends on how
they were found, since the checks are complete. The axiom footprints of the results are pinned at
the end of the file.

## What is not claimed

The bounds are lower bounds on charged S-boxes in the `IsTrail` model for the toy layer. The
witness trail is a trail in that model; it is not claimed to be realised by an input pair with the
toy's constants (an actual pair that charges `8` is `longMinimum` of
`WideTrail.Hades.Checks.MiddleBound`). A failing check says only that the given data are not a
certificate. Nothing here concerns the BN254 instance, whose certificate is checked in
`WideTrail.Poseidon2.Checks.BN254MiddleSharp`.
-/

set_option autoImplicit false

namespace Hades.AutomatonChecks

open Hades.Toy
open Hades.AutomatonCheck (AState get mat checkInactive checkActive checkAll checkHadesTrail
  trailWeight)
open Hades.RelationCheck (ent row vec)

/-! ### The toy layer as a table -/

/-- The matrix of `mix`, as a table of rows: row `i` holds the coefficients of output
coordinate `i`. -/
def toyRows : List (List ℕ) := [[1, 1], [1, 2]]

/-- The toy matrix `!![1, 1; 1, 2]` is the matrix of `toyRows`, entry by entry. -/
theorem matrix_eq_mat : matrix = mat 5 2 toyRows := by
  ext i k
  fin_cases i <;> fin_cases k <;> decide

/-- `mix` acts as the matrix of `toyRows`. -/
theorem mix_eq_mat (v : Fin 2 → ZMod 5) : mix v = (mat 5 2 toyRows).mulVec v := by
  rw [mix_eq_mulVec, matrix_eq_mat]

/-! ### The automaton: the middle bound `m / 2` for every window -/

/-- The automaton. State `0` (no functional, potential `1`, depth `0`) goes to state `1` after an
inactive round and to itself after an active round. State `1` (the functional `(3, 1)`, potential
`0`, depth `1`) has no successor after an inactive round and goes to state `0` after an active
round. -/
def toyStates : List AState :=
  [⟨[], 1, 0, some 1, some 0, [[4]], []⟩,
    ⟨[[3, 1]], 0, 1, none, some 0, [[0, 1], [1, 2]], []⟩]

/-- The start state has potential `1`. -/
theorem toy_start_pot : (get toyStates 0).pot = 1 := by
  decide

/-- Both states pass both transition checks, by `decide +kernel`. -/
theorem toy_transitions : (List.range toyStates.length).all (fun q =>
    checkInactive 5 2 0 toyRows toyStates (get toyStates q) &&
      checkActive 5 2 0 toyRows toyStates (get toyStates q)) = true := by
  decide +kernel

/-- **The checker accepts the toy automaton for every window `m`.** -/
theorem toy_automaton_check (m : ℕ) : checkAll 5 2 0 m toyRows 0 toyStates = true := by
  have hhead : (decide (0 < toyStates.length) && (get toyStates 0).H.isEmpty &&
      decide ((get toyStates 0).depth = 0)) = true := by
    decide +kernel
  have htr := toy_transitions
  rw [List.all_eq_true] at htr
  unfold checkAll
  rw [hhead, Bool.true_and, List.all_eq_true]
  intro q hq
  rw [htr q hq, Bool.or_true]

/-- **`m` rounds charge at least `m / 2` S-boxes**, from the automaton: every trail through `m`
consecutive rounds with `mix` and mask `{0}`, from a nonzero difference, charges at least `m / 2`
S-boxes. -/
theorem toy_middleBound_automaton (m : ℕ) :
    MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) m (m / 2) := by
  have h := MiddleBound.of_automatonCheck (p := 5) mix.toLinearMap 0 m toyRows 0 toyStates
    mix_eq_mat (toy_automaton_check m)
  rwa [toy_start_pot, Nat.add_sub_cancel] at h

/-- For six rounds the automaton gives the `3` of the relation certificate
(`WindowRelationChecks.toy_middleBound_six`); `3` is the largest middle bound for six rounds
(`WindowRelationChecks.toy_not_middleBound_six_four`). -/
theorem toy_middleBound_six_automaton :
    MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 6 3 :=
  toy_middleBound_automaton 6

/-- **No automaton for five rounds has start potential `0`**: if a list of states passes
`checkAll` with the toy table for five rounds, its start state has potential at least `1`, since
potential `0` would give `MiddleBound mix {0} 5 3`, which
`WindowRelationChecks.toy_not_middleBound_five_three` refutes. -/
theorem toy_start_pot_pos (start : ℕ) (states : List AState)
    (h : checkAll 5 2 0 5 toyRows start states = true) : 1 ≤ (get states start).pot := by
  by_contra hlt
  have hz : (get states start).pot = 0 := by omega
  have hb := MiddleBound.of_automatonCheck (p := 5) mix.toLinearMap 0 5 toyRows start states
    mix_eq_mat h
  rw [hz] at hb
  exact WindowRelationChecks.toy_not_middleBound_five_three hb

/-! ### A whole schedule: `8` charged S-boxes, attained in the `IsTrail` model -/

/-- **Eight charged S-boxes for every trail, for every constant table.** Every trail in the
`IsTrail` model through the `2 + 4 + 2` rounds of the toy schedule, from a nonzero difference,
charges at least `8` S-boxes: at least `6` in the full rounds (`mix_branch`) and at least `2` in
the partial rounds (`toy_middleBound_automaton`). -/
theorem toy_isTrail_activity (table : ℕ → Fin 2 → ZMod 5) {T : ℕ → Fin 2 → ZMod 5}
    (hT : IsTrail (hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) table) T 8)
    (h0 : T 0 ≠ 0) :
    8 ≤ scheduledWeight (hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) table) T 0 8 :=
  hT.outer_middle_bound_of 2 4 2 3 2 h0
    (fun _ hj => hadesMask_prefix 2 4 2 _ hj) (fun _ hj => hadesMask_suffix 2 4 2 _ hj)
    (fun _ _ => mix_branch) (fun _ _ => mix_branch) mix.toLinearMap {0} (fun _ _ => rfl)
    (fun _ hj => hadesMask_middle 2 4 2 _ hj) (toy_middleBound_automaton 4)

/-- The differences entering the rounds of a trail through the `2 + 4 + 2` rounds. -/
def toyTrailStates : List (List ℕ) :=
  [[0, 1], [1, 2], [2, 3], [0, 3], [3, 1], [0, 1], [1, 2], [3, 0], [1, 1]]

/-- The S-box output differences of that trail. -/
def toyTrailOutputs : List (List ℕ) :=
  [[0, 1], [1, 1], [2, 3], [0, 3], [4, 1], [0, 1], [1, 2], [1, 0]]

/-- The checker accepts the trail, with `mix` in every round. -/
theorem toy_trail_check :
    checkHadesTrail 5 2 0 2 4 2 toyRows toyRows toyTrailStates toyTrailOutputs = true := by
  decide +kernel

/-- The charged weight of the trail is `8`. -/
theorem toy_trail_weight : trailWeight 5 2 0 2 4 2 toyTrailStates = 8 := by
  decide +kernel

/-- The witness trail: row `n` of `toyTrailStates`, the difference entering round `n`. -/
def toyTrail (n : ℕ) : Fin 2 → ZMod 5 :=
  vec 5 2 (row toyTrailStates n)

/-- **The witness is a trail** in the `IsTrail` model through the `8` rounds, for every constant
table (`toy_trail_check`). -/
theorem toy_trail_isTrail (table : ℕ → Fin 2 → ZMod 5) :
    IsTrail (hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) table) toyTrail 8 :=
  isTrail_of_checkHadesTrail (p := 5) (0 : Fin 2) 2 4 2 toyRows toyRows toyTrailStates
    toyTrailOutputs _ (fun _ => mix) table (fun _ _ _ v => mix_eq_mat v)
    (fun _ _ _ v => mix_eq_mat v) toy_trail_check

/-- **The witness charges exactly `8` S-boxes**, for every constant table
(`toy_trail_weight`). -/
theorem toy_trail_weight_general (table : ℕ → Fin 2 → ZMod 5) :
    scheduledWeight (hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) table) toyTrail 0
      8 = 8 :=
  (scheduledWeight_eq_trailWeight (p := 5) (0 : Fin 2) 2 4 2 toyTrailStates _ (fun _ => mix)
    table).trans toy_trail_weight

/-- The witness starts from a nonzero difference. -/
theorem toyTrail_zero_ne_zero : toyTrail 0 ≠ 0 := by
  decide +kernel

/-- **Eight is attained in the `IsTrail` model, for every constant table.** Some trail through
the `8` rounds, from a nonzero difference, charges exactly `8` S-boxes; with
`toy_isTrail_activity`, `8` is the least charge over all such trails. The trail is not claimed to
be realised by an input pair. -/
theorem toy_activity_attained (table : ℕ → Fin 2 → ZMod 5) :
    ∃ T : ℕ → Fin 2 → ZMod 5, T 0 ≠ 0 ∧
      IsTrail (hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) table) T 8 ∧
      scheduledWeight (hadesSchedule 2 4 2 {0} (fun _ _ => cube) (fun _ => mix) table) T 0 8 =
        8 :=
  ⟨toyTrail, toyTrail_zero_ne_zero, toy_trail_isTrail table, toy_trail_weight_general table⟩

/-! ### Changed certificates are rejected -/

/-- `toyStates` with entry `1` of the functional of state `1` increased by one (`1` becomes `2`);
every other entry is unchanged. -/
def toyStatesFunctional : List AState :=
  toyStates.set 1 { get toyStates 1 with
    H := (get toyStates 1).H.set 0
      (((get toyStates 1).H.getD 0 []).set 1 (((get toyStates 1).H.getD 0 []).getD 1 0 + 1)) }

/-- The changed table differs from `toyStates` in the functional of state `1`. -/
theorem toyStatesFunctional_ne : (get toyStatesFunctional 1).H ≠ (get toyStates 1).H := by
  decide +kernel

/-- **The checker rejects the changed functional.** -/
theorem toy_functional_rejected : checkAll 5 2 0 6 toyRows 0 toyStatesFunctional = false := by
  decide +kernel

/-- `toyStates` with the first coefficient of row `1` of the inactive check of state `1`
increased by one (`1` becomes `2`); every other entry is unchanged. -/
def toyStatesCoef : List AState :=
  toyStates.set 1 { get toyStates 1 with
    coef0 := (get toyStates 1).coef0.set 1
      (((get toyStates 1).coef0.getD 1 []).set 0
        (((get toyStates 1).coef0.getD 1 []).getD 0 0 + 1)) }

/-- The changed table differs from `toyStates` in the coefficients of state `1`. -/
theorem toyStatesCoef_ne : (get toyStatesCoef 1).coef0 ≠ (get toyStates 1).coef0 := by
  decide +kernel

/-- **The checker rejects the changed coefficient.** -/
theorem toy_coef_rejected : checkAll 5 2 0 6 toyRows 0 toyStatesCoef = false := by
  decide +kernel

/-- `toyStates` with the potential of the start state lowered from `1` to `0`. For five rounds it
would give the middle bound `(5 + 1 - 0) / 2 = 3`, which
`WindowRelationChecks.toy_not_middleBound_five_three` refutes. -/
def toyStatesLowPotential : List AState :=
  toyStates.set 0 { get toyStates 0 with pot := 0 }

/-- **The checker rejects the lowered start potential** for five rounds (as it must, by
`toy_start_pot_pos`). -/
theorem toy_low_potential_rejected :
    checkAll 5 2 0 5 toyRows 0 toyStatesLowPotential = false := by
  decide +kernel

/-- `toyStates` with the successor of state `0` after an inactive round moved from `1` to `2`,
which is not a state (the list has `2` states). Past the end of the list, `get` reads a state with
no functional, potential and depth `0` and no successor, whose transitions are never checked. -/
def toyStatesOutOfRange : List AState :=
  toyStates.set 0 { get toyStates 0 with next0 := some 2 }

/-- **The checker rejects the successor out of range.** -/
theorem toy_out_of_range_rejected : checkAll 5 2 0 6 toyRows 0 toyStatesOutOfRange = false := by
  decide +kernel

/-- `toyStates` with the depth of state `1` raised from `1` to `6`, which for six rounds would
exempt its transitions from the check. -/
def toyStatesDeep : List AState :=
  toyStates.set 1 { get toyStates 1 with depth := 6 }

/-- **The checker rejects the raised depth.** -/
theorem toy_deep_rejected : checkAll 5 2 0 6 toyRows 0 toyStatesDeep = false := by
  decide +kernel

/-- **The checker rejects state `1` as the start**: it has a functional and depth `1`. -/
theorem toy_start_rejected : checkAll 5 2 0 6 toyRows 1 toyStates = false := by
  decide +kernel

/-- `toyTrailStates` with entry `1` of row `3` increased by one (`3` becomes `4`); every other
entry is unchanged. -/
def toyTrailCorrupted : List (List ℕ) :=
  toyTrailStates.set 3
    ((toyTrailStates.getD 3 []).set 1 ((toyTrailStates.getD 3 []).getD 1 0 + 1))

/-- The changed trail differs from `toyTrailStates`. -/
theorem toyTrailCorrupted_ne : toyTrailCorrupted ≠ toyTrailStates := by
  decide +kernel

/-- **The trail checker rejects the changed trail.** -/
theorem toy_trail_rejected :
    checkHadesTrail 5 2 0 2 4 2 toyRows toyRows toyTrailCorrupted toyTrailOutputs = false := by
  decide +kernel

end Hades.AutomatonChecks

/-- info: 'Hades.AutomatonChecks.mix_eq_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.mix_eq_mat

/-- info: 'Hades.AutomatonChecks.toy_automaton_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_automaton_check

/-- info: 'Hades.AutomatonChecks.toy_middleBound_automaton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_middleBound_automaton

/-- info: 'Hades.AutomatonChecks.toy_start_pot_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_start_pot_pos

/-- info: 'Hades.AutomatonChecks.toy_isTrail_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_isTrail_activity

/-- info: 'Hades.AutomatonChecks.toy_trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_trail_check

/-- info: 'Hades.AutomatonChecks.toy_trail_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_trail_weight

/-- info: 'Hades.AutomatonChecks.toy_trail_isTrail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_trail_isTrail

/-- info: 'Hades.AutomatonChecks.toy_trail_weight_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_trail_weight_general

/-- info: 'Hades.AutomatonChecks.toy_activity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_activity_attained

/-- info: 'Hades.AutomatonChecks.toy_functional_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_functional_rejected

/-- info: 'Hades.AutomatonChecks.toy_coef_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_coef_rejected

/-- info: 'Hades.AutomatonChecks.toy_low_potential_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_low_potential_rejected

/-- info: 'Hades.AutomatonChecks.toy_out_of_range_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_out_of_range_rejected

/-- info: 'Hades.AutomatonChecks.toy_deep_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_deep_rejected

/-- info: 'Hades.AutomatonChecks.toy_start_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_start_rejected

/-- info: 'Hades.AutomatonChecks.toy_trail_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonChecks.toy_trail_rejected
