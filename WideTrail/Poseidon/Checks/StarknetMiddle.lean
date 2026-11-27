/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon.StarknetMiddle

/-!
# Checks for the Starknet middle bound

`WideTrail.Poseidon.StarknetMiddle` proves, by a forward-space automaton certificate, that every
trail through the `83` partial rounds of Starknet's Poseidon permutation charges at least `41`
S-boxes, hence `57` charged S-boxes in all and the exponent `14250` (exact ratio and whole bits
alike). The checks below show that `41` is the largest middle bound for these rounds, that `57`
is attained by a trail in the `IsTrail` model, that `14250` is the largest exponent the arithmetic
gives for `57` charged S-boxes, in both forms, and that the checker rejects changed certificates.
Every finite check is `decide` or `decide +kernel`.

## Exactness

* `middle_bound_not_forty_two`, `middle_bound_diag_not_forty_two`: `42` is not a middle bound for
  `83` rounds with `M` (`diag (2, -2, -3) + J`) and mask `{2}`. The witness is the trail
  `middleStates`, `middleOutputs` of the certificate file, a trail through `83` rounds with that
  linear map and mask from a nonzero difference, checked by `RelationCheck.checkTrail`
  (`middle_trail_check`). Its active rounds are exactly the odd rounds from `1` to `81`
  (`middle_trail_pattern`): the first round is inactive, then active and inactive rounds
  alternate; so exactly `41` of its rounds are active (`middle_trail_active`).
* `trail_isTrail_general`, `trail_weight_general`, `activity_attained_general`,
  `activity_attained`: the rows of `trailStates` are a trail in the `IsTrail` model through the
  `91` rounds of the schedule, for every round-constant table, from a nonzero difference, and
  they charge exactly `57` S-boxes. With `isTrail_activity_middle_general`, `57` is the least
  number of charged S-boxes over all trails in the `IsTrail` model through these rounds, so no
  argument that uses only `IsTrail` proves more. The trail is not claimed to be realised by an
  input pair or a key.
* `middle_sharp_exponent_succ_fails`: `2^14251 * 2^57 ≤ p^57` fails, so `14250` is the largest
  exponent the exact ratio gives for `57` charged S-boxes.
* `bits_251_too_large`, `whole_bit_exponent_le`: `2 * 2^251 > p`, so every whole number `dd` of
  bits per charged S-box with `2 * 2^dd ≤ p` has `dd * 57 ≤ 14250`.

## Negative controls

Each table below is `states` with one value changed, and `AutomatonCheck.checkAll` returns
`false` on it, by `decide +kernel`:

* `statesCorrupted`: the first coefficient of the inactive transition of state `1` increased by
  one (`corrupted_rejected`);
* `statesLowPotential`: the potential of the start state lowered from `2` to `0`, which would give
  the bound `(83 + 1 - 0) / 2 = 42` that `middle_bound_not_forty_two` refutes
  (`low_potential_rejected`).

## What is not claimed

These checks concern the `IsTrail` model and the arithmetic of the exponents. They do not show that
`57` is the least number of S-boxes an actual input pair incurs, that the witness trails are
realised by input pairs or keys, or anything about the permutation with its fixed constants
beyond the statements of the results file. The axiom footprints of the new theorems are pinned at
the end of the file.
-/

set_option autoImplicit false

namespace Poseidon.Starknet.MiddleChecks

open Poseidon.Certificates.Starknet (fieldModulus mdsRows mdsDiagonal states trailStates
  trailSboxOutputs middleStates middleOutputs trail_check trail_weight middle_trail_check)

open Hades.RelationCheck (ent row vec)

/-! ### The middle bound `41` is the largest -/

/-- The array `mdsDiag` (with `M = diag mdsDiag + J`) is the list `mdsDiagonal` of the
certificate, entry by entry, by `decide`. -/
theorem mdsDiag_eq_diagonal : ∀ k : Fin 3, mdsDiag k = ent modulus mdsDiagonal k := by
  decide

/-- The active rounds of the middle witness trail are exactly the odd rounds from `1` to `81`. -/
theorem middle_trail_pattern : ∀ n < 83,
    (ent modulus (row middleStates n) 2 ≠ 0 ↔ n % 2 = 1) := by
  decide +kernel

/-- Exactly `41` of the `83` rounds of the middle witness trail are active. -/
theorem middle_trail_active :
    ((Finset.range 83).filter (fun n => ent modulus (row middleStates n) 2 ≠ 0)).card = 41 := by
  decide +kernel

/-- **`42` is not a middle bound** for `83` rounds with `diag (2, -2, -3) + J` and mask `{2}`: the
trail of `middleStates` and `middleOutputs` (`middle_trail_check`), a trail through `83` rounds
with that linear map and mask, starts from a nonzero difference and charges `41` S-boxes. -/
theorem middle_bound_diag_not_forty_two :
    ¬ Hades.MiddleBound (Poseidon2.diagPlusOnes (1 : F) mdsDiag) ({2} : Finset (Fin 3)) 83 42 :=
  Hades.MiddleBound.not_of_checkTrail (p := modulus) mdsDiag 2 83 42 mdsDiagonal middleStates
    middleOutputs mds mds_toLinearMap_eq mdsDiag_eq_diagonal middle_trail_check
    (by decide +kernel) (middle_trail_active.trans_lt (by norm_num))

/-- **`42` is not a middle bound for the linear layer `M`**, which is `diag (2, -2, -3) + J`. So
`41` (`middle_bound`) is the largest middle bound for the `83` partial rounds. -/
theorem middle_bound_not_forty_two :
    ¬ Hades.MiddleBound mds.toLinearMap ({2} : Finset (Fin 3)) 83 42 := by
  rw [mds_toLinearMap_eq]
  exact middle_bound_diag_not_forty_two

/-! ### Fifty-seven is attained in the `IsTrail` model -/

/-- The witness trail: row `n` of `trailStates`, the difference entering round `n`. -/
def trail (n : ℕ) : State :=
  vec modulus 3 (row trailStates n)

/-- **The witness is a trail** in the `IsTrail` model through the `91` rounds, for every
round-constant table (`trail_check`). Every round's linear map is `M`, the matrix of `mdsRows`. -/
theorem trail_isTrail_general (table : ℕ → State) :
    Hades.IsTrail (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table)
      trail 91 :=
  Hades.isTrail_of_checkHadesTrail (p := modulus) (2 : Fin 3) 4 83 4 mdsRows mdsRows
    trailStates trailSboxOutputs _ (fun _ => mds) table (fun _ _ _ v => mds_eq_mat_mulVec v)
    (fun _ _ _ v => mds_eq_mat_mulVec v) trail_check

/-- **The witness charges exactly `57` S-boxes**, for every round-constant table
(`trail_weight`). -/
theorem trail_weight_general (table : ℕ → State) :
    Hades.scheduledWeight (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table)
      trail 0 91 = 57 :=
  (Hades.scheduledWeight_eq_trailWeight (p := modulus) (2 : Fin 3) 4 83 4 trailStates _
    (fun _ => mds) table).trans trail_weight

/-- The witness starts from a nonzero difference. -/
theorem trail_zero_ne_zero : trail 0 ≠ 0 := by
  decide +kernel

/-- **Fifty-seven is attained in the `IsTrail` model, for every round-constant table.** Some
trail through the `91` rounds, from a nonzero difference, charges exactly `57` S-boxes; with
`isTrail_activity_middle_general`, `57` is the least charge over all such trails. The trail is not
claimed to be realised by an input pair or a key. -/
theorem activity_attained_general (table : ℕ → State) :
    ∃ T : ℕ → State, T 0 ≠ 0 ∧
      Hades.IsTrail (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) T 91 ∧
      Hades.scheduledWeight
        (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) T 0 91 = 57 :=
  ⟨trail, trail_zero_ne_zero, trail_isTrail_general table, trail_weight_general table⟩

/-- **Fifty-seven is attained in the `IsTrail` model** for the pinned rounds. -/
theorem activity_attained :
    ∃ T : ℕ → State, T 0 ≠ 0 ∧ Hades.IsTrail rounds T 91 ∧
      Hades.scheduledWeight rounds T 0 91 = 57 :=
  activity_attained_general values

/-! ### The exponents -/

set_option exponentiation.threshold 15000 in
/-- **`14250` is the largest exponent the exact ratio gives.** `2^14251 * 2^57 ≤ p^57` fails. -/
theorem middle_sharp_exponent_succ_fails : ¬ 2 ^ 14251 * 2 ^ 57 ≤ modulus ^ 57 := by
  decide

/-- `2 * 2^251 > p`: `250` is the largest whole number of bits per charged S-box. -/
theorem bits_251_too_large : ¬ 2 * 2 ^ 251 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- **`14250` is the largest exponent of the whole-bit form.** If `2 * 2^dd ≤ p`, then
`dd * 57 ≤ 14250`. -/
theorem whole_bit_exponent_le (dd : ℕ) (h : 2 * 2 ^ dd ≤ Fintype.card F) :
    dd * 57 ≤ 14250 := by
  by_contra hlt
  exact bits_251_too_large (le_trans (Nat.mul_le_mul_left 2
    (Nat.pow_le_pow_right (by norm_num) (by omega))) h)

/-! ### Changed certificates are rejected -/

open Hades.AutomatonCheck (AState get checkAll)

/-- `states` with the first coefficient of the inactive transition of state `1` increased by one;
every other entry is unchanged. -/
def statesCorrupted : List AState :=
  states.set 1 { get states 1 with
    coef0 := (get states 1).coef0.set 0
      (((get states 1).coef0.getD 0 []).set 0 (((get states 1).coef0.getD 0 []).getD 0 0 + 1)) }

/-- The corrupted table differs from `states`. -/
theorem statesCorrupted_ne : (get statesCorrupted 1).coef0 ≠ (get states 1).coef0 := by
  decide +kernel

/-- **The checker rejects the corrupted certificate.** -/
theorem corrupted_rejected :
    checkAll fieldModulus 3 2 83 mdsRows 0 statesCorrupted = false := by
  decide +kernel

/-- `states` with the potential of the start state lowered from `2` to `0`. If it passed, it would
give the middle bound `(83 + 1 - 0) / 2 = 42`, which `middle_bound_not_forty_two` refutes. -/
def statesLowPotential : List AState :=
  states.set 0 { get states 0 with pot := 0 }

/-- **The checker rejects the lowered start potential.** -/
theorem low_potential_rejected :
    checkAll fieldModulus 3 2 83 mdsRows 0 statesLowPotential = false := by
  decide +kernel

end Poseidon.Starknet.MiddleChecks

/-! ### Axiom footprints -/

/-- info: 'Poseidon.Certificates.Starknet.automaton_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Certificates.Starknet.automaton_check

/-- info: 'Poseidon.Certificates.Starknet.start_pot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Certificates.Starknet.start_pot

/-- info: 'Poseidon.Certificates.Starknet.trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Certificates.Starknet.trail_check

/-- info: 'Poseidon.Certificates.Starknet.trail_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Certificates.Starknet.trail_weight

/-- info: 'Poseidon.Certificates.Starknet.middle_trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Certificates.Starknet.middle_trail_check

/-- info: 'Poseidon.Starknet.middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.middle_bound

/-- info: 'Poseidon.Starknet.middle_bound_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.middle_bound_diag

/-- info: 'Poseidon.Starknet.isTrail_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.isTrail_activity_middle_general

/-- info: 'Poseidon.Starknet.activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.activity_middle_general

/-- info: 'Poseidon.Starknet.activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.activity_middle

/--
info: 'Poseidon.Starknet.independent_key_probability_middle_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_middle_general

/-- info: 'Poseidon.Starknet.independent_key_probability_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_middle

/--
info: 'Poseidon.Starknet.independent_key_probability_middle_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_middle_exact_general

/-- info: 'Poseidon.Starknet.independent_key_probability_middle_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_middle_exact

/-- info: 'Poseidon.Starknet.middle_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.middle_sharp_exponent_bound

/--
info: 'Poseidon.Starknet.independent_key_probability_middle_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_middle_sharp_general

/-- info: 'Poseidon.Starknet.independent_key_probability_middle_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_middle_sharp

/--
info: 'Poseidon.Starknet.MiddleChecks.middle_bound_diag_not_forty_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.middle_bound_diag_not_forty_two

/-- info: 'Poseidon.Starknet.MiddleChecks.middle_bound_not_forty_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.middle_bound_not_forty_two

/-- info: 'Poseidon.Starknet.MiddleChecks.activity_attained_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.activity_attained_general

/-- info: 'Poseidon.Starknet.MiddleChecks.activity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.activity_attained

/-- info: 'Poseidon.Starknet.MiddleChecks.middle_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.middle_sharp_exponent_succ_fails

/-- info: 'Poseidon.Starknet.MiddleChecks.whole_bit_exponent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.whole_bit_exponent_le

/-- info: 'Poseidon.Starknet.MiddleChecks.corrupted_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.corrupted_rejected

/-- info: 'Poseidon.Starknet.MiddleChecks.low_potential_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.MiddleChecks.low_potential_rejected
