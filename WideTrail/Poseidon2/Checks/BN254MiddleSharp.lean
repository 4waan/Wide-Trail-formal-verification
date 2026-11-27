/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BN254MiddleSharp

/-!
# Checks for the BN254 width-three middle bound

`WideTrail.Poseidon2.BN254MiddleSharp` proves, by a forward-space automaton certificate, that
every trail through the `56` partial rounds of the pinned BN254 width-three permutation charges
at least `27` S-boxes, hence `43` charged S-boxes in all and the exponents `10818` (exact ratio)
and `10793` (whole bits). The checks below show that `27` is the largest middle bound for these
rounds, that `43` is attained by a trail in the `IsTrail` model, that `10818` and `10793` are the
largest exponents the arithmetic gives for `43` charged S-boxes, and that the checker rejects
changed certificates. Every finite check is `decide` or `decide +kernel`.

## Exactness

* `middle_bound_not_twenty_eight`, `middle_bound_diag_not_twenty_eight`: `28` is not a middle
  bound for `56` rounds with the internal layer (`diag (1, 1, 2) + J`) and mask `{0}`. The witness
  is the trail `middleStates`, `middleOutputs` of the certificate file, a trail through `56`
  rounds with that linear map and mask from a nonzero difference, checked by
  `RelationCheck.checkTrail` (`middle_trail_check`). Its active rounds are exactly the even
  rounds from `2` to `54` (`middle_trail_pattern`): the first two rounds are inactive, then active
  and inactive rounds alternate; so exactly `27` of its rounds are active (`middle_trail_active`).
* `trail_isTrail_general`, `trail_weight_general`, `activity_attained_general`,
  `activity_attained`: the rows of `trailStates` are a trail in the `IsTrail` model through the
  `64` rounds of the schedule, for every round-constant table, from a nonzero difference, and
  they charge exactly `43` S-boxes. With `isTrail_activity_middle_general`, `43` is the least
  number of charged S-boxes over all trails in the `IsTrail` model through these rounds, so no
  argument that uses only `IsTrail` proves more. The trail is not claimed to be realised by an
  input pair or a key.
* `middle_sharp_exponent_succ_fails`: `2^10819 * 4^43 ≤ p^43` fails, so `10818` is the largest
  exponent the exact ratio gives for `43` charged S-boxes.
* `bits_252_too_large`, `whole_bit_exponent_le`: `4 * 2^252 > p`, so every whole number `dd` of
  bits per charged S-box with `4 * 2^dd ≤ p` has `dd * 43 ≤ 10793`.

## Negative controls

Each table below is `states` with one value changed, and `AutomatonCheck.checkAll` returns
`false` on it, by `decide +kernel`:

* `statesCorrupted`: the first coefficient of the inactive transition of state `3` increased by
  one (`corrupted_rejected`);
* `statesLowPotential`: the potential of the start state lowered from `2` to `1`, which would give
  the bound `28` that `middle_bound_not_twenty_eight` refutes (`low_potential_rejected`);
* `statesOutOfRange`: the successor of state `1` after an active round moved from `0` to `57`, a
  number that is not a state (`out_of_range_rejected`);
* `statesDeep`: the depth of state `2` raised to `56`, which would exempt its transitions from the
  check (`deep_rejected`).

## What is not claimed

These checks concern the `IsTrail` model and the arithmetic of the exponents. They do not show that
`43` is the least number of S-boxes an actual input pair incurs, that the witness trails are
realised by input pairs or keys, or anything about the permutation with its fixed constants
beyond the statements of the results file. The axiom footprints of the new theorems are pinned at
the end of the file.
-/

set_option autoImplicit false

open Poseidon2.BN254 (F State modulus field_card)

namespace Poseidon2.BN254.MiddleSharpChecks

open Poseidon2.Certificates.BN254 (fieldModulus internalRows externalRows internalDiagonal states
  trailStates trailSboxOutputs middleStates middleOutputs trail_check trail_weight
  middle_trail_check)

open Hades.RelationCheck (ent row vec)

/-! ### The middle bound `27` is the largest -/

/-- The diagonal `internalDiag` is the list `internalDiagonal` of the certificate, entry by entry,
by `decide`. -/
theorem internalDiag_eq_diagonal :
    ∀ k : Fin 3, internalDiag k = ent modulus internalDiagonal k := by
  decide

/-- The active rounds of the middle witness trail are exactly the even rounds from `2` to `54`. -/
theorem middle_trail_pattern : ∀ n < 56,
    (ent modulus (row middleStates n) 0 ≠ 0 ↔ 2 ≤ n ∧ n % 2 = 0) := by
  decide +kernel

/-- Exactly `27` of the `56` rounds of the middle witness trail are active. -/
theorem middle_trail_active :
    ((Finset.range 56).filter (fun n => ent modulus (row middleStates n) 0 ≠ 0)).card = 27 := by
  decide +kernel

/-- **`28` is not a middle bound** for `56` rounds with `diag (1, 1, 2) + J` and mask `{0}`: the
trail of `middleStates` and `middleOutputs` (`middle_trail_check`), a trail through `56` rounds
with that linear map and mask, starts from a nonzero difference and charges `27` S-boxes. -/
theorem middle_bound_diag_not_twenty_eight :
    ¬ Hades.MiddleBound (diagPlusOnes (1 : F) internalDiag) ({0} : Finset (Fin 3)) 56 28 :=
  Hades.MiddleBound.not_of_checkTrail (p := modulus) internalDiag 0 56 28 internalDiagonal
    middleStates middleOutputs internal internal_toLinearMap_eq internalDiag_eq_diagonal
    middle_trail_check (by decide +kernel) (middle_trail_active.trans_lt (by norm_num))

/-- **`28` is not a middle bound for the internal layer**, which is `diag (1, 1, 2) + J`. So `27`
(`middle_bound`) is the largest middle bound for the `56` partial rounds. -/
theorem middle_bound_not_twenty_eight :
    ¬ Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 3)) 56 28 := by
  rw [internal_toLinearMap_eq]
  exact middle_bound_diag_not_twenty_eight

/-! ### Forty-three is attained in the `IsTrail` model -/

/-- The witness trail: row `n` of `trailStates`, the difference entering round `n`. -/
def trail (n : ℕ) : State :=
  vec modulus 3 (row trailStates n)

/-- The external matrix is the matrix of the certificate's table `externalRows`. -/
theorem externalMatrix_eq_mat :
    externalMatrix = Hades.AutomatonCheck.mat modulus 3 externalRows := by
  ext i k
  fin_cases i <;> fin_cases k <;> decide

/-- The linear map of a full round acts as the matrix of `externalRows`. -/
theorem linear_full (n : ℕ) (_hn : n < 4 + 56 + 4) (hf : n < 4 ∨ 4 + 56 ≤ n) (v : State) :
    linear n v = (Hades.AutomatonCheck.mat modulus 3 externalRows).mulVec v := by
  have hl : linear n = external := by
    simp only [linear]
    exact if_pos (by omega)
  rw [hl, external_eq_mulVec, externalMatrix_eq_mat]

/-- The linear map of a partial round acts as the matrix of `internalRows`. -/
theorem linear_partial (n : ℕ) (h1 : 4 ≤ n) (h2 : n < 4 + 56) (v : State) :
    linear n v = (Hades.AutomatonCheck.mat modulus 3 internalRows).mulVec v := by
  have hl : linear n = internal := by
    simp only [linear]
    exact if_neg (by omega)
  rw [hl, internal_eq_mulVec, internalMatrix_eq_mat]

/-- **The witness is a trail** in the `IsTrail` model through the `64` rounds, for every
round-constant table (`trail_check`). -/
theorem trail_isTrail_general (table : ℕ → State) :
    Hades.IsTrail (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) trail 64 :=
  Hades.isTrail_of_checkHadesTrail (p := modulus) (0 : Fin 3) 4 56 4 externalRows internalRows
    trailStates trailSboxOutputs _ linear table linear_full linear_partial trail_check

/-- **The witness charges exactly `43` S-boxes**, for every round-constant table
(`trail_weight`). -/
theorem trail_weight_general (table : ℕ → State) :
    Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) trail 0
      64 = 43 :=
  (Hades.scheduledWeight_eq_trailWeight (p := modulus) (0 : Fin 3) 4 56 4 trailStates _ linear
    table).trans trail_weight

/-- The witness starts from a nonzero difference. -/
theorem trail_zero_ne_zero : trail 0 ≠ 0 := by
  decide +kernel

/-- **Forty-three is attained in the `IsTrail` model, for every round-constant table.** Some
trail through the `64` rounds, from a nonzero difference, charges exactly `43` S-boxes; with
`isTrail_activity_middle_general`, `43` is the least charge over all such trails. The trail is not
claimed to be realised by an input pair or a key. -/
theorem activity_attained_general (table : ℕ → State) :
    ∃ T : ℕ → State, T 0 ≠ 0 ∧
      Hades.IsTrail (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) T 64 ∧
      Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) T 0
        64 = 43 :=
  ⟨trail, trail_zero_ne_zero, trail_isTrail_general table, trail_weight_general table⟩

/-- **Forty-three is attained in the `IsTrail` model** for the pinned rounds. -/
theorem activity_attained :
    ∃ T : ℕ → State, T 0 ≠ 0 ∧ Hades.IsTrail rounds T 64 ∧
      Hades.scheduledWeight rounds T 0 64 = 43 :=
  activity_attained_general values

/-! ### The exponents -/

set_option exponentiation.threshold 11000 in
/-- **`10818` is the largest exponent the exact ratio gives.** `2^10819 * 4^43 ≤ p^43` fails. -/
theorem middle_sharp_exponent_succ_fails : ¬ 2 ^ 10819 * 4 ^ 43 ≤ modulus ^ 43 := by
  decide

/-- `4 * 2^252 > p`: `251` is the largest whole number of bits per charged S-box. -/
theorem bits_252_too_large : ¬ 4 * 2 ^ 252 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- **`10793` is the largest exponent of the whole-bit form.** If `4 * 2^dd ≤ p`, then
`dd * 43 ≤ 10793`. -/
theorem whole_bit_exponent_le (dd : ℕ) (h : 4 * 2 ^ dd ≤ Fintype.card F) : dd * 43 ≤ 10793 := by
  by_contra hlt
  exact bits_252_too_large (le_trans (Nat.mul_le_mul_left 4
    (Nat.pow_le_pow_right (by norm_num) (by omega))) h)

/-! ### Changed certificates are rejected -/

open Hades.AutomatonCheck (AState get checkAll)

/-- `states` with the first coefficient of the inactive transition of state `3` increased by one;
every other entry is unchanged. -/
def statesCorrupted : List AState :=
  states.set 3 { get states 3 with
    coef0 := (get states 3).coef0.set 0
      (((get states 3).coef0.getD 0 []).set 0 (((get states 3).coef0.getD 0 []).getD 0 0 + 1)) }

/-- The corrupted table differs from `states`. -/
theorem statesCorrupted_ne : (get statesCorrupted 3).coef0 ≠ (get states 3).coef0 := by
  decide +kernel

/-- **The checker rejects the corrupted certificate.** -/
theorem corrupted_rejected :
    checkAll fieldModulus 3 0 56 internalRows 0 statesCorrupted = false := by
  decide +kernel

/-- `states` with the potential of the start state lowered from `2` to `1`. If it passed, it would
give the middle bound `(56 + 1 - 1) / 2 = 28`, which `middle_bound_not_twenty_eight` refutes. -/
def statesLowPotential : List AState :=
  states.set 0 { get states 0 with pot := 1 }

/-- **The checker rejects the lowered start potential.** -/
theorem low_potential_rejected :
    checkAll fieldModulus 3 0 56 internalRows 0 statesLowPotential = false := by
  decide +kernel

/-- `states` with the successor of state `1` after an active round moved from `0` to `57`, which
is not a state (the list has `57` states). Past the end of the list, `get` reads a state with no
functional and potential `0` whose transitions are never checked. -/
def statesOutOfRange : List AState :=
  states.set 1 { get states 1 with next1 := some 57 }

/-- **The checker rejects the successor out of range.** -/
theorem out_of_range_rejected :
    checkAll fieldModulus 3 0 56 internalRows 0 statesOutOfRange = false := by
  decide +kernel

/-- `states` with the depth of state `2` raised from `2` to `56`, which would exempt its
transitions from the check. -/
def statesDeep : List AState :=
  states.set 2 { get states 2 with depth := 56 }

/-- **The checker rejects the raised depth.** -/
theorem deep_rejected : checkAll fieldModulus 3 0 56 internalRows 0 statesDeep = false := by
  decide +kernel

end Poseidon2.BN254.MiddleSharpChecks

/-! ### Axiom footprints -/

/-- info: 'Hades.MiddleBound.of_automaton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.of_automaton

/-- info: 'Hades.AutomatonCheck.checkComb_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonCheck.checkComb_spec

/-- info: 'Hades.AutomatonCheck.checkAll_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.AutomatonCheck.checkAll_spec

/-- info: 'Hades.MiddleBound.of_automatonCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.of_automatonCheck

/-- info: 'Hades.isTrail_of_checkHadesTrail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isTrail_of_checkHadesTrail

/-- info: 'Hades.scheduledWeight_eq_trailWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.scheduledWeight_eq_trailWeight

/-- info: 'Poseidon2.Certificates.BN254.automaton_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.BN254.automaton_check

/-- info: 'Poseidon2.Certificates.BN254.start_pot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.BN254.start_pot

/-- info: 'Poseidon2.Certificates.BN254.trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.BN254.trail_check

/-- info: 'Poseidon2.Certificates.BN254.trail_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.BN254.trail_weight

/-- info: 'Poseidon2.Certificates.BN254.middle_trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.BN254.middle_trail_check

/-- info: 'Poseidon2.BN254.middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.middle_bound

/-- info: 'Poseidon2.BN254.middle_bound_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.middle_bound_diag

/-- info: 'Poseidon2.BN254.isTrail_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.isTrail_activity_middle_general

/-- info: 'Poseidon2.BN254.activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.activity_middle_general

/-- info: 'Poseidon2.BN254.activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.activity_middle

/-- info: 'Poseidon2.BN254.independent_key_probability_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_middle_general

/-- info: 'Poseidon2.BN254.independent_key_probability_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_middle

/--
info: 'Poseidon2.BN254.independent_key_probability_middle_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_middle_exact_general

/-- info: 'Poseidon2.BN254.independent_key_probability_middle_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_middle_exact

/-- info: 'Poseidon2.BN254.middle_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.BN254.middle_sharp_exponent_bound

/--
info: 'Poseidon2.BN254.independent_key_probability_middle_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_middle_sharp_general

/-- info: 'Poseidon2.BN254.independent_key_probability_middle_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_middle_sharp

/--
info: 'Poseidon2.BN254.MiddleSharpChecks.middle_bound_not_twenty_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.middle_bound_not_twenty_eight

/--
info: 'Poseidon2.BN254.MiddleSharpChecks.middle_bound_diag_not_twenty_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.middle_bound_diag_not_twenty_eight

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.activity_attained_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.activity_attained_general

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.activity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.activity_attained

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.middle_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.middle_sharp_exponent_succ_fails

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.whole_bit_exponent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.whole_bit_exponent_le

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.corrupted_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.corrupted_rejected

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.low_potential_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.low_potential_rejected

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.out_of_range_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.out_of_range_rejected

/-- info: 'Poseidon2.BN254.MiddleSharpChecks.deep_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.MiddleSharpChecks.deep_rejected
