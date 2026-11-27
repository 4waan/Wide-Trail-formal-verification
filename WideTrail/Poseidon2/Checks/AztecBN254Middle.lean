/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.AztecBN254Middle

/-!
# Checks for the Aztec and Noir BN254 width-four middle bound

`WideTrail.Poseidon2.AztecBN254Middle` proves, by a forward-space automaton certificate for a
window of `14` partial rounds, that every trail through `14` consecutive partial rounds of the
pinned Aztec and Noir width-four permutation charges at least `6` S-boxes, hence `24` in the `56`
partial rounds, `44` charged S-boxes in all, and the exponents `11070` (exact ratio) and `11044`
(whole bits). The checks below show that `6` is the largest middle bound for a window of `14`
rounds, that no middle bound above `27` holds for the `56` partial rounds, that some trail in the
`IsTrail` model charges exactly `47`, that `11070` and `11044` are the largest exponents the
arithmetic gives for `44` charged S-boxes, and that the checker rejects changed certificates.
Every finite check is `decide` or `decide +kernel`.

## Exactness

* `middle_bound_window_not_seven`, `middle_bound_window_diag_not_seven`: `7` is not a middle bound
  for `14` rounds with the internal layer (`diagPlusOnes 1 internalDiag`) and mask `{0}`. The
  witness is the trail `windowStates`, `windowOutputs` of the certificate file, checked by
  `RelationCheck.checkTrail` (`window_trail_check`), from a nonzero difference; its active rounds
  are exactly the even rounds from `2` to `12` (`window_trail_pattern`), so `6` of them
  (`window_trail_active`).
* `middle_bound_not_twenty_eight`, `middle_bound_diag_not_twenty_eight`: `28` is not a middle
  bound for the `56` partial rounds. The witness is the trail `middleStates`, `middleOutputs`
  (`middle_trail_check`), whose active rounds are exactly the even rounds from `2` to `54`
  (`middle_trail_pattern`), so `27` of them (`middle_trail_active`). The lower bound proved in
  Lean is `24`; the gap between `24` and `27` is not closed in Lean.
* `trail_isTrail_general`, `trail_weight_general`, `activity_attained_general`,
  `activity_attained`: the rows of `trailStates` are a trail in the `IsTrail` model through the
  `64` rounds of the schedule, for every round-constant table, from a nonzero difference, and
  they charge exactly `47` S-boxes. So no argument that uses only `IsTrail` proves more than `47`.
  The trail is not claimed to be realised by an input pair or a key.
* `middle_sharp_exponent_succ_fails`: `2^11071 * 4^44 ≤ p^44` fails, so `11070` is the largest
  exponent the exact ratio gives for `44` charged S-boxes.
* `bits_252_too_large`, `whole_bit_exponent_le`: `4 * 2^252 > p`, so every whole number `dd` of
  bits per charged S-box with `4 * 2^dd ≤ p` has `dd * 44 ≤ 11044`.

## Negative controls

Each table below is `states` with one value changed, and `AutomatonCheck.checkAll` returns
`false` on it, by `decide +kernel`:

* `statesCorrupted`: the first coefficient of the inactive transition of state `1` increased by
  one (`corrupted_rejected`);
* `statesLowPotential`: the potential of the start state lowered from `3` to `1`, which would give
  the window bound `(14 + 1 - 1) / 2 = 7` that `middle_bound_window_not_seven` refutes
  (`low_potential_rejected`).

## What is not claimed

These checks concern the `IsTrail` model and the arithmetic of the exponents. They do not show that
`24` or `44` is attained, that `47` is the least number of S-boxes an actual input pair incurs,
that the witness trails are realised by input pairs or keys, or anything about the permutation
with its fixed constants beyond the statements of the results file. The axiom footprints of the
new theorems are pinned at the end of the file.
-/

set_option autoImplicit false

open Poseidon2.BN254 (F modulus field_card sbox)

namespace Poseidon2.AztecBN254.MiddleChecks

open Poseidon2.Certificates.AztecBN254 (fieldModulus internalRows externalRows internalDiagonal
  states windowStates windowOutputs trailStates trailSboxOutputs middleStates middleOutputs
  window_trail_check trail_check trail_weight middle_trail_check)

open Hades.RelationCheck (ent row vec)

/-! ### The window bound `6` is the largest, and `28` fails for the partial rounds -/

/-- The stored array `internalDiag` is the list `internalDiagonal` of the certificate, entry by
entry, by `decide`. -/
theorem internalDiag_eq_diagonal :
    ∀ k : Fin 4, internalDiag k = ent modulus internalDiagonal k := by
  decide

/-- The active rounds of the window witness trail are exactly the even rounds from `2` to `12`. -/
theorem window_trail_pattern : ∀ n < 14,
    (ent modulus (row windowStates n) 0 ≠ 0 ↔ 2 ≤ n ∧ n % 2 = 0) := by
  decide +kernel

/-- Exactly `6` of the `14` rounds of the window witness trail are active. -/
theorem window_trail_active :
    ((Finset.range 14).filter (fun n => ent modulus (row windowStates n) 0 ≠ 0)).card = 6 := by
  decide +kernel

/-- **`7` is not a middle bound for `14` rounds** with `diagPlusOnes 1 internalDiag` and mask
`{0}`: the trail of `windowStates` and `windowOutputs` (`window_trail_check`), a trail through `14`
rounds with that linear map and mask, starts from a nonzero difference and charges `6` S-boxes. -/
theorem middle_bound_window_diag_not_seven :
    ¬ Hades.MiddleBound (diagPlusOnes (1 : F) internalDiag) ({0} : Finset (Fin 4)) 14 7 :=
  Hades.MiddleBound.not_of_checkTrail (p := modulus) internalDiag 0 14 7 internalDiagonal
    windowStates windowOutputs internal internal_toLinearMap internalDiag_eq_diagonal
    window_trail_check (by decide +kernel) (window_trail_active.trans_lt (by norm_num))

/-- **`7` is not a middle bound for `14` rounds with the internal layer**, so `6`
(`middle_bound_window`) is the largest middle bound for a window of `14` partial rounds. -/
theorem middle_bound_window_not_seven :
    ¬ Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 4)) 14 7 := by
  rw [internal_toLinearMap]
  exact middle_bound_window_diag_not_seven

/-- The active rounds of the middle witness trail are exactly the even rounds from `2` to `54`. -/
theorem middle_trail_pattern : ∀ n < 56,
    (ent modulus (row middleStates n) 0 ≠ 0 ↔ 2 ≤ n ∧ n % 2 = 0) := by
  decide +kernel

/-- Exactly `27` of the `56` rounds of the middle witness trail are active. -/
theorem middle_trail_active :
    ((Finset.range 56).filter (fun n => ent modulus (row middleStates n) 0 ≠ 0)).card = 27 := by
  decide +kernel

/-- **`28` is not a middle bound for `56` rounds** with `diagPlusOnes 1 internalDiag` and mask
`{0}`: the trail of `middleStates` and `middleOutputs` (`middle_trail_check`), a trail through `56`
rounds with that linear map and mask, starts from a nonzero difference and charges `27` S-boxes. -/
theorem middle_bound_diag_not_twenty_eight :
    ¬ Hades.MiddleBound (diagPlusOnes (1 : F) internalDiag) ({0} : Finset (Fin 4)) 56 28 :=
  Hades.MiddleBound.not_of_checkTrail (p := modulus) internalDiag 0 56 28 internalDiagonal
    middleStates middleOutputs internal internal_toLinearMap internalDiag_eq_diagonal
    middle_trail_check (by decide +kernel) (middle_trail_active.trans_lt (by norm_num))

/-- **`28` is not a middle bound for the `56` partial rounds with the internal layer.** With
`middle_bound`, the largest middle bound for these rounds lies between `24` and `27`. -/
theorem middle_bound_not_twenty_eight :
    ¬ Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 4)) 56 28 := by
  rw [internal_toLinearMap]
  exact middle_bound_diag_not_twenty_eight

/-! ### Forty-seven is attained in the `IsTrail` model -/

/-- The witness trail: row `n` of `trailStates`, the difference entering round `n`. -/
def trail (n : ℕ) : State :=
  vec modulus 4 (row trailStates n)

/-- The external matrix `hlMat4` is the matrix of the certificate's table `externalRows`. -/
theorem hlMat4_eq_mat : hlMat4 F = Hades.AutomatonCheck.mat modulus 4 externalRows := by
  ext i k
  fin_cases i <;> fin_cases k <;> decide

/-- The linear map of a full round acts as the matrix of `externalRows`. -/
theorem linear_full (n : ℕ) (_hn : n < 4 + 56 + 4) (hf : n < 4 ∨ 4 + 56 ≤ n) (v : State) :
    linear n v = (Hades.AutomatonCheck.mat modulus 4 externalRows).mulVec v := by
  have hl : linear n = external := by
    simp only [linear]
    exact if_pos (by omega)
  rw [hl, external_eq_mulVec, hlMat4_eq_mat]

/-- The linear map of a partial round acts as the matrix of `internalRows`. -/
theorem linear_partial (n : ℕ) (h1 : 4 ≤ n) (h2 : n < 4 + 56) (v : State) :
    linear n v = (Hades.AutomatonCheck.mat modulus 4 internalRows).mulVec v := by
  have hl : linear n = internal := by
    simp only [linear]
    exact if_neg (by omega)
  rw [hl]
  exact internal_eq_mat_mulVec v

/-- **The witness is a trail** in the `IsTrail` model through the `64` rounds, for every
round-constant table (`trail_check`). -/
theorem trail_isTrail_general (table : ℕ → State) :
    Hades.IsTrail (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) trail 64 :=
  Hades.isTrail_of_checkHadesTrail (p := modulus) (0 : Fin 4) 4 56 4 externalRows internalRows
    trailStates trailSboxOutputs _ linear table linear_full linear_partial trail_check

/-- **The witness charges exactly `47` S-boxes**, for every round-constant table
(`trail_weight`). -/
theorem trail_weight_general (table : ℕ → State) :
    Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) trail 0
      64 = 47 :=
  (Hades.scheduledWeight_eq_trailWeight (p := modulus) (0 : Fin 4) 4 56 4 trailStates _ linear
    table).trans trail_weight

/-- The witness starts from a nonzero difference. -/
theorem trail_zero_ne_zero : trail 0 ≠ 0 := by
  decide +kernel

/-- **Forty-seven is attained in the `IsTrail` model, for every round-constant table.** Some
trail through the `64` rounds, from a nonzero difference, charges exactly `47` S-boxes, so no
argument that uses only `IsTrail` proves a lower bound above `47`. The trail is not claimed to be
realised by an input pair or a key. -/
theorem activity_attained_general (table : ℕ → State) :
    ∃ T : ℕ → State, T 0 ≠ 0 ∧
      Hades.IsTrail (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) T 64 ∧
      Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) T 0
        64 = 47 :=
  ⟨trail, trail_zero_ne_zero, trail_isTrail_general table, trail_weight_general table⟩

/-- **Forty-seven is attained in the `IsTrail` model** for the pinned rounds. -/
theorem activity_attained :
    ∃ T : ℕ → State, T 0 ≠ 0 ∧ Hades.IsTrail rounds T 64 ∧
      Hades.scheduledWeight rounds T 0 64 = 47 :=
  activity_attained_general values

/-! ### The exponents -/

set_option exponentiation.threshold 12000 in
/-- **`11070` is the largest exponent the exact ratio gives.** `2^11071 * 4^44 ≤ p^44` fails. -/
theorem middle_sharp_exponent_succ_fails : ¬ 2 ^ 11071 * 4 ^ 44 ≤ modulus ^ 44 := by
  decide

/-- `4 * 2^252 > p`: `251` is the largest whole number of bits per charged S-box. -/
theorem bits_252_too_large : ¬ 4 * 2 ^ 252 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- **`11044` is the largest exponent of the whole-bit form.** If `4 * 2^dd ≤ p`, then
`dd * 44 ≤ 11044`. -/
theorem whole_bit_exponent_le (dd : ℕ) (h : 4 * 2 ^ dd ≤ Fintype.card F) :
    dd * 44 ≤ 11044 := by
  by_contra hlt
  exact bits_252_too_large (le_trans (Nat.mul_le_mul_left 4
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
    checkAll fieldModulus 4 0 14 internalRows 0 statesCorrupted = false := by
  decide +kernel

/-- `states` with the potential of the start state lowered from `3` to `1`. If it passed, it would
give the window bound `(14 + 1 - 1) / 2 = 7`, which `middle_bound_window_not_seven` refutes. -/
def statesLowPotential : List AState :=
  states.set 0 { get states 0 with pot := 1 }

/-- **The checker rejects the lowered start potential.** -/
theorem low_potential_rejected :
    checkAll fieldModulus 4 0 14 internalRows 0 statesLowPotential = false := by
  decide +kernel

end Poseidon2.AztecBN254.MiddleChecks

/-! ### Axiom footprints -/

/-- info: 'Poseidon2.Certificates.AztecBN254.automaton_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.AztecBN254.automaton_check

/-- info: 'Poseidon2.Certificates.AztecBN254.start_pot' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.AztecBN254.start_pot

/-- info: 'Poseidon2.Certificates.AztecBN254.window_trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.AztecBN254.window_trail_check

/-- info: 'Poseidon2.Certificates.AztecBN254.trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.AztecBN254.trail_check

/-- info: 'Poseidon2.Certificates.AztecBN254.trail_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.AztecBN254.trail_weight

/-- info: 'Poseidon2.Certificates.AztecBN254.middle_trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.AztecBN254.middle_trail_check

/-- info: 'Poseidon2.AztecBN254.middle_bound_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.middle_bound_window

/-- info: 'Poseidon2.AztecBN254.middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.middle_bound

/-- info: 'Poseidon2.AztecBN254.middle_bound_window_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.middle_bound_window_diag

/-- info: 'Poseidon2.AztecBN254.middle_bound_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.middle_bound_diag

/-- info: 'Poseidon2.AztecBN254.isTrail_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.isTrail_activity_middle_general

/-- info: 'Poseidon2.AztecBN254.activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.activity_middle_general

/-- info: 'Poseidon2.AztecBN254.activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.activity_middle

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_middle_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_middle_general

/-- info: 'Poseidon2.AztecBN254.independent_key_probability_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_middle

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_middle_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_middle_exact_general

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_middle_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_middle_exact

/-- info: 'Poseidon2.AztecBN254.middle_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.middle_sharp_exponent_bound

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_middle_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_middle_sharp_general

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_middle_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_middle_sharp

/--
info: 'Poseidon2.AztecBN254.MiddleChecks.middle_bound_window_diag_not_seven' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.middle_bound_window_diag_not_seven

/--
info: 'Poseidon2.AztecBN254.MiddleChecks.middle_bound_window_not_seven' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.middle_bound_window_not_seven

/--
info: 'Poseidon2.AztecBN254.MiddleChecks.middle_bound_diag_not_twenty_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.middle_bound_diag_not_twenty_eight

/--
info: 'Poseidon2.AztecBN254.MiddleChecks.middle_bound_not_twenty_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.middle_bound_not_twenty_eight

/-- info: 'Poseidon2.AztecBN254.MiddleChecks.activity_attained_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.activity_attained_general

/-- info: 'Poseidon2.AztecBN254.MiddleChecks.activity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.activity_attained

/-- info: 'Poseidon2.AztecBN254.MiddleChecks.middle_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.middle_sharp_exponent_succ_fails

/-- info: 'Poseidon2.AztecBN254.MiddleChecks.whole_bit_exponent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.whole_bit_exponent_le

/-- info: 'Poseidon2.AztecBN254.MiddleChecks.corrupted_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.corrupted_rejected

/-- info: 'Poseidon2.AztecBN254.MiddleChecks.low_potential_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.MiddleChecks.low_potential_rejected
