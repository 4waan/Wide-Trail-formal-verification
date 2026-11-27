/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.Plonky3MiddleBound
import WideTrail.Poseidon2.KoalaBear
import WideTrail.Poseidon2.BN254Middle

/-!
# Today's Poseidon2 counts through the middle-bound interface

`WideTrail.Hades.MiddleBound` takes a lower bound on the partial rounds as a hypothesis,
`Hades.MiddleBound A mask m μ`, and `WideTrail.Poseidon2.Plonky3MiddleBound` states the
width-sixteen results with it. This file re-derives two existing instance counts through that
interface, with their statements unchanged, from the window bound
`Hades.MiddleBound.of_inactiveSpace` at `μ = m / w`.

* KoalaBear (SP1, width sixteen): `koalaBear_activity_general` (`33`) and
  `koalaBear_probability_sharp_general` (exponent `989`) through
  `Poseidon2.Plonky3.Diag.activity_with_middle_bound` and
  `Diag.independent_key_probability_with_middle_bound_sharp`, with the middle bound
  `20 / 16 = 1` from `KoalaBear.inactive_trivial`; these are the statements of
  `KoalaBear.activity_general` and `KoalaBear.independent_key_probability_sharp_general`.
* BN254 (width three): `bn254_activity` (`34`) and `bn254_probability_sharp` (exponent `8554`)
  through the generic `Hades.outer_middle_bound_of` and
  `Hades.hades_probability_with_middle_bound_exact`, with the middle bound `56 / 3 = 18` from
  `BN254.internal_inactive_trivial`; these are the statements of `BN254.activity_with_partial` and
  `BN254.independent_key_probability_sharp`.

The generic checks of the interface (the window theorems as the case `μ = m / w`, and a `ZMod 5`
toy where a middle bound is shown from the definition and refuted by executions) are in
`WideTrail.Hades.Checks.MiddleBound`. The axiom footprints of the width-sixteen `Diag` forms and
of the results here are pinned at the end of the file.

## What is not claimed

The re-derived counts are the existing lower bounds on charged S-boxes in the `IsTrail` model,
unchanged; nothing here improves them or claims that they are attained. The probability
statements concern one trail in the model with an additional independent uniform key per round:
not the permutations with their fixed constants, and not a differential.
-/

set_option autoImplicit false

namespace Poseidon2.MiddleBoundChecks

/-! ### KoalaBear through `Diag`: `33` and the exponent `989` -/

section KoalaBear

open Poseidon2.KoalaBear

/-- The window middle bound for SP1 KoalaBear: every trail through `20` consecutive partial rounds
with `diag d + J` charges at least `20 / 16 = 1` S-box. -/
theorem koalaBear_window_middleBound :
    Hades.MiddleBound (diagPlusOnes (1 : F) (Plonky3.sp1Diag F)) ({0} : Finset (Fin 16)) 20
      (20 / 16) :=
  Hades.MiddleBound.of_inactiveSpace inactive_trivial 20

/-- **`KoalaBear.activity_general` through the interface**: the same statement, from
`Plonky3.Diag.activity_with_middle_bound` and `koalaBear_window_middleBound`. -/
theorem koalaBear_activity_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    33 ≤ Hades.scheduledWeight (Plonky3.rounds conditions 20 sbox table)
      (Hades.differenceTrace (Plonky3.rounds conditions 20 sbox table) (external x) (external y))
      0 28 :=
  Plonky3.Diag.activity_with_middle_bound conditions.toDiag m4Primes_ne_zero 20 sbox table
    koalaBear_window_middleBound hxy

/-- **`KoalaBear.independent_key_probability_sharp_general` through the interface**: the same
statement, exponent `989`, from `Plonky3.Diag.independent_key_probability_with_middle_bound_sharp`
and `koalaBear_window_middleBound`. One trail, an additional independent uniform key per
round. -/
theorem koalaBear_probability_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.rounds conditions 20 sbox table) (8 + 20) T x * 2 ^ 989
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Plonky3.Diag.independent_key_probability_with_middle_bound_sharp conditions.toDiag
    m4Primes_ne_zero 20 sbox table sbox_uniform (by norm_num) koalaBear_window_middleBound
    (by rw [field_card]; exact sharp_exponent_bound) h0 x

end KoalaBear

/-! ### BN254 width three through the generic form: `34` and the exponent `8554` -/

section BN254

open Poseidon2.BN254

/-- The window middle bound for BN254: every trail through `56` consecutive internal rounds
charges at least `56 / 3 = 18` S-boxes. -/
theorem bn254_window_middleBound :
    Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 3)) 56 (56 / 3) :=
  Hades.MiddleBound.of_inactiveSpace internal_inactive_trivial 56

/-- **`BN254.activity_with_partial` through the interface**: the same statement, from
`Hades.outer_middle_bound_of` and `bn254_window_middleBound`. -/
theorem bn254_activity {x y : State} (hxy : x ≠ y) :
    34 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 64 :=
  Hades.outer_middle_bound_of rounds (fun h => hxy (external.injective h)) 4 56 4 4 (56 / 3)
    (fun j hj => by simp [rounds, Hades.hadesSchedule, Hades.hadesMask_prefix 4 56 4 _ hj])
    (fun j hj => by simp [rounds, Hades.hadesSchedule, Hades.hadesMask_suffix 4 56 4 _ hj])
    (fun j hj => by simpa [rounds, Hades.hadesSchedule] using full_prefix j hj)
    (fun j hj => by simpa [rounds, Hades.hadesSchedule] using full_suffix j hj)
    internal.toLinearMap {0} (fun j hj => by rw [middle_linear j hj]) middle_mask
    bn254_window_middleBound

/-- **`BN254.independent_key_probability_sharp` through the interface**: the same statement,
exponent `8554`, from `Hades.hades_probability_with_middle_bound_exact`, `bn254_window_middleBound`
and `BN254.sharp_exponent_bound`. One trail, an additional independent uniform key per round. -/
theorem bn254_probability_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values)
        (4 + 56 + 4) T x * 2 ^ 8554
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_probability_with_middle_bound_exact (Idx := Fin 3) (K := F) (u := 4)
    4 56 4 4 (56 / 3) {0} (fun _ _ => sbox) linear values (fun _ _ _ => sbox_uniform)
    full_prefix full_suffix internal.toLinearMap (fun j hj => by rw [linear_middle j hj])
    bn254_window_middleBound h0 x
  rw [field_card] at h
  exact Hades.mul_le_of_ratio h sharp_exponent_bound (pow_pos (by norm_num) _)

end BN254

end Poseidon2.MiddleBoundChecks

/-- info: 'Poseidon2.Plonky3.Diag.middleBound_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.middleBound_internal

/-- info: 'Poseidon2.Plonky3.Diag.activity_with_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.activity_with_middle_bound

/--
info: 'Poseidon2.Plonky3.Diag.independent_key_probability_with_middle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.independent_key_probability_with_middle_bound

/--
info: 'Poseidon2.Plonky3.Diag.independent_key_probability_with_middle_bound_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.independent_key_probability_with_middle_bound_exact

/--
info: 'Poseidon2.Plonky3.Diag.independent_key_probability_with_middle_bound_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.independent_key_probability_with_middle_bound_sharp

/-- info: 'Poseidon2.MiddleBoundChecks.koalaBear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.MiddleBoundChecks.koalaBear_activity_general

/--
info: 'Poseidon2.MiddleBoundChecks.koalaBear_probability_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.MiddleBoundChecks.koalaBear_probability_sharp_general

/-- info: 'Poseidon2.MiddleBoundChecks.bn254_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.MiddleBoundChecks.bn254_activity

/-- info: 'Poseidon2.MiddleBoundChecks.bn254_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.MiddleBoundChecks.bn254_probability_sharp
