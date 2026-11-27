/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.KoalaBearMiddle
import WideTrail.Poseidon2.PicoKoalaBearMiddle

/-!
# Checks for the KoalaBear middle bounds

`WideTrail.Poseidon2.KoalaBearMiddle` and `WideTrail.Poseidon2.PicoKoalaBearMiddle` prove, by
window-relation certificates, that every trail through the `20` partial rounds of SP1's and of
Pico's KoalaBear permutation charges at least `3` S-boxes, hence `35` charged S-boxes in all and
the exponents `1049` (exact ratio) and `1015` (whole bits). The checks below show that `3` is the
largest middle bound for these rounds, that `1049` and `1015` are the largest exponents the
arithmetic gives for `35` charged S-boxes, and that the checker rejects a changed certificate.
Every finite check is `decide` or `decide +kernel`.

## Exactness

* `middle_bound_not_four` (for SP1 and for Pico): `4` is not a middle bound for `20` rounds with
  linear map `diag d + J` and mask `{0}`. The witness is the explicit trail `trailStates`,
  `trailOutputs` of the certificate file, a trail through `20` rounds with that linear map and
  mask from a nonzero difference, checked by `RelationCheck.checkTrail` (`trail_check`); its
  active rounds are exactly `0`, `2` and `4` (`trail_active`), so it stays inactive through the
  last `15` consecutive rounds. The trail is a trail in the `IsTrail` model, not claimed to be
  realised by any input pair or key.
* `internal_middle_bound_not_four` (for SP1 and for Pico): the same for the code's internal layer.
  For SP1 that layer is `R^{-1} (diag d + J)`; the witness above is not a trail for it, and the
  statement follows from `middle_bound_not_four` by `Hades.MiddleBound.smul_iff`. For Pico the
  layer is `diag d + J` itself. So `3` is the largest middle bound for the `20` partial rounds of
  both instances, for `diag d + J` and for the code's layer.
* `middle_sharp_exponent_succ_fails`: `2^1050 * 2^35 ≤ p^35` fails, so `1049` is the largest
  exponent the exact ratio gives for `35` charged S-boxes.
* `thirty_bits_too_large`, `whole_bit_exponent_le`: `2 * 2^30 > p`, so every whole number `dd` of
  bits per charged S-box with `2 * 2^dd ≤ p` has `dd * 35 ≤ 1015`, and `1016` is out of reach of
  the whole-bit form.

The two instances share the field, the S-box and the exponent arithmetic, so the exponent checks,
stated in `KoalaBear.MiddleChecks`, cover both.

## Negative controls

* `singlesCorrupted`: the certificate table `singles` with the multiplier `λ_0` of the certificate
  of the pattern `{5}` increased by one, for SP1 (`KoalaBear.MiddleChecks`) and for Pico
  (`PicoKoalaBear.MiddleChecks`); `corrupted_rejected`: `RelationCheck.checkAll` returns `false`
  on it, by `decide +kernel`.

## What is not claimed

These checks concern the `IsTrail` model and the arithmetic of the exponents. They do not show that
`35` is the least number of charged S-boxes over the whole permutation (only that the middle term
cannot exceed `3`), that it is attained by an input pair, or anything about the permutation with
its fixed constants beyond the statements of the results files. The axiom
footprints of the new theorems are pinned at the end of the file.
-/

set_option autoImplicit false

open Poseidon2.KoalaBear (F modulus field_card)

namespace Poseidon2.KoalaBear.MiddleChecks

open Poseidon2.Certificates.KoalaBear (diagonal psi gamma singles pairs trailStates trailOutputs
  trail_check)

/-! ### SP1: the middle bound `3` is the largest -/

/-- The active rounds of the witness trail are exactly `0`, `2` and `4`. -/
theorem trail_active : ∀ n < 20,
    (Hades.RelationCheck.ent modulus (Hades.RelationCheck.row trailStates n) 0 ≠ 0 ↔
      n = 0 ∨ n = 2 ∨ n = 4) := by
  decide +kernel

/-- **`4` is not a middle bound** for `20` rounds with the unscaled layer `diag d + J` and mask
`{0}`: the trail of `trailStates` and `trailOutputs` (`trail_check`), a trail through `20` rounds
with that linear map and mask, starts from a nonzero difference and charges `3` S-boxes. -/
theorem middle_bound_not_four :
    ¬ Hades.MiddleBound (diagPlusOnes (1 : F) (Plonky3.sp1Diag F)) ({0} : Finset (Fin 16)) 20 4 :=
  Hades.MiddleBound.not_of_checkTrail (p := modulus) _ 0 20 4 diagonal trailStates trailOutputs
    (Plonky3.internal 1 one_ne_zero conditions.two conditions.shermanMorrison) rfl
    sp1Diag_eq_diagonal trail_check (by decide +kernel) (by decide +kernel)

/-- **`4` is not a middle bound for the code's internal layer** `R^{-1} (diag d + J)` either: the
factor `R^{-1}` changes nothing (`Hades.MiddleBound.smul_iff`). The witness of
`middle_bound_not_four` is not itself a trail for this layer. -/
theorem internal_middle_bound_not_four :
    ¬ Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 16)) 20 4 := by
  rw [internal, Plonky3.internal_toLinearMap, diagPlusOnes_eq_smul,
    Hades.MiddleBound.smul_iff conditions.scale]
  exact middle_bound_not_four

/-! ### The exponents -/

set_option exponentiation.threshold 1100 in
/-- **`1049` is the largest exponent the exact ratio gives.** `2^1050 * 2^35 ≤ p^35` fails. -/
theorem middle_sharp_exponent_succ_fails : ¬ 2 ^ 1050 * 2 ^ 35 ≤ modulus ^ 35 := by
  decide

/-- `2 * 2^30 > p`: `29` is the largest whole number of bits per charged S-box. -/
theorem thirty_bits_too_large : ¬ 2 * 2 ^ 30 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- **`1015` is the largest exponent of the whole-bit form.** If `2 * 2^dd ≤ p`, then
`dd * 35 ≤ 1015`. -/
theorem whole_bit_exponent_le (dd : ℕ) (h : 2 * 2 ^ dd ≤ Fintype.card F) : dd * 35 ≤ 1015 := by
  by_contra hlt
  exact thirty_bits_too_large (le_trans (Nat.mul_le_mul_left 2
    (Nat.pow_le_pow_right (by norm_num) (by omega))) h)

/-! ### A changed certificate is rejected -/

/-- `singles` with the multiplier `λ_0` of the certificate of the pattern `{5}` increased by one;
every other entry is unchanged. -/
def singlesCorrupted : List (List ℕ) :=
  singles.set 5 ((singles.getD 5 []).set 2 ((singles.getD 5 []).getD 2 0 + 1))

/-- The corrupted table differs from `singles`. -/
theorem singlesCorrupted_ne : singlesCorrupted ≠ singles := by
  decide +kernel

/-- **The checker rejects the corrupted certificate.** -/
theorem corrupted_rejected :
    Hades.RelationCheck.checkAll 2130706433 16 0 20 16 diagonal psi gamma singlesCorrupted pairs =
      false := by
  decide +kernel

end Poseidon2.KoalaBear.MiddleChecks

namespace Poseidon2.PicoKoalaBear.MiddleChecks

open Poseidon2.Certificates.PicoKoalaBear (diagonal psi gamma singles pairs trailStates
  trailOutputs trail_check)

/-! ### Pico: the middle bound `3` is the largest -/

/-- The active rounds of the witness trail are exactly `0`, `2` and `4`. -/
theorem trail_active : ∀ n < 20,
    (Hades.RelationCheck.ent modulus (Hades.RelationCheck.row trailStates n) 0 ≠ 0 ↔
      n = 0 ∨ n = 2 ∨ n = 4) := by
  decide +kernel

/-- **`4` is not a middle bound** for the `20` partial rounds with `diag d + J`,
`d = PicoKoalaBear.diag`: the trail of `trailStates` and `trailOutputs` (`trail_check`) starts
from a nonzero difference and charges `3` S-boxes. -/
theorem middle_bound_not_four :
    ¬ Hades.MiddleBound (diagPlusOnes (1 : F) diag) ({0} : Finset (Fin 16)) 20 4 :=
  Hades.MiddleBound.not_of_checkTrail (p := modulus) _ 0 20 4 diagonal trailStates trailOutputs
    internal rfl diag_eq_diagonal trail_check (by decide +kernel) (by decide +kernel)

/-- **`4` is not a middle bound for the code's internal layer**, which is `diag d + J`. -/
theorem internal_middle_bound_not_four :
    ¬ Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 16)) 20 4 := by
  rw [internal_toLinearMap]
  exact middle_bound_not_four

/-! ### A changed certificate is rejected -/

/-- `singles` with the multiplier `λ_0` of the certificate of the pattern `{5}` increased by one;
every other entry is unchanged. -/
def singlesCorrupted : List (List ℕ) :=
  singles.set 5 ((singles.getD 5 []).set 2 ((singles.getD 5 []).getD 2 0 + 1))

/-- The corrupted table differs from `singles`. -/
theorem singlesCorrupted_ne : singlesCorrupted ≠ singles := by
  decide +kernel

/-- **The checker rejects the corrupted certificate.** -/
theorem corrupted_rejected :
    Hades.RelationCheck.checkAll 2130706433 16 0 20 16 diagonal psi gamma singlesCorrupted pairs =
      false := by
  decide +kernel

end Poseidon2.PicoKoalaBear.MiddleChecks

/-! ### Axiom footprints -/

/-- info: 'Hades.IsTrail.window_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.IsTrail.window_relation

/-- info: 'Hades.refutations_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.refutations_of_pairs

/-- info: 'Hades.MiddleBound.of_relations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.of_relations

/-- info: 'Hades.MiddleBound.of_relationCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.of_relationCheck

/-- info: 'Hades.MiddleBound.not_of_checkTrail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.not_of_checkTrail

/-- info: 'Poseidon2.Certificates.KoalaBear.relations_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.KoalaBear.relations_check

/-- info: 'Poseidon2.Certificates.KoalaBear.trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.KoalaBear.trail_check

/-- info: 'Poseidon2.Certificates.PicoKoalaBear.relations_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.PicoKoalaBear.relations_check

/-- info: 'Poseidon2.Certificates.PicoKoalaBear.trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Certificates.PicoKoalaBear.trail_check

/-- info: 'Poseidon2.KoalaBear.middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.middle_bound

/-- info: 'Poseidon2.KoalaBear.internal_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.internal_middle_bound

/-- info: 'Poseidon2.KoalaBear.activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.activity_middle_general

/-- info: 'Poseidon2.KoalaBear.activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.activity_middle

/--
info: 'Poseidon2.KoalaBear.independent_key_probability_middle_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_middle_general

/-- info: 'Poseidon2.KoalaBear.independent_key_probability_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_middle

/--
info: 'Poseidon2.KoalaBear.independent_key_probability_middle_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_middle_exact_general

/--
info: 'Poseidon2.KoalaBear.independent_key_probability_middle_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_middle_exact

/-- info: 'Poseidon2.KoalaBear.middle_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.middle_sharp_exponent_bound

/--
info: 'Poseidon2.KoalaBear.independent_key_probability_middle_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_middle_sharp_general

/--
info: 'Poseidon2.KoalaBear.independent_key_probability_middle_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.independent_key_probability_middle_sharp

/-- info: 'Poseidon2.PicoKoalaBear.middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.middle_bound

/-- info: 'Poseidon2.PicoKoalaBear.internal_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.internal_middle_bound

/-- info: 'Poseidon2.PicoKoalaBear.activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.activity_middle_general

/-- info: 'Poseidon2.PicoKoalaBear.activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.activity_middle

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_probability_middle_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_middle_general

/-- info: 'Poseidon2.PicoKoalaBear.independent_key_probability_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_middle

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_probability_middle_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_middle_exact_general

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_probability_middle_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_middle_exact

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_probability_middle_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_middle_sharp_general

/--
info: 'Poseidon2.PicoKoalaBear.independent_key_probability_middle_sharp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.independent_key_probability_middle_sharp

/-- info: 'Poseidon2.KoalaBear.MiddleChecks.trail_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.MiddleChecks.trail_active

/-- info: 'Poseidon2.KoalaBear.MiddleChecks.middle_bound_not_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.MiddleChecks.middle_bound_not_four

/--
info: 'Poseidon2.KoalaBear.MiddleChecks.internal_middle_bound_not_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.MiddleChecks.internal_middle_bound_not_four

/-- info: 'Poseidon2.KoalaBear.MiddleChecks.middle_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.MiddleChecks.middle_sharp_exponent_succ_fails

/-- info: 'Poseidon2.KoalaBear.MiddleChecks.whole_bit_exponent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.MiddleChecks.whole_bit_exponent_le

/-- info: 'Poseidon2.KoalaBear.MiddleChecks.corrupted_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.MiddleChecks.corrupted_rejected

/-- info: 'Poseidon2.PicoKoalaBear.MiddleChecks.trail_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.MiddleChecks.trail_active

/-- info: 'Poseidon2.PicoKoalaBear.MiddleChecks.middle_bound_not_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.MiddleChecks.middle_bound_not_four

/--
info: 'Poseidon2.PicoKoalaBear.MiddleChecks.internal_middle_bound_not_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.MiddleChecks.internal_middle_bound_not_four

/-- info: 'Poseidon2.PicoKoalaBear.MiddleChecks.corrupted_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.MiddleChecks.corrupted_rejected
