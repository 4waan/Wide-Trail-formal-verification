/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Rijndael.Checks.Probability

/-!
# Pinned axiom footprints for the Rijndael-256 and AES probability bounds

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one declaration of
`Rijndael/Probability.lean` or `Rijndael/Checks/Probability.lean`. Every footprint is
`[propext, Classical.choice, Quot.sound]` or a subset of it, so none of these results uses
`sorryAx` or `Lean.ofReduceBool`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves. The module-based audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Rijndael.ProbabilityAxiomChecks

/-! ### Trail probabilities, two-round differentials and the final round (`Probability.lean`) -/

/-- info: 'Rijndael.card_gridIdx48' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.card_gridIdx48

/-- info: 'Rijndael.card_state256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.card_state256

/-- info: 'Rijndael.rijndael256Lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256Lin

/-- info: 'Rijndael.rijndael256Lin_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256Lin_apply

/-- info: 'Rijndael.rijndael256Lin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256Lin_isBranchBound

/-- info: 'Rijndael.aesLin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aesLin_isBranchBound

/-- info: 'Rijndael.bricklayer_bijective' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.bricklayer_bijective

/-- info: 'Rijndael.rijndael256_rounds_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_rounds_prob

/-- info: 'Rijndael.rijndael256_four_round_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_four_round_prob

/-- info: 'Rijndael.rijndael256_eight_round_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_eight_round_prob

/-- info: 'Rijndael.rijndael256_fourteen_round_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_fourteen_round_prob

/-- info: 'Rijndael.mul_two_pow_24_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mul_two_pow_24_le

/-- info: 'Rijndael.rijndael256_two_round_differential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_two_round_differential

/-- info: 'Rijndael.rijndael256_differential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_differential

/-- info: 'Rijndael.aes128_two_round_differential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes128_two_round_differential

/-- info: 'Rijndael.aes128_differential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes128_differential

/-- info: 'Rijndael.transposeAddEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.transposeAddEquiv

/-- info: 'Rijndael.shiftRows256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.shiftRows256

/-- info: 'Rijndael.aesShiftRows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aesShiftRows

/-- info: 'Rijndael.rijndael256Lin_eq_mixColumns_shiftRows256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256Lin_eq_mixColumns_shiftRows256

/-- info: 'Rijndael.aesLin_eq_aesMixColumns_aesShiftRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aesLin_eq_aesMixColumns_aesShiftRows

/-- info: 'Rijndael.lastRoundSchedule' does not depend on any axioms -/
#guard_msgs in
#print axioms Rijndael.lastRoundSchedule

/-- info: 'Rijndael.lastRoundSchedule_of_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms Rijndael.lastRoundSchedule_of_ne

/-- info: 'Rijndael.lastRoundSchedule_last' does not depend on any axioms -/
#guard_msgs in
#print axioms Rijndael.lastRoundSchedule_last

/-- info: 'Rijndael.relabelLast' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.relabelLast

/-- info: 'Rijndael.relabelLast_of_ne' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.relabelLast_of_ne

/-- info: 'Rijndael.trailKeyCount_lastRoundSchedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.trailKeyCount_lastRoundSchedule

/-- info: 'Rijndael.relabelLast_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.relabelLast_zero

/-- info: 'Rijndael.rijndael256_fourteen_round_prob_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_fourteen_round_prob_final

/-- info: 'Rijndael.aes128_ten_round_prob_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes128_ten_round_prob_final

/-- info: 'Rijndael.aes192_twelve_round_prob_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes192_twelve_round_prob_final

/-- info: 'Rijndael.aes256_fourteen_round_prob_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes256_fourteen_round_prob_final

/-- info: 'Rijndael.rijndael256_four_round_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_four_round_probability

/-- info: 'Rijndael.rijndael256_eight_round_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_eight_round_probability

/-- info: 'Rijndael.rijndael256_fourteen_round_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_fourteen_round_probability

/-- info: 'Rijndael.rijndael256_fourteen_round_probability_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_fourteen_round_probability_final

/-- info: 'Rijndael.aes128_ten_round_probability_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes128_ten_round_probability_final

/-- info: 'Rijndael.aes192_twelve_round_probability_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes192_twelve_round_probability_final

/-- info: 'Rijndael.aes256_fourteen_round_probability_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.aes256_fourteen_round_probability_final


/-! ### Controls (`Checks/Probability.lean`) -/

/-- info: 'Rijndael.Checks.exponent_seven_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.exponent_seven_fails

/-- info: 'Rijndael.Checks.sbox_uniformity_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.sbox_uniformity_ge

/-- info: 'Rijndael.Checks.sbox_diff_clears_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.sbox_diff_clears_iff

/-- info: 'Rijndael.Checks.not_exists_sbox_diff_clears_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.not_exists_sbox_diff_clears_seven

/-- info: 'Rijndael.Checks.trailExponent' does not depend on any axioms -/
#guard_msgs in
#print axioms Rijndael.Checks.trailExponent

/-- info: 'Rijndael.Checks.trailExponent_values' does not depend on any axioms -/
#guard_msgs in
#print axioms Rijndael.Checks.trailExponent_values

/-- info: 'Rijndael.Checks.trailExponent_le_of_lt_eight' does not depend on any axioms -/
#guard_msgs in
#print axioms Rijndael.Checks.trailExponent_le_of_lt_eight

/-- info: 'Rijndael.Checks.trailExponent_eight' does not depend on any axioms -/
#guard_msgs in
#print axioms Rijndael.Checks.trailExponent_eight

/-- info: 'Rijndael.Checks.rounds_prob_trailExponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.rounds_prob_trailExponent

/-- info: 'Rijndael.Checks.trailKeyCount_zero_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.trailKeyCount_zero_seq

/-- info: 'Rijndael.Checks.diffKeyCount_zero_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.diffKeyCount_zero_zero

/-- info: 'Rijndael.Checks.four_round_prob_needs_h0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.four_round_prob_needs_h0

/-- info: 'Rijndael.Checks.two_round_differential_needs_ha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.two_round_differential_needs_ha

/-- info: 'Rijndael.Checks.final_prob_needs_h0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.final_prob_needs_h0

/-- info: 'Rijndael.Checks.final_schedule_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.final_schedule_of_lt

/-- info: 'Rijndael.Checks.weight_shiftRows256_e30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.weight_shiftRows256_e30

/-- info: 'Rijndael.Checks.final_schedule_last_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.final_schedule_last_ne

/-- info: 'Rijndael.Checks.medp_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.medp_between

/-- info: 'Rijndael.Checks.medp_below_coarse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.medp_below_coarse

end Rijndael.ProbabilityAxiomChecks
