/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Checks.ToySpec
import WideTrail.Linear.Checks.ToyNat

/-!
# Pinned axiom footprints for linear trails and hulls

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of
`Trail.lean`, `Hull.lean`, `Checks/ToyOne.lean`, `Checks/Toy.lean`, `Checks/ToySpec.lean` or
`Checks/ToyNat.lean`. Every footprint is `[propext, Classical.choice, Quot.sound]` or a subset
of it, so none of these results uses `sorryAx` or `Lean.ofReduceBool`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves. The module-based audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Linear.TrailAxiomChecks

/-! ### Trails -/

/-- info: 'Linear.walsh_keyedRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_keyedRound

/-- info: 'Linear.walsh_run_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_run_succ

/-- info: 'Linear.walsh_run_eq_sum_trails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_run_eq_sum_trails

/-- info: 'Linear.isTrail_of_trailCorr_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.isTrail_of_trailCorr_ne_zero

/-- info: 'Linear.natAbs_trailPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.natAbs_trailPhase

/-- info: 'Linear.natAbs_trailCorr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.natAbs_trailCorr_le

/-- info: 'Linear.natAbs_trailCorr_mul_card_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.natAbs_trailCorr_mul_card_pow_le

/-- info: 'Linear.natAbs_trailCorr_mul_card_pow_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.natAbs_trailCorr_mul_card_pow_le_of_le

/-- info: 'Linear.natAbs_trailCorr_mul_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.natAbs_trailCorr_mul_pow_le

/-- info: 'Linear.trailCorr_le_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.trailCorr_le_of_spec

/-- info: 'Linear.trailCorr_ratio_le_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.trailCorr_ratio_le_of_spec

/-! ### The hull -/

/-- info: 'Linear.Pairing.Separating.add_self_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Pairing.Separating.add_self_eq_zero

/-- info: 'Linear.sum_sq_sum_walsh_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_sq_sum_walsh_run

/-- info: 'Linear.elpCount_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_zero

/-- info: 'Linear.elpCount_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_succ

/-- info: 'Linear.elpCount_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_add

/-- info: 'Linear.elpCount_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_one

/-- info: 'Linear.elpCount_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_two

/-- info: 'Linear.elpCount_succ_eq_sum_trails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_succ_eq_sum_trails

/-- info: 'Linear.run_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.run_injective

/-- info: 'Linear.sum_elpCount_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_elpCount_left

/-- info: 'Linear.sum_elpCount_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_elpCount_right

/-- info: 'Linear.elpCount_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_zero_right

/-- info: 'Linear.elpCount_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_window_bound

/-- info: 'Linear.elpCount_two_round_bound_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_two_round_bound_of_eq

/-- info: 'Linear.elpCount_two_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_two_round_bound

/-- info: 'Linear.elpCount_bound_of_two_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.elpCount_bound_of_two_rounds

/-! ### Toy checks -/

/-- info: 'Linear.Checks.one_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.one_expansion

/-- info: 'Linear.Checks.one_expansion_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.one_expansion_direct

/-- info: 'Linear.Checks.one_elpCount_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.one_elpCount_direct

/-- info: 'Linear.Checks.one_elpCount_via_nyberg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.one_elpCount_via_nyberg

/-- info: 'Linear.Checks.one_nyberg_fails_zeroPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.one_nyberg_fails_zeroPairing

/-- info: 'Linear.Checks.toy_two_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_two_round_bound

/-- info: 'Linear.Checks.toy_elp_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_elp_attained

/-- info: 'Linear.Checks.toy_bound_fails_branch_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_bound_fails_branch_four

/-- info: 'Linear.Checks.toy_fixed_exceeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_fixed_exceeds

/-- info: 'Linear.Checks.toy_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_sign

/-- info: 'Linear.Checks.toy_nonbijective_exceeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_nonbijective_exceeds

/-- info: 'Linear.Checks.toy_bridge_fails_nonbijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_bridge_fails_nonbijective

/-- info: 'Linear.Checks.toy_trail_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_trail_bound

/-- info: 'Linear.Checks.toy_trail_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_trail_attained

/-- info: 'Linear.Checks.toy_trail_bound_fails_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_trail_bound_fails_two

/-! ### The toy as a wide-trail specification, and further hypothesis checks -/

/-- info: 'Linear.Checks.toyMaskSpec_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toyMaskSpec_lin

/-- info: 'Linear.Checks.toy_isTrail_of_trailCorr_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_isTrail_of_trailCorr_ne_zero

/-- info: 'Linear.Checks.toy_trailCorr_le_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_trailCorr_le_of_spec

/-- info: 'Linear.Checks.toy_trailCorr_ratio_le_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_trailCorr_ratio_le_of_spec

/-- info: 'Linear.Checks.toy_three_round_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_three_round_bound

/-- info: 'Linear.Checks.toy_not_isTrail_nonbijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_not_isTrail_nonbijective

/-- info: 'Linear.Checks.toy_bridge_fails_nonbijective_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_bridge_fails_nonbijective_spec

/-- info: 'Linear.Checks.toy_bound_fails_zero_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_bound_fails_zero_mask

/-- info: 'Linear.Checks.toy_bound_fails_linearity_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_bound_fails_linearity_two

/-- info: 'Linear.Checks.one_expansion_fails_zeroPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.one_expansion_fails_zeroPairing

/-! ### The numerical cross-check -/

/-- info: 'Linear.ToyNat.all_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.ToyNat.all_le

/-- info: 'Linear.ToyNat.elp_max' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.ToyNat.elp_max

/-- info: 'Linear.ToyNat.not_all_le_pred' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.ToyNat.not_all_le_pred

end Linear.TrailAxiomChecks
