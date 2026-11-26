/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Checks.Toy
import WideTrail.Hades.Subspace
import WideTrail.Hades.Krylov

/-!
# Pinned axiom footprints for the HADES model and its checks

These guards cover actual execution semantics, activity bounds, finite witnesses,
missing-assumption counterexamples, the independent-key trail bounds of `Probability.lean`, and
the inactive-space results of `Subspace.lean` and `Krylov.lean`. `card_sub_le_finrank_inactiveSpace`
is pinned in `WideTrail.Poseidon2.Checks.Plonky3`, `inactiveSpace_eq_bot_of_krylov` and
`inactiveSpace_diagPlusOnes_eq_bot` in `WideTrail.Hades.Checks.Krylov`, and the results of
`Dimension.lean` in `WideTrail.Hades.Checks.Dimension`. The module-based CI audit additionally
checks every project declaration, including generated declarations.
-/

/-- info: 'Hades.masked_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.masked_support

/-- info: 'Hades.masked_difference_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.masked_difference_of_not_mem

/-- info: 'Hades.execute_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.execute_bijective

/-- info: 'Hades.nonlinearDifference_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.nonlinearDifference_support

/-- info: 'Hades.nonlinearDifference_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.nonlinearDifference_outside

/-- info: 'Hades.hadesMask_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hadesMask_middle

/-- info: 'Hades.hadesMask_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hadesMask_suffix

/-- info: 'Hades.pair_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.pair_sum_bound

/-- info: 'Hades.fullRound_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.fullRound_pair

/-- info: 'Hades.fullWindow_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.fullWindow_bound

/-- info: 'Hades.outerRound_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.outerRound_bound

/-- info: 'Hades.hades_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_bound

/-- info: 'Hades.branch_of_mds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.branch_of_mds

/-- info: 'Hades.hades_mds_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_mds_bound

/-- info: 'Hades.symmetric_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.symmetric_bound

/-- info: 'Hades.Toy.matrix_mds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.matrix_mds

/-- info: 'Hades.Toy.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.bound

/-- info: 'Hades.Toy.bound_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.bound_decide

/-- info: 'Hades.Toy.minimum_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.minimum_witness

/-- info: 'Hades.Toy.masked_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.masked_witness

/-- info: 'Hades.Toy.unmasked_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.unmasked_witness

/-- info: 'Hades.Toy.identity_mix_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.identity_mix_fails

/-- info: 'Hades.Toy.singular_middle_collapses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.singular_middle_collapses

/-- info: 'Hades.Toy.singular_middle_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.singular_middle_fails

/-- info: 'Hades.Toy.odd_zero_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.odd_zero_middle

/-- info: 'Hades.Toy.omitted_final_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.Toy.omitted_final_mix

/-! ### Independent-key trail bounds -/

/-- info: 'Hades.keyCount_weight_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.keyCount_weight_bound

/-- info: 'Hades.hades_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_probability

/-! ### Inactive propagation through partial rounds -/

/-- info: 'Hades.IsTrail.free_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.IsTrail.free_window

/-- info: 'Hades.inactiveSpace_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_ne_bot

/-- info: 'Hades.outer_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.outer_middle_bound

/-- info: 'Hades.hades_probability_with_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_probability_with_middle

/-- info: 'Hades.mem_inactiveSpace_singleton_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.mem_inactiveSpace_singleton_iff

/-- info: 'Hades.inactiveSpace_diagPlusOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_diagPlusOnes

/-! ### Independent-key trail bounds as exact ratios -/

/-- info: 'Hades.mul_le_of_ratio' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Hades.mul_le_of_ratio

/-- info: 'Hades.keyCount_le_card_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.keyCount_le_card_pow

/-- info: 'Hades.keyCount_weight_bound_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.keyCount_weight_bound_exact

/-- info: 'Hades.keyCount_weight_bound_exact_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.keyCount_weight_bound_exact_of_le

/-- info: 'Hades.hades_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_probability_exact

/-- info: 'Hades.hades_probability_with_middle_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_probability_with_middle_exact

/-! ### The per-round count behind both trail bounds -/

/-- info: 'Hades.scheduledWeight_le_mul_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.scheduledWeight_le_mul_card

/-- info: 'Hades.keyCount_le_pow_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.keyCount_le_pow_mul_pow
