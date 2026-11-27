/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon.Checks.Starknet

/-!
# Pinned axiom footprints for the Poseidon certificates

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of
`WideTrail.Poseidon`: the headline theorems of the Starknet certificate (`StarkPrimality.lean`,
`Starknet.lean`), the generic folding lemmas (`ConstantFolding.lean`), the equivalence of the
compressed schedule (`StarknetCompressed.lean`), the runner and its transfer lemmas
(`StarknetExecution.lean`), and the known-answer vectors, negative controls and exactness
checks of `Checks/Starknet.lean`. Every footprint is `[propext, Classical.choice, Quot.sound]` or
a subset of it, so none of these results uses `sorryAx` or `Lean.ofReduceBool`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves, and nothing here strengthens the claims of the certificate files. The module-based
audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Poseidon.AxiomChecks

/-! ### `StarkPrimality.lean` -/

/-- info: 'Poseidon.Starknet.modulus_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.modulus_eq

/-- info: 'Poseidon.Starknet.modulus_sub_one_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.modulus_sub_one_eq

/-- info: 'Poseidon.Starknet.modulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.modulus_prime

/-- info: 'Poseidon.Starknet.field_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.field_card

/-! ### `Starknet.lean`: S-box and linear layer -/

/-- info: 'Poseidon.Starknet.inverseExponent_equation' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon.Starknet.inverseExponent_equation

/-- info: 'Poseidon.Starknet.sbox_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.sbox_uniform

/-- info: 'Poseidon.Starknet.sbox_diffCount_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.sbox_diffCount_attained

/-- info: 'Poseidon.Starknet.sbox_not_uniform_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.sbox_not_uniform_one

/-- info: 'Poseidon.Starknet.eight_mul_inv8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.eight_mul_inv8

/-- info: 'Poseidon.Starknet.mds_eq_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_eq_mulVec

/-- info: 'Poseidon.Starknet.mds_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_symm_apply

/-- info: 'Poseidon.Starknet.adjugate_mul_mds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.adjugate_mul_mds

/-- info: 'Poseidon.Starknet.mds_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_det

/-- info: 'Poseidon.Starknet.mdsMatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mdsMatrix_transpose

/-- info: 'Poseidon.Starknet.mds_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_isMDS

/-- info: 'Poseidon.Starknet.mds_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_branch

/-- info: 'Poseidon.Starknet.mds_toLinearMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_toLinearMap_eq

/-- info: 'Poseidon.Starknet.mdsDiag_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mdsDiag_injOn

/-! ### `Starknet.lean`: the permutation and its bounds -/

/-- info: 'Poseidon.Starknet.permutation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutation_eq

/-- info: 'Poseidon.Starknet.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutation_bijective

/-- info: 'Poseidon.Starknet.permutation_bijective_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutation_bijective_general

/-- info: 'Poseidon.Starknet.rounds_apply_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.rounds_apply_full

/-- info: 'Poseidon.Starknet.rounds_apply_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.rounds_apply_partial

/-- info: 'Poseidon.Starknet.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.activity

/-- info: 'Poseidon.Starknet.activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.activity_general

/-- info: 'Poseidon.Starknet.mds_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_inactive_trivial

/-- info: 'Poseidon.Starknet.finrank_mds_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.finrank_mds_inactive

/-- info: 'Poseidon.Starknet.mds_inactive_two_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_inactive_two_ne_bot

/-- info: 'Poseidon.Starknet.activity_with_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.activity_with_partial

/-- info: 'Poseidon.Starknet.activity_with_partial_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.activity_with_partial_general

/-- info: 'Poseidon.Starknet.two_mul_two_pow_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.two_mul_two_pow_le_card

/-- info: 'Poseidon.Starknet.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability

/-- info: 'Poseidon.Starknet.independent_key_probability_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_general

/-- info: 'Poseidon.Starknet.probability_exponent' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon.Starknet.probability_exponent

/-- info: 'Poseidon.Starknet.independent_key_probability_outer_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_outer_exact

/--
info: 'Poseidon.Starknet.independent_key_probability_outer_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_outer_exact_general

/-- info: 'Poseidon.Starknet.independent_key_probability_with_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_with_partial

/--
info: 'Poseidon.Starknet.independent_key_probability_with_partial_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_with_partial_general

/-- info: 'Poseidon.Starknet.probability_exponent_with_partial' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon.Starknet.probability_exponent_with_partial

/-- info: 'Poseidon.Starknet.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_exact

/-- info: 'Poseidon.Starknet.independent_key_probability_exact_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_exact_general

/-- info: 'Poseidon.Starknet.sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.sharp_exponent_bound

/-- info: 'Poseidon.Starknet.independent_key_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_sharp

/-- info: 'Poseidon.Starknet.independent_key_probability_sharp_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_probability_sharp_general

/-- info: 'Poseidon.Starknet.independent_key_differential_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_differential_exact

/--
info: 'Poseidon.Starknet.independent_key_differential_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_differential_exact_general

/-- info: 'Poseidon.Starknet.differential_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.differential_sharp_exponent_bound

/-- info: 'Poseidon.Starknet.independent_key_differential_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_differential_sharp

/--
info: 'Poseidon.Starknet.independent_key_differential_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.independent_key_differential_sharp_general

/-! ### `ConstantFolding.lean` -/

/-- info: 'Poseidon.maskedEquiv_add_of_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.maskedEquiv_add_of_eq_zero

/-- info: 'Poseidon.roundSpec_apply_add_of_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.roundSpec_apply_add_of_eq_zero

/-- info: 'Poseidon.execute_eq_add_of_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.execute_eq_add_of_fold

/-- info: 'Poseidon.execute_eq_of_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.execute_eq_of_fold

/-- info: 'Poseidon.hadesSchedule_execute_eq_of_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.hadesSchedule_execute_eq_of_fold

/-! ### `StarknetCompressed.lean` -/

/-- info: 'Poseidon.Starknet.compressedRounds_apply_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressedRounds_apply_partial

/-- info: 'Poseidon.Starknet.compressed_partial_constants_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressed_partial_constants_zero

/-- info: 'Poseidon.Starknet.compressedValues_eq_values_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressedValues_eq_values_full

/-- info: 'Poseidon.Starknet.compressedValues_ne_values_87' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressedValues_ne_values_87

/-- info: 'Poseidon.Starknet.compressedValues_ne_values_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressedValues_ne_values_partial

/-- info: 'Poseidon.Starknet.compressedValues_ne_values_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressedValues_ne_values_5

/-- info: 'Poseidon.Starknet.fold_mask_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.fold_mask_zero

/-- info: 'Poseidon.Starknet.fold_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.fold_next

/-- info: 'Poseidon.Starknet.compressedPermutation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressedPermutation_eq

/-- info: 'Poseidon.Starknet.compressedPermutation_eq_permutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.compressedPermutation_eq_permutation

/-- info: 'Poseidon.Starknet.keyed_compressed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.keyed_compressed_eq

/-- info: 'Poseidon.Starknet.keyCount_compressed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.keyCount_compressed_eq

/-! ### `StarknetExecution.lean` -/

/-- info: 'Poseidon.Starknet.mixT_eq_dotMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mixT_eq_dotMod

/-- info: 'Poseidon.Starknet.dotMod_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.dotMod_toState

/-- info: 'Poseidon.Starknet.cubeLast_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.cubeLast_toState

/-- info: 'Poseidon.Starknet.roundDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.roundDense_toState

/-- info: 'Poseidon.Starknet.executeDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.executeDense_toState

/-- info: 'Poseidon.Starknet.permutationWith_eq_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutationWith_eq_of_dense

/-- info: 'Poseidon.Starknet.permutationWith_ne_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutationWith_ne_of_dense

/-- info: 'Poseidon.Starknet.permutation_eq_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutation_eq_of_dense

/-- info: 'Poseidon.Starknet.permutation_ne_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutation_ne_of_dense

/-- info: 'Poseidon.Starknet.permutation_mds_ne_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.permutation_mds_ne_of_dense

/-! ### `Checks/Starknet.lean`: known-answer vectors -/

/-- info: 'Poseidon.Starknet.Checks.zeroOutput_eq_cryptoexperts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.zeroOutput_eq_cryptoexperts

/-- info: 'Poseidon.Starknet.Checks.zero_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.zero_vector

/-- info: 'Poseidon.Starknet.Checks.lambdaworks_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.lambdaworks_vector

/-- info: 'Poseidon.Starknet.Checks.corelib_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.corelib_vector

/-- info: 'Poseidon.Starknet.Checks.compressed_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.compressed_vectors

/-! ### `Checks/Starknet.lean`: negative controls -/

/-- info: 'Poseidon.Starknet.Checks.zero_vector_fails_sbox_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.zero_vector_fails_sbox_first

/--
info: 'Poseidon.Starknet.Checks.lambdaworks_vector_fails_sbox_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.lambdaworks_vector_fails_sbox_first

/-- info: 'Poseidon.Starknet.Checks.corelib_vector_fails_sbox_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.corelib_vector_fails_sbox_first

/-- info: 'Poseidon.Starknet.Checks.zero_vector_fails_plus_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.zero_vector_fails_plus_two

/-- info: 'Poseidon.Starknet.Checks.lambdaworks_vector_fails_plus_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.lambdaworks_vector_fails_plus_two

/-- info: 'Poseidon.Starknet.Checks.corelib_vector_fails_plus_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.corelib_vector_fails_plus_two

/--
info: 'Poseidon.Starknet.Checks.lambdaworks_vector_fails_initial_layer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.lambdaworks_vector_fails_initial_layer

/-- info: 'Poseidon.Starknet.Checks.corelib_vector_fails_initial_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.corelib_vector_fails_initial_layer

/-- info: 'Poseidon.Starknet.Checks.zero_vector_blind_to_initial_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.zero_vector_blind_to_initial_layer

/--
info: 'Poseidon.Starknet.Checks.lambdaworks_vector_fails_partial_at_two_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.lambdaworks_vector_fails_partial_at_two_only

/--
info: 'Poseidon.Starknet.Checks.lambdaworks_vector_fails_transposed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.lambdaworks_vector_fails_transposed

/-! ### `Checks/Starknet.lean`: exactness and cross-checks -/

/-- info: 'Poseidon.Starknet.Checks.whole_bits_succ_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.whole_bits_succ_fails

/-- info: 'Poseidon.Starknet.Checks.outer_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.outer_sharp_exponent_bound

/-- info: 'Poseidon.Starknet.Checks.outer_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.outer_sharp_exponent_succ_fails

/-- info: 'Poseidon.Starknet.Checks.sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.sharp_exponent_succ_fails

/-- info: 'Poseidon.Starknet.Checks.differential_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.differential_sharp_exponent_succ_fails

/-- info: 'Poseidon.Starknet.Checks.mds_not_branch_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.mds_not_branch_five

/-- info: 'Poseidon.Starknet.Checks.mdsInt_minors_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.mdsInt_minors_one

/-- info: 'Poseidon.Starknet.Checks.mdsInt_minors_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.mdsInt_minors_two

/-- info: 'Poseidon.Starknet.Checks.mdsInt_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.mdsInt_det

/-- info: 'Poseidon.Starknet.Checks.finrank_inactive_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.finrank_inactive_one

/-- info: 'Poseidon.Starknet.Checks.finrank_inactive_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.finrank_inactive_two

/-- info: 'Poseidon.Starknet.Checks.values_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.values_ne_zero

/-- info: 'Poseidon.Starknet.Checks.values_partial_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.values_partial_ne_zero

/-- info: 'Poseidon.Starknet.Checks.values_zero_eq_air' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.values_zero_eq_air

/-- info: 'Poseidon.Starknet.Checks.values_four_two_eq_air' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.values_four_two_eq_air

/-- info: 'Poseidon.Starknet.Checks.modulus_hex' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.modulus_hex

/-- info: 'Poseidon.Starknet.Checks.inverseExponent_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.inverseExponent_eq

/-- info: 'Poseidon.Starknet.Checks.modulus_sub_one_mod_three' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.modulus_sub_one_mod_three

/-- info: 'Poseidon.Starknet.Checks.mdsMatrix_symmetric_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.Checks.mdsMatrix_symmetric_ne

end Poseidon.AxiomChecks
