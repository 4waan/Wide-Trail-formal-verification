/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BN254Middle
import WideTrail.Poseidon2.KoalaBear
import WideTrail.Poseidon2.BabyBear

/-!
# Pinned axiom footprints for the Poseidon2 certificates

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of
`WideTrail.Poseidon2` that is not pinned elsewhere: the headline theorems of the BN254
certificate (`BN254.lean`, `BN254Middle.lean`), and the results of the generic Plonky3 model and
of the KoalaBear and BabyBear instances that the pins at the ends of `Checks/Plonky3.lean`,
`Checks/KoalaBear.lean` and `Checks/BabyBear.lean` do not cover. The BN254 pins include the
internal matrix as `diag (1, 1, 2) + J` and the diagonal-criterion results of
`BN254Middle.lean`. Every footprint is `[propext, Classical.choice, Quot.sound]` or a subset of
it (`BN254.sharp_exponent_bound` uses `propext` only), so none of these results uses `sorryAx`
or `Lean.ofReduceBool`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves, and nothing here strengthens the claims of the certificate files. The module-based
audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Poseidon2.AxiomChecks

/-! ### BN254 -/

/-- info: 'Poseidon2.BN254.sbox_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.sbox_uniform

/-- info: 'Poseidon2.BN254.external_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.external_branch

/-- info: 'Poseidon2.BN254.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.permutation_bijective

/-- info: 'Poseidon2.BN254.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.activity

/-- info: 'Poseidon2.BN254.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability

/-- info: 'Poseidon2.BN254.internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.internal_inactive_trivial

/-- info: 'Poseidon2.BN254.activity_with_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.activity_with_partial

/-- info: 'Poseidon2.BN254.independent_key_probability_with_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_with_partial

/-- info: 'Poseidon2.BN254.internal_toLinearMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.internal_toLinearMap_eq

/-- info: 'Poseidon2.BN254.internalDiag_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.internalDiag_injOn

/-- info: 'Poseidon2.BN254.internal_inactive_trivial_by_criterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.internal_inactive_trivial_by_criterion

/-- info: 'Poseidon2.BN254.finrank_internal_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.finrank_internal_inactive

/-! ### The generic Plonky3 model -/

/-- info: 'Poseidon2.Plonky3.inactiveSpace_internal_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.inactiveSpace_internal_ne_bot

/-- info: 'Poseidon2.Plonky3.three_le_finrank_inactiveSpace_thirteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.three_le_finrank_inactiveSpace_thirteen

/-- info: 'Poseidon2.Plonky3.rounds_roundValues_apply_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.rounds_roundValues_apply_middle

/-! ### The KoalaBear and BabyBear instances -/

/-- info: 'Poseidon2.KoalaBear.external_eq_mdsLight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.external_eq_mdsLight

/-- info: 'Poseidon2.BabyBear.external_eq_mdsLight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.external_eq_mdsLight

end Poseidon2.AxiomChecks

/-! ### BN254: the exact ratio and the sharp exponent -/

/-- info: 'Poseidon2.BN254.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_exact

/-- info: 'Poseidon2.BN254.sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.BN254.sharp_exponent_bound

/-- info: 'Poseidon2.BN254.independent_key_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_probability_sharp

/-! ### BN254: the independent-key differential bound -/

/-- info: 'Poseidon2.BN254.independent_key_differential_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_differential_exact

/-- info: 'Poseidon2.BN254.differential_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.BN254.differential_sharp_exponent_bound

/-- info: 'Poseidon2.BN254.independent_key_differential_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.independent_key_differential_sharp

/-! ### Plonky3: states whose four blocks sum to zero -/

/-- info: 'Poseidon2.Plonky3.positionSums_mat4Blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.positionSums_mat4Blocks

/-- info: 'Poseidon2.Plonky3.mem_blockSumZeroFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.mem_blockSumZeroFlat

/-- info: 'Poseidon2.Plonky3.external_eq_mat4Blocks_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_eq_mat4Blocks_of_mem

/-- info: 'Poseidon2.Plonky3.positionSums_mat4Blocks_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.positionSums_mat4Blocks_eq_zero_iff

/-- info: 'Poseidon2.Plonky3.external_eq_mat4Blocks_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_eq_mat4Blocks_iff

/-! ### Plonky3: transposes of the two layers -/

/-- info: 'Poseidon2.Plonky3.external_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_dotProduct

/-- info: 'Poseidon2.Plonky3.external_transpose_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_transpose_isBranchBound

/-- info: 'Poseidon2.Plonky3.internal_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.internal_dotProduct
