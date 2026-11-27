/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Poseidon2
import WideTrail.Linear.Poseidon
import WideTrail.Linear.Checks.Hades

/-!
# Pinned axiom footprints for the linear trails of HADES rounds

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of
`Linear/Hades.lean`, `Linear/Poseidon2.lean`, `Linear/Poseidon.lean` or `Linear/Checks/Hades.lean`.
Every footprint is `[propext, Classical.choice, Quot.sound]`, so none of these results uses
`sorryAx` or `Lean.ofReduceBool`.

`Linear/Field.lean` is not pinned here: it is the only module that imports `Mathlib.Analysis`,
and it belongs to the library `WideTrailHeavy`, not to the default library. The module-based
audit `scripts/AuditAxiomsHeavy.lean` covers its declarations.

These guards record which axioms the proofs use; they say nothing about the statements
themselves.
-/

set_option autoImplicit false

namespace Linear.HadesAxiomChecks

/-! ### Masks, adjoints and branch numbers (`Hades.lean`) -/

/-- info: 'Hades.transposeLin_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.transposeLin_dotProduct

/-- info: 'Hades.maskLin_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.maskLin_dotProduct

/-- info: 'Hades.maskLin_symm_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.maskLin_symm_dotProduct

/-- info: 'Hades.maskLin_symm_eq_of_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.maskLin_symm_eq_of_dotProduct

/-- info: 'Hades.maskLin_eq_symm_of_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.maskLin_eq_symm_of_selfAdjoint

/-- info: 'Hades.dotProduct_of_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.dotProduct_of_mulVec

/-- info: 'Hades.selfAdjoint_of_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.selfAdjoint_of_mulVec

/-- info: 'Hades.isAdjoint_of_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isAdjoint_of_dotProduct

/-- info: 'Hades.isAdjoint_maskLin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isAdjoint_maskLin

/-- info: 'Hades.isBranchBound_maskLin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isBranchBound_maskLin_iff

/-- info: 'Hades.isBranchBound_maskLin_iff_of_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isBranchBound_maskLin_iff_of_selfAdjoint

/-- info: 'Hades.isBranchBound_maskLin_of_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isBranchBound_maskLin_of_isMDS

/-- info: 'Hades.isLinBranchBound_iff_maskLin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isLinBranchBound_iff_maskLin

/-- info: 'Hades.maskSchedule_hadesSchedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.maskSchedule_hadesSchedule

/-- info: 'Hades.scheduledWeight_maskSchedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.scheduledWeight_maskSchedule

/-- info: 'Hades.isTrail_maskSchedule_iff_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isTrail_maskSchedule_iff_backward

/-! ### Walsh values, the bridge and the expansion (`Hades.lean`) -/

/-- info: 'Hades.walsh_roundGamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.walsh_roundGamma

/-- info: 'Hades.walsh_masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.walsh_masked

/-- info: 'Hades.isTrail_of_trailCorr_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isTrail_of_trailCorr_ne_zero

/-- info: 'Hades.isTrail_of_linCorr_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.isTrail_of_linCorr_ne_zero

/-- info: 'Hades.walsh_run_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.walsh_run_eq_sum_linCorr

/-- info: 'Hades.run_zero_eq_execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.run_zero_eq_execute

/-- info: 'Hades.walsh_execute_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.walsh_execute_eq_sum_linCorr

/-- info: 'Hades.walsh_comp_linearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.walsh_comp_linearEquiv

/-- info: 'Hades.walsh_comp_execute_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.walsh_comp_execute_eq_sum_linCorr


/-! ### Inverses, activity and bounds (`Hades.lean`) -/

/-- info: 'Hades.inactiveSpace_symm_eq_bot_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.inactiveSpace_symm_eq_bot_iff

/-- info: 'Hades.MiddleBound.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.symm

/-- info: 'Hades.middleBound_symm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.middleBound_symm_iff

/-- info: 'Hades.MiddleBound.maskLin_of_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.MiddleBound.maskLin_of_selfAdjoint

/-- info: 'Hades.hades_linear_outer_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_linear_outer_activity

/-- info: 'Hades.hades_linear_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_linear_activity

/-- info: 'Linear.abv_walsh_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.abv_walsh_le_card

/-- info: 'Linear.mul_pow_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.mul_pow_le_of_le

/-- info: 'Hades.abv_walsh_roundGamma_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.abv_walsh_roundGamma_le

/-- info: 'Hades.abv_linCorr_le_card_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.abv_linCorr_le_card_pow

/-- info: 'Hades.abv_linCorr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.abv_linCorr_le

/-- info: 'Hades.abv_linCorr_mul_card_pow_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.abv_linCorr_mul_card_pow_le_of_le

/-- info: 'Hades.hades_linear_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_linear_bound


/-! ### The Plonky3 layers (`Poseidon2.lean`) -/

/-- info: 'Poseidon2.Plonky3.external_maskLin_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_maskLin_symm_apply

/-- info: 'Poseidon2.Plonky3.external_maskLin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_maskLin_isBranchBound

/-- info: 'Poseidon2.Plonky3.external_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_isLinBranchBound

/-- info: 'Poseidon2.Plonky3.Diag.internal_maskLin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.internal_maskLin

/-- info: 'Poseidon2.Plonky3.Diag.maskLin_middleBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.maskLin_middleBound

/-- info: 'Poseidon2.Plonky3.Diag.linear_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.linear_activity

/-- info: 'Poseidon2.Plonky3.Diag.linear_activity_with_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.linear_activity_with_middle_bound

/-- info: 'Poseidon2.Plonky3.Diag.linear_bound_with_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.linear_bound_with_middle_bound

/-- info: 'Poseidon2.Plonky3.Diag.linear_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Diag.linear_bound


/-! ### SP1 KoalaBear (`Poseidon2.lean`) -/

/-- info: 'Poseidon2.KoalaBear.external_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.external_isLinBranchBound

/-- info: 'Poseidon2.KoalaBear.linear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.linear_activity_general

/-- info: 'Poseidon2.KoalaBear.linear_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.linear_activity_middle_general

/-- info: 'Poseidon2.KoalaBear.linear_activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.linear_activity_middle

/-- info: 'Poseidon2.KoalaBear.linear_bound_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.linear_bound_middle_general

/-- info: 'Poseidon2.KoalaBear.walsh_permutation_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.KoalaBear.walsh_permutation_eq_sum_linCorr


/-! ### Pico KoalaBear (`Poseidon2.lean`) -/

/-- info: 'Poseidon2.PicoKoalaBear.external_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.external_isLinBranchBound

/-- info: 'Poseidon2.PicoKoalaBear.linear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.linear_activity_general

/-- info: 'Poseidon2.PicoKoalaBear.linear_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.linear_activity_middle_general

/-- info: 'Poseidon2.PicoKoalaBear.linear_activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.linear_activity_middle

/-- info: 'Poseidon2.PicoKoalaBear.linear_bound_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.linear_bound_middle_general

/-- info: 'Poseidon2.PicoKoalaBear.walsh_permutation_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.PicoKoalaBear.walsh_permutation_eq_sum_linCorr


/-! ### SP1 BabyBear (`Poseidon2.lean`) -/

/-- info: 'Poseidon2.BabyBear.external_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.external_isLinBranchBound

/-- info: 'Poseidon2.BabyBear.linear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.linear_activity_general

/-- info: 'Poseidon2.BabyBear.linear_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.linear_activity

/-- info: 'Poseidon2.BabyBear.linear_bound_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.linear_bound_general

/-- info: 'Poseidon2.BabyBear.walsh_permutation_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BabyBear.walsh_permutation_eq_sum_linCorr


/-! ### OpenVM BabyBear (`Poseidon2.lean`) -/

/-- info: 'Poseidon2.OpenVMBabyBear.external_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.external_isLinBranchBound

/-- info: 'Poseidon2.OpenVMBabyBear.linear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.linear_activity_general

/-- info: 'Poseidon2.OpenVMBabyBear.linear_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.linear_activity

/-- info: 'Poseidon2.OpenVMBabyBear.linear_bound_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.linear_bound_general

/-- info: 'Poseidon2.OpenVMBabyBear.walsh_permutation_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.OpenVMBabyBear.walsh_permutation_eq_sum_linCorr


/-! ### HorizenLabs BN254 width three (`Poseidon2.lean`) -/

/-- info: 'Poseidon2.BN254.externalMatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.externalMatrix_transpose

/-- info: 'Poseidon2.BN254.internalMatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.internalMatrix_transpose

/-- info: 'Poseidon2.BN254.external_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.external_selfAdjoint

/-- info: 'Poseidon2.BN254.internal_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.internal_selfAdjoint

/-- info: 'Poseidon2.BN254.maskLin_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_external

/-- info: 'Poseidon2.BN254.maskLin_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_internal

/-- info: 'Poseidon2.BN254.maskLin_external_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_external_isBranchBound

/-- info: 'Poseidon2.BN254.maskLin_internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_internal_inactive_trivial

/-- info: 'Poseidon2.BN254.maskLin_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_middle_bound

/-- info: 'Poseidon2.BN254.maskLin_full_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_full_prefix

/-- info: 'Poseidon2.BN254.maskLin_full_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_full_suffix

/-- info: 'Poseidon2.BN254.external_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.external_isLinBranchBound

/-- info: 'Poseidon2.BN254.linear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.linear_activity_general

/-- info: 'Poseidon2.BN254.linear_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.linear_activity_middle_general

/-- info: 'Poseidon2.BN254.linear_activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.linear_activity_middle

/-- info: 'Poseidon2.BN254.linear_bound_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.linear_bound_middle_general

/-- info: 'Poseidon2.BN254.walsh_permutation_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.walsh_permutation_eq_sum_linCorr


/-! ### Aztec BN254 width four (`Poseidon2.lean`) -/

/-- info: 'Poseidon2.AztecBN254.hlMat4_transpose_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.hlMat4_transpose_isBranchBound

/-- info: 'Poseidon2.AztecBN254.maskLin_external_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.maskLin_external_symm_apply

/-- info: 'Poseidon2.AztecBN254.maskLin_external_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.maskLin_external_isBranchBound

/-- info: 'Poseidon2.AztecBN254.internal_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.internal_selfAdjoint

/-- info: 'Poseidon2.AztecBN254.maskLin_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.maskLin_internal

/-- info: 'Poseidon2.AztecBN254.maskLin_internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.maskLin_internal_inactive_trivial

/-- info: 'Poseidon2.AztecBN254.maskLin_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.maskLin_middle_bound

/-- info: 'Poseidon2.AztecBN254.maskLin_full_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.maskLin_full_prefix

/-- info: 'Poseidon2.AztecBN254.maskLin_full_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.maskLin_full_suffix

/-- info: 'Poseidon2.AztecBN254.external_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.external_isLinBranchBound

/-- info: 'Poseidon2.AztecBN254.linear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.linear_activity_general

/-- info: 'Poseidon2.AztecBN254.linear_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.linear_activity_middle_general

/-- info: 'Poseidon2.AztecBN254.linear_activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.linear_activity_middle

/-- info: 'Poseidon2.AztecBN254.linear_bound_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.linear_bound_middle_general

/-- info: 'Poseidon2.AztecBN254.walsh_permutation_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.walsh_permutation_eq_sum_linCorr


/-! ### Starknet (`Poseidon.lean`) -/

/-- info: 'Poseidon.Starknet.mds_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_selfAdjoint

/-- info: 'Poseidon.Starknet.maskLin_mds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.maskLin_mds

/-- info: 'Poseidon.Starknet.maskLin_mds_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.maskLin_mds_isBranchBound

/-- info: 'Poseidon.Starknet.maskLin_mds_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.maskLin_mds_inactive_trivial

/-- info: 'Poseidon.Starknet.maskLin_middle_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.maskLin_middle_bound

/-- info: 'Poseidon.Starknet.mds_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.mds_isLinBranchBound

/-- info: 'Poseidon.Starknet.linear_activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.linear_activity_general

/-- info: 'Poseidon.Starknet.linear_activity_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.linear_activity_middle_general

/-- info: 'Poseidon.Starknet.linear_activity_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.linear_activity_middle

/-- info: 'Poseidon.Starknet.linear_bound_middle_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.linear_bound_middle_general

/-- info: 'Poseidon.Starknet.walsh_permutation_eq_sum_linCorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon.Starknet.walsh_permutation_eq_sum_linCorr


/-! ### Checks (`Checks/Hades.lean`) -/

/-- info: 'Linear.Checks.trivial_not_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.trivial_not_separating

/-- info: 'Linear.Checks.walsh_masked_needs_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.walsh_masked_needs_separation

/-- info: 'Linear.Checks.bridge_needs_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.bridge_needs_separation

/-- info: 'Linear.Checks.linCorr_zero_trail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.linCorr_zero_trail

/-- info: 'Linear.Checks.linCorr_zero_trail_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.linCorr_zero_trail_ne_zero

/-- info: 'Linear.Checks.scheduledWeight_zero_trail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.scheduledWeight_zero_trail

/-- info: 'Poseidon2.BN254.maskLin_external_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.BN254.maskLin_external_ne

end Linear.HadesAxiomChecks
