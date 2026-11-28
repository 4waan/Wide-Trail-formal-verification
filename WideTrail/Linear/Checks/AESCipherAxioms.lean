/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Checks.AESCipher

/-!
# Pinned axiom footprints for the AES trail and hull bounds

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of `AES.lean`
or `Checks/AESCipher.lean`. Every footprint is `[propext, Classical.choice, Quot.sound]` or a
subset of it, so none of these results uses `sorryAx` or `Lean.ofReduceBool`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves. The module-based audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Linear.AESCipherAxiomChecks

/-! ### Masks, branch numbers, trails and the hull (`AES.lean`) -/

/-- info: 'AES.transpose_mul_invT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.transpose_mul_invT

/-- info: 'AES.invT_mul_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.invT_mul_transpose

/-- info: 'AES.aesInvMatrixT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesInvMatrixT_eq

/-- info: 'AES.mixColumnsT_mixColumnsInvT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mixColumnsT_mixColumnsInvT

/-- info: 'AES.mixColumnsInvT_mixColumnsT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mixColumnsInvT_mixColumnsT

/-- info: 'AES.mixColumnsT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mixColumnsT_zero

/-- info: 'AES.aesMixColumns_isAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesMixColumns_isAdjoint

/-- info: 'AES.aesMatrix_transpose_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesMatrix_transpose_isMDS

/-- info: 'AES.mixColumnsT_isColBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mixColumnsT_isColBranchBound

/-- info: 'AES.mixColumnsInvT_isColBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mixColumnsInvT_isColBranchBound

/-- info: 'AES.mixColumnsInvT_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mixColumnsInvT_nondegenerate

/-- info: 'AES.mixColumnsT_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mixColumnsT_isBranchBound

/-- info: 'AES.aesMixColumns_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesMixColumns_isLinBranchBound

/-- info: 'AES.aesMaskSpec_fourRoundBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesMaskSpec_fourRoundBound

/-- info: 'AES.aesMaskSpec_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesMaskSpec_branch

/-- info: 'AES.aesMaskSpec_disp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesMaskSpec_disp

/-- info: 'AES.aesLinSpec_disp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesLinSpec_disp

/-- info: 'AES.aesMaskSpec_lin_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesMaskSpec_lin_apply

/-- info: 'AES.aesLinSpec_lin_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesLinSpec_lin_apply

/-- info: 'AES.aesLin_isAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesLin_isAdjoint

/-- info: 'AES.aesLinT_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesLinT_unique

/-- info: 'AES.aesLinT_maskSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesLinT_maskSpec

/-- info: 'AES.maskSpec_aesLinT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.maskSpec_aesLinT

/-- info: 'AES.dot_maskSpec_aesLin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.dot_maskSpec_aesLin

/-- info: 'AES.aesLinT_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesLinT_isBranchBound

/-- info: 'AES.aesLin_isLinBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.aesLin_isLinBranchBound

/-- info: 'AES.maskTrail_iff_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.maskTrail_iff_backward

/-- info: 'AES.sbox_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.sbox_bijective

/-- info: 'AES.sbox_clears' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.sbox_clears

/-- info: 'AES.walsh_run_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.walsh_run_expansion

/-- info: 'AES.isTrail_of_corr_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.isTrail_of_corr_ne_zero

/-- info: 'AES.rounds_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.rounds_correlation

/-- info: 'AES.four_round_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.four_round_correlation

/-- info: 'AES.ten_round_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.ten_round_correlation

/-- info: 'AES.twelve_round_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.twelve_round_correlation

/-- info: 'AES.fourteen_round_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.fourteen_round_correlation

/-- info: 'AES.four_round_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.four_round_contribution

/-- info: 'AES.mul_two_pow_24_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.mul_two_pow_24_le

/-- info: 'AES.two_round_elp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.two_round_elp

/-- info: 'AES.rounds_elp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.rounds_elp

/-! ### Checks (`Checks/AESCipher.lean`) -/

/-- info: 'Linear.Checks.sbox_clears_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.sbox_clears_iff

/-- info: 'Linear.Checks.not_exists_sbox_clears_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_exists_sbox_clears_four

/-- info: 'Linear.Checks.binMatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.binMatrix_transpose

/-- info: 'Linear.Checks.binMatrix_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.binMatrix_mul_self

/-- info: 'Linear.Checks.binMatrix_inv_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.binMatrix_inv_transpose

/-- info: 'Linear.Checks.binMixColumns_isAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.binMixColumns_isAdjoint

/-- info: 'Linear.Checks.e00_ne_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.Checks.e00_ne_zero

/-- info: 'Linear.Checks.weight_e00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.weight_e00

/-- info: 'Linear.Checks.weight_binMixColumns_e00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.weight_binMixColumns_e00

/-- info: 'Linear.Checks.binMixColumns_not_isColBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.binMixColumns_not_isColBranchBound

/-- info: 'Linear.Checks.binMixColumns_not_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.binMixColumns_not_isBranchBound

/-- info: 'Linear.Checks.binMatrix_not_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.binMatrix_not_isMDS

/-- info: 'Linear.Checks.weight_aesLinT_e00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.weight_aesLinT_e00

/-- info: 'Linear.Checks.weight_mixColumnsT_e00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.weight_mixColumnsT_e00

/-- info: 'Linear.Checks.aesLinT_not_isBranchBound_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.aesLinT_not_isBranchBound_six

/-- info: 'Linear.Checks.aesLin_not_isLinBranchBound_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.aesLin_not_isLinBranchBound_six

/-- info: 'Linear.Checks.aesMixColumns_not_isLinBranchBound_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.aesMixColumns_not_isLinBranchBound_six

/-- info: 'Linear.Checks.maskSpec_lin_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.maskSpec_lin_ne

/-- info: 'Linear.Checks.natAbs_trailCorr_zero_masks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.natAbs_trailCorr_zero_masks

/-- info: 'Linear.Checks.elpCount_zero_masks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.elpCount_zero_masks

/-- info: 'Linear.Checks.not_mul_two_pow_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_mul_two_pow_le

/-- info: 'Linear.Checks.not_natAbs_trailCorr_zero_masks_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_natAbs_trailCorr_zero_masks_le

/-- info: 'Linear.Checks.not_elpCount_zero_masks_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_elpCount_zero_masks_le

/-- info: 'Linear.Checks.not_forall_natAbs_trailCorr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_forall_natAbs_trailCorr_le

/-- info: 'Linear.Checks.not_forall_elpCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_forall_elpCount_le

/-- info: 'Linear.Checks.four_round_correlation_needs_h0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.four_round_correlation_needs_h0

/-- info: 'Linear.Checks.two_round_elp_needs_hu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.two_round_elp_needs_hu

end Linear.AESCipherAxiomChecks
