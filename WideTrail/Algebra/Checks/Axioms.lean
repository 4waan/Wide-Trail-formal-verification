/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.MDS
import WideTrail.Algebra.AESMix
import WideTrail.Algebra.MDS4
import WideTrail.Algebra.BlockCirculant
import WideTrail.Algebra.DiagPlusOnes
import WideTrail.Algebra.Transpose

/-!
# Pinned axiom footprints for the algebra layer

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of
`WideTrail.Algebra`: the MDS branch-number theorem and its corollary, the AES `MixColumns`
matrix, the `MDSMat4` criterion `m4_isMDS_iff` and its branch bound, the block-circulant branch
bounds and linear equivalence, the block-circulant layer on states whose blocks sum to zero, the
inverse of `diag d + J`, and the transposes of these layers (`WideTrail.Algebra.Transpose`). Every
footprint is `[propext, Classical.choice, Quot.sound]` or a subset of it
(`Poseidon2.diagPlusOnes_isSymm` uses `propext` and `Quot.sound` only), so none of these results
uses `sorryAx` or `Lean.ofReduceBool`. `Poseidon2.diagPlusOnesEquiv` and
`Poseidon2.diagPlusOnes_injective_iff` are pinned in `WideTrail.Hades.Checks.Krylov`, and
`BlockCirculant.blockMix_apply_eq_add_sum` and `Poseidon2.m4_natCast_ne_zero_of_le_five` in
`WideTrail.Poseidon2.Checks.Plonky3`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves. The module-based audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace AlgebraChecks.Axioms

/-! ### MDS matrices -/

/-- info: 'isMDS_branch_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isMDS_branch_bound

/-- info: 'isMDS_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isMDS_injective

/-- info: 'aesMatrix_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aesMatrix_isMDS

/-- info: 'aesMixColumns_isColBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aesMixColumns_isColBranchBound

/-! ### `MDSMat4` -/

/-- info: 'Poseidon2.m4_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4_isMDS

/-- info: 'Poseidon2.m4_isMDS_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4_isMDS_iff

/-- info: 'Poseidon2.m4_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4_isBranchBound

/-- info: 'Poseidon2.m4Equiv_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4Equiv_isBranchBound

/-! ### Block-circulant layers -/

/-- info: 'BlockCirculant.blockMixEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockMixEquiv

/-- info: 'BlockCirculant.isBranchBound_blockMix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.isBranchBound_blockMix

/-- info: 'BlockCirculant.isBranchBound_blockMix_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.isBranchBound_blockMix_sixteen

/-! ### `diag d + J` and its inverse -/

/-- info: 'Poseidon2.diagPlusOnesInv_diagPlusOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnesInv_diagPlusOnes

/-- info: 'Poseidon2.diagPlusOnes_diagPlusOnesInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnes_diagPlusOnesInv

/-- info: 'Poseidon2.diagPlusOnesEquiv_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnesEquiv_symm_apply

/-! ### Block-circulant layers on states whose blocks sum to zero -/

/-- info: 'BlockCirculant.blockMix_of_blockSum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockMix_of_blockSum_eq_zero

/-- info: 'BlockCirculant.blockSum_blockMix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockSum_blockMix

/-- info: 'BlockCirculant.blockMix_mem_blockSumZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockMix_mem_blockSumZero

/-- info: 'BlockCirculant.blockMix_mem_blockSumZero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockMix_mem_blockSumZero_iff

/-- info: 'BlockCirculant.finrank_blockSumZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.finrank_blockSumZero

/-! ### Transposes -/

/-- info: 'IsMDS.transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsMDS.transpose

/-- info: 'isMDS_transpose_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isMDS_transpose_iff

/-- info: 'Poseidon2.m4_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4_transpose

/-- info: 'Poseidon2.m4_transpose_isMDS_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4_transpose_isMDS_iff

/-- info: 'Poseidon2.m4_transpose_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4_transpose_isBranchBound

/-- info: 'BlockCirculant.blockMix_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockMix_dotProduct

/-- info: 'BlockCirculant.blockMix_mulVecLin_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockMix_mulVecLin_dotProduct

/-- info: 'Poseidon2.blockMix_m4_sixteen_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.blockMix_m4_sixteen_dotProduct

/--
info: 'Poseidon2.isBranchBound_blockMix_m4_transpose_sixteen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.isBranchBound_blockMix_m4_transpose_sixteen

/-- info: 'Poseidon2.diagPlusOnes_isSymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.diagPlusOnes_isSymm

/-- info: 'Poseidon2.toLin'_transpose_diagPlusOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.toLin'_transpose_diagPlusOnes

end AlgebraChecks.Axioms
