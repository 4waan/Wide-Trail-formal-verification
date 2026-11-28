/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Rijndael.Checks.MixColumns

/-!
# Pinned axiom footprints for Rijndael `MixColumns` and the Rijndael-192/256 bounds

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one theorem of
`Rijndael/MixColumns.lean` or `Rijndael/Checks/MixColumns.lean`. Every footprint is
`[propext, Classical.choice, Quot.sound]` or a subset of it, so none of these results uses
`sorryAx` or `Lean.ofReduceBool`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves. The module-based audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Rijndael.AxiomChecks

/-! ### `MixColumns`, the specifications and the bounds (`MixColumns.lean`) -/

/-- info: 'Rijndael.localWeight_gridCol_eq_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.localWeight_gridCol_eq_weight

/-- info: 'Rijndael.mixColumnsWith_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumnsWith_column

/-- info: 'Rijndael.mixColumnsWith_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumnsWith_add

/-- info: 'Rijndael.mixColumnsWith_isColBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumnsWith_isColBranchBound

/-- info: 'Rijndael.mixColumnsWith_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumnsWith_nondegenerate

/-- info: 'Rijndael.mixColumns_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumns_apply

/-- info: 'Rijndael.mixColumns_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumns_four

/-- info: 'Rijndael.mixColumns_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumns_add

/-- info: 'Rijndael.mixColumns_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumns_nondegenerate

/-- info: 'Rijndael.mixColumns_isColBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumns_isColBranchBound

/-- info: 'Rijndael.mixColumns_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.mixColumns_isBranchBound

/-- info: 'Rijndael.lin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.lin_isBranchBound

/-- info: 'Rijndael.linSpec_fourRoundBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.linSpec_fourRoundBound

/-- info: 'Rijndael.linSpec_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.linSpec_branch

/-- info: 'Rijndael.linSpec_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.linSpec_lin

/-- info: 'Rijndael.linSpec_lin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.linSpec_lin_isBranchBound

/-- info: 'Rijndael.linSpec_lin_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.linSpec_lin_add

/-- info: 'Rijndael.isTrail_rijndaelSpec_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.isTrail_rijndaelSpec_iff

/-- info: 'Rijndael.four_round_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.four_round_concrete

/-- info: 'Rijndael.rounds_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rounds_concrete

/-- info: 'Rijndael.rijndael256LinSpec_fourRoundBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256LinSpec_fourRoundBound

/-- info: 'Rijndael.rijndael256LinSpec_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256LinSpec_branch

/-- info: 'Rijndael.rijndael256LinSpec_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256LinSpec_lin

/-- info: 'Rijndael.rijndael256LinSpec_lin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256LinSpec_lin_isBranchBound

/-- info: 'Rijndael.rijndael256_four_round_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_four_round_concrete

/-- info: 'Rijndael.rijndael256_rounds_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_rounds_concrete

/-- info: 'Rijndael.rijndael256_fourteen_round_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_fourteen_round_concrete

/-- info: 'Rijndael.rijndael192LinSpec_fourRoundBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael192LinSpec_fourRoundBound

/-- info: 'Rijndael.rijndael192LinSpec_lin_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael192LinSpec_lin_isBranchBound

/-- info: 'Rijndael.rijndael192_four_round_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael192_four_round_concrete

/-- info: 'Rijndael.rijndael192_rounds_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael192_rounds_concrete

/-- info: 'Rijndael.rijndael192_twelve_round_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael192_twelve_round_concrete

/-- info: 'Rijndael.rijndael256_four_round_concrete_trail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_four_round_concrete_trail

/-- info: 'Rijndael.rijndael256_fourteen_round_concrete_trail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael256_fourteen_round_concrete_trail

/-- info: 'Rijndael.rijndael192_twelve_round_concrete_trail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.rijndael192_twelve_round_concrete_trail


/-! ### Controls (`Checks/MixColumns.lean`) -/

/-- info: 'Rijndael.Checks.mixColumns_appendixB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.mixColumns_appendixB

/-- info: 'Rijndael.Checks.mixColumns_transpose_appendixB_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.mixColumns_transpose_appendixB_ne

/-- info: 'Rijndael.Checks.corruptMatrix_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.corruptMatrix_mul_inv

/-- info: 'Rijndael.Checks.corruptInv_mul_corruptMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.corruptInv_mul_corruptMatrix

/-- info: 'Rijndael.Checks.corrupt_appendixB_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.corrupt_appendixB_ne

/-- info: 'Rijndael.Checks.corruptMix_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.corruptMix_nondegenerate

/-- info: 'Rijndael.Checks.e30_ne_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Rijndael.Checks.e30_ne_zero

/-- info: 'Rijndael.Checks.weight_e30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.weight_e30

/-- info: 'Rijndael.Checks.weight_corruptMix_e30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.weight_corruptMix_e30

/-- info: 'Rijndael.Checks.weight_corruptLin_e30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.weight_corruptLin_e30

/-- info: 'Rijndael.Checks.corruptMix_not_isColBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.corruptMix_not_isColBranchBound

/-- info: 'Rijndael.Checks.corruptLin_not_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.corruptLin_not_isBranchBound

/-- info: 'Rijndael.Checks.corruptMatrix_not_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.corruptMatrix_not_isMDS

/-- info: 'Rijndael.Checks.weight_mixColumns_e30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.weight_mixColumns_e30

/-- info: 'Rijndael.Checks.weight_rijndael256Lin_e30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.weight_rijndael256Lin_e30

/-- info: 'Rijndael.Checks.mixColumns_not_isColBranchBound_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.mixColumns_not_isColBranchBound_six

/-- info: 'Rijndael.Checks.rijndael256_lin_not_isBranchBound_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.rijndael256_lin_not_isBranchBound_six

/-- info: 'Rijndael.Checks.rijndael256Lin_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.rijndael256Lin_zero

/-- info: 'Rijndael.Checks.zero_isTrail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.zero_isTrail

/-- info: 'Rijndael.Checks.patternWeight_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.patternWeight_zero

/-- info: 'Rijndael.Checks.fourteen_round_needs_h0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rijndael.Checks.fourteen_round_needs_h0

end Rijndael.AxiomChecks
