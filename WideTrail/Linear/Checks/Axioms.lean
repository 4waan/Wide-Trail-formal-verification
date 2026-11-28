/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Checks.Character
import WideTrail.Linear.Checks.Conventions

/-!
# Pinned axiom footprints for the linear layer

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of
`WideTrail.Linear`: the separation lemmas and identities of `Character.lean`, the binary case of
`Binary.lean`, the adjoint calculus and branch-number statements of `Masks.lean`, and the kernel
checks of `Checks/Character.lean` and `Checks/Conventions.lean`. Every footprint is
`[propext, Classical.choice, Quot.sound]` or a subset of it, so none of these results uses
`sorryAx` or `Lean.ofReduceBool`.

These guards record which axioms the proofs use; they say nothing about the statements
themselves. The module-based audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Linear.AxiomChecks

/-! ### Pairings and separation -/

/-- info: 'Linear.Pairing.Separating.pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Pairing.Separating.pi

/-- info: 'Linear.Pairing.Separating.comap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Pairing.Separating.comap

/-- info: 'Linear.Pairing.traceForm_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Pairing.traceForm_separating

/-! ### Identities with no hypothesis -/

/-- info: 'Linear.walsh_addKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_addKey

/-- info: 'Linear.walsh_postAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_postAdd

/-- info: 'Linear.walsh_comp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_comp_adjoint

/-- info: 'Linear.walsh_bricklayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_bricklayer

/-- info: 'Linear.walsh_inv_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_inv_mul

/-- info: 'Linear.walsh_maskRelabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_maskRelabel

/-- info: 'Linear.walsh_comap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_comap

/-! ### Identities that need separation -/

/-- info: 'Linear.sum_char_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_char_dot

/-- info: 'Linear.sum_char_dot_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_char_dot_left

/-- info: 'Linear.walsh_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_comp

/-- info: 'Linear.walsh_of_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_of_adjoint

/-- info: 'Linear.walsh_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_zero_right

/-- info: 'Linear.walsh_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_zero_left

/-- info: 'Linear.activePattern_eq_of_walsh_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.activePattern_eq_of_walsh_ne_zero

/-- info: 'Linear.sum_walsh_mul_walsh_neg_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_walsh_mul_walsh_neg_left

/-- info: 'Linear.sum_walsh_mul_walsh_neg_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_walsh_mul_walsh_neg_right

/-! ### The binary case -/

/-- info: 'Linear.bitPairing_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.bitPairing_separating

/-- info: 'Linear.walsh_sign₂_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.walsh_sign₂_apply

/-- info: 'Linear.sum_walsh_sq_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_walsh_sq_left

/-- info: 'Linear.sum_walsh_sq_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.sum_walsh_sq_right

/-- info: 'Linear.natAbs_walsh_bricklayer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.natAbs_walsh_bricklayer_le

/-! ### Masks -/

/-- info: 'Linear.IsAdjoint.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.IsAdjoint.comp

/-- info: 'Linear.IsAdjoint.symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.IsAdjoint.symm

/-- info: 'Linear.IsAdjoint.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.IsAdjoint.unique

/-- info: 'Linear.IsAdjoint.comap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.IsAdjoint.comap

/-- info: 'Linear.IsAdjoint.maskRelabel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.IsAdjoint.maskRelabel

/-- info: 'Linear.isAdjoint_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.isAdjoint_transpose

/-- info: 'Linear.isAdjoint_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.isAdjoint_mulVec

/-- info: 'Linear.isAdjoint_colMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.isAdjoint_colMatrix

/-- info: 'Linear.isBranchBound_symm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.isBranchBound_symm_iff

/-- info: 'Linear.isLinBranchBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.isLinBranchBound_iff

/-- info: 'Linear.isTrail_iff_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.isTrail_iff_backward

/-! ### Kernel checks -/

/-- info: 'Linear.Checks.toy_addKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_addKey

/-- info: 'Linear.Checks.toy_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_comp

/-- info: 'Linear.Checks.toy_parseval_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_parseval_left

/-- info: 'Linear.Checks.toy_parseval_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_parseval_right

/-- info: 'Linear.Checks.toy_and_parseval_right_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_and_parseval_right_fails

/-- info: 'Linear.Checks.toy_comp_fails_zeroPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.toy_comp_fails_zeroPairing

/-- info: 'Linear.Checks.byte_adjoint_two_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.byte_adjoint_two_apply_one

/-- info: 'Linear.Checks.not_isAdjoint_byte_aesMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_isAdjoint_byte_aesMatrix

/-- info: 'Linear.Checks.trace_adjoint_aesMixColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.trace_adjoint_aesMixColumns

/-- info: 'Linear.Checks.trA0_adjoint_two_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.trA0_adjoint_two_apply_one

end Linear.AxiomChecks
