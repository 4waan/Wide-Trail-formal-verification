/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Checks.AES

/-!
# Pinned axiom footprints for the AES S-box linearity bound

Each `#guard_msgs` below fixes the exact output of `#print axioms` for one result of
`AESSpectrum.lean`, `GF256Trace.lean`, `AESSbox.lean` or `Checks/AES.lean`. Every footprint is
`[propext, Classical.choice, Quot.sound]` or a subset of it, so none of these results uses
`sorryAx` or `Lean.ofReduceBool`. The four chunks of the spectrum check, evaluated by
`decide +kernel`, use `propext` only.

These guards record which axioms the proofs use; they say nothing about the statements
themselves. The module-based audit `scripts/AuditAxioms.lean` checks every project declaration.
-/

set_option autoImplicit false

namespace Linear.AESAxiomChecks

/-! ### The spectrum on natural numbers (`AESSpectrum.lean`) -/

/-- info: 'Linear.AESSpectrum.chunk₀' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.chunk₀

/-- info: 'Linear.AESSpectrum.chunk₁' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.chunk₁

/-- info: 'Linear.AESSpectrum.chunk₂' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.chunk₂

/-- info: 'Linear.AESSpectrum.chunk₃' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.chunk₃

/-- info: 'Linear.AESSpectrum.specLe_32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.specLe_32

/-- info: 'Linear.AESSpectrum.spectrum_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.spectrum_bound

/-- info: 'Linear.AESSpectrum.mism_ac' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.mism_ac

/-- info: 'Linear.AESSpectrum.specLe_28_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.specLe_28_false

/-- info: 'Linear.AESSpectrum.not_forall_specLe_28' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Linear.AESSpectrum.not_forall_specLe_28

/-! ### The trace of `GF(2⁸)` (`GF256Trace.lean`) -/

/-- info: 'GF256.eq_sum_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GF256.eq_sum_basis

/-- info: 'GF256.addHom_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GF256.addHom_ext

/-- info: 'GF256.fieldTrace_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GF256.fieldTrace_eq

/-- info: 'GF256.trace_eq_fieldTrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GF256.trace_eq_fieldTrace

/-- info: 'GF256.trace_inv_eq_g' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GF256.trace_inv_eq_g

/-- info: 'GF256.bit_phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GF256.bit_phi

/-- info: 'GF256.trace_mul_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GF256.trace_mul_eq_sum

/-- info: 'GF256.natCast_par8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GF256.natCast_par8

/-- info: 'GF256.trace_mul_eq_par8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GF256.trace_mul_eq_par8

/-! ### The S-box bound (`AESSbox.lean`) -/

/-- info: 'GF256.tracePairing_separating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GF256.tracePairing_separating

/-- info: 'AES.affine_isAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.affine_isAdjoint

/-- info: 'AES.affAdj_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.affAdj_eq_zero

/-- info: 'AES.walsh_sbox_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.walsh_sbox_eq

/-- info: 'AES.walsh_inv_one_eq_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.walsh_inv_one_eq_spectrum

/-- info: 'AES.walsh_inv_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.walsh_inv_one_le

/-- info: 'AES.walsh_sbox_eq_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.walsh_sbox_eq_spectrum

/-- info: 'AES.sbox_walsh_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.sbox_walsh_le

/-- info: 'AES.sbox_isLinearityBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.sbox_isLinearityBound

/-- info: 'AES.phi_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.phi_witness

/-- info: 'AES.sbox_walsh_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.sbox_walsh_attained

/-- info: 'AES.sbox_isLinearityBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AES.sbox_isLinearityBound_iff

/-! ### Checks (`Checks/AES.lean`) -/

/-- info: 'Linear.Checks.sbox_walsh_witness_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.sbox_walsh_witness_direct

/-- info: 'Linear.Checks.sbox_not_isLinearityBound_31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.sbox_not_isLinearityBound_31

/-- info: 'Linear.Checks.sbox_walsh_zero_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.sbox_walsh_zero_zero

/-- info: 'Linear.Checks.not_forall_sbox_walsh_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_forall_sbox_walsh_le

/-- info: 'Linear.Checks.walsh_inv_one_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.walsh_inv_one_witness

/-- info: 'Linear.Checks.not_forall_walsh_inv_one_le_28' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_forall_walsh_inv_one_le_28

/-- info: 'Linear.Checks.sbox_mul_two_pow_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.sbox_mul_two_pow_three

/-- info: 'Linear.Checks.not_sbox_mul_two_pow_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.not_sbox_mul_two_pow_four

/-- info: 'Linear.Checks.affine_not_selfAdjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.affine_not_selfAdjoint

/-- info: 'Linear.Checks.trace_eq_trA0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Linear.Checks.trace_eq_trA0

end Linear.AESAxiomChecks
