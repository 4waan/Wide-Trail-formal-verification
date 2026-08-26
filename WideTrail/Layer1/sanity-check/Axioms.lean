/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.«sanity-check».Verification

/-!
# Axiom audit

Every result in this development is checked by the Lean kernel, but "checked by the
kernel" is only as strong as the axiom set the kernel was asked to trust. Two ways a
formalisation can quietly stop meaning anything:

* a `sorry` anywhere in the dependency graph, which shows up as `sorryAx`;
* a `native_decide`, which shows up as `Lean.ofReduceBool` and moves the evidence out of
  the kernel and into the compiler plus the machine that ran it.

Every finite check in this project uses kernel `decide`, never `native_decide`, so the
toy ciphers are evaluated by the same trusted core that checks the abstract proofs.

The `#guard_msgs` below turn that into a regression test rather than a claim. If a later
edit introduces a `sorry` or swaps a `decide` for a `native_decide`, the reported axiom
list changes and this file stops compiling.
-/

/-! ### Theorem 1 -/

/-- info: 'two_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_round

/-! ### Lemma 1 -/

/-- info: 'lemma_one_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_one_in

/-- info: 'lemma_one_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_one_out

/-! ### Lemma 2 -/

/-- info: 'lemma_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_two

/-! ### Theorems 2 and 3 -/

/-- info: 'four_round_thetaTheta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms four_round_thetaTheta

/-- info: 'four_round_identical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms four_round_identical

/-! ### Multi-round and AES bounds -/

/--
info: 'WideTrailSpec.trailWeight_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WideTrailSpec.trailWeight_bound

/-- info: 'aes_four_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes_four_round

/-- info: 'aes128_ten_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes128_ten_round

/-! ### The finite checks

These are the results proved by `decide`. Their axiom lists are the interesting ones,
because this is exactly where a `native_decide` would show up. -/

/-- info: 'shiftRows_diffusionOptimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftRows_diffusionOptimal

/-- info: 'toyMix_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toyMix_branch

/-- info: 'toyMix_branch_not_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toyMix_branch_not_three

/--
info: 'four_round_fails_without_dispersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms four_round_fails_without_dispersion

/-- info: 'noPi_trail_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noPi_trail_weight

/-- info: 'thetaTheta_bound_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thetaTheta_bound_matches
