/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.«sanity-check».Verification
import WideTrail.Layer1.Rijndael

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

/--
info: 'WideTrailSpec.trailWeight_bound_add_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WideTrailSpec.trailWeight_bound_add_two

/--
info: 'WideTrailSpec.trailWeight_bound_rounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WideTrailSpec.trailWeight_bound_rounds

/-- info: 'aes256_fourteen_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes256_fourteen_round


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

/-! ### The rectangular generalisation

`Grid.lean` widens the state from `Fin m × Fin m` to `Fin rows × Fin cols`. Nothing above
it changed, so a `sorry` slipped into the widening would be invisible from the AES side.
The two loads it carries are the reduction of Definition 5 to injectivity of the offset
vector, and the shape constraint `rows ≤ cols` inherited from `card_fiber_le_card_col`. -/

/-- info: 'card_fiber_le_card_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_fiber_le_card_col

/-- info: 'diffusionOptimal_shiftRowsPerm_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms diffusionOptimal_shiftRowsPerm_iff

/--
info: 'rows_le_cols_of_diffusionOptimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rows_le_cols_of_diffusionOptimal

/--
info: 'card_diffusionOptimal_offsets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms card_diffusionOptimal_offsets

/-! ### The Rijndael offsets

These are the decisions the formalisation makes about a real design choice, so they are the
ones where a `native_decide` would be most tempting and least acceptable. All of them are
kernel `decide`. In particular `shiftOff256naive_diffusionOptimal` is a *negative* result
about the wide-trail strategy, and a negative result resting on an unchecked compiler
would be worth nothing. -/

/--
info: 'shiftOff256_diffusionOptimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shiftOff256_diffusionOptimal

/--
info: 'shiftOff256naive_diffusionOptimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shiftOff256naive_diffusionOptimal

/--
info: 'shiftOff256_not_diffusionOptimal_on_128' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shiftOff256_not_diffusionOptimal_on_128

/--
info: 'card_diffusionOptimal_offsets_256' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms card_diffusionOptimal_offsets_256

/--
info: 'card_diffusionOptimal_offsets_128_enumerated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms card_diffusionOptimal_offsets_128_enumerated

/--
info: 'no_diffusionOptimal_four_by_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms no_diffusionOptimal_four_by_three

/--
info: 'shiftOff256_sq_not_diffusionOptimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shiftOff256_sq_not_diffusionOptimal

/--
info: 'shiftOff256naive_sq_diffusionOptimal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shiftOff256naive_sq_diffusionOptimal

/-- info: 'rijndael256_fourteen_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rijndael256_fourteen_round

