/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Differential.AESProb
import WideTrail.Differential.Checks.Toy

/-!
# Axiom audit for Differential layer

The same regression test `Propagation/Checks/Axioms.lean` runs, applied to the
probability layer. Every result below reports `[propext, Classical.choice, Quot.sound]`
and nothing else: no `sorryAx`, and no `Lean.ofReduceBool`, which is what a `native_decide`
would leave behind.

That matters more here than it did in Propagation layer, because Differential layer's content is
arithmetic on
counts and the temptation to reach for `native_decide` on a toy cipher is real. The kernel
enumerates all `256` round-key vectors of `Toy.lean` itself.

`Classical.choice` enters through Mathlib's `Finset` API throughout, and additionally
through `linAddEquiv`, which inverts a finite injective additive map by
`Equiv.ofBijective`. That is a construction of an inverse, not an assumption about the
cipher.
-/

/-! ### Differential counts -/

/-- info: 'diffCount_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_zero_left

/-- info: 'sum_diffCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_diffCount

/-- info: 'diffCount_addKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_addKey

/-- info: 'diffCount_addEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_addEquiv

/-! ### The hull identity -/

/-- info: 'diffCount_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_comp

/-! ### The S-box layer -/

/-- info: 'diffCount_bricklayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_bricklayer

/-- info: 'activePattern_eq_of_diffCount_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms activePattern_eq_of_diffCount_ne_zero

/-- info: 'diffCount_bricklayer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_bricklayer_le

/-! ### The Markov product -/

/-- info: 'diffCount_keyedRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms diffCount_keyedRound

/-- info: 'trailKeyCount_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trailKeyCount_eq_prod

/-- info: 'trailKeyCount_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trailKeyCount_const

/-! ### The trail bound -/

/-- info: 'trailKeyCount_bricklayer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trailKeyCount_bricklayer_le

/-- info: 'isTrail_of_trailKeyCount_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isTrail_of_trailKeyCount_ne_zero

/-- info: 'trailKeyCount_le_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trailKeyCount_le_of_spec

/-! ### AES -/

/-- info: 'card_aesState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_aesState

/-- info: 'aes_four_round_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes_four_round_prob

/-- info: 'aes128_ten_round_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes128_ten_round_prob

/-- info: 'aes192_twelve_round_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes192_twelve_round_prob

/-- info: 'aes256_fourteen_round_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes256_fourteen_round_prob

/-! ### The toy cipher -/

/-- info: 'toy_diffUniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toy_diffUniform

/-- info: 'toy_not_diffUniform_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toy_not_diffUniform_one

/-- info: 'toy_bricklayer_factors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toy_bricklayer_factors

/-- info: 'toy_markov_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toy_markov_matches

/-- info: 'toy_fixed_key_fails_markov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toy_fixed_key_fails_markov

/-- info: 'toy_bound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toy_bound_holds

/-- info: 'toy_hull_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toy_hull_gap
