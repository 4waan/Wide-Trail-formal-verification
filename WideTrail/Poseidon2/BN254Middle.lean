import WideTrail.Poseidon2.BN254
import WideTrail.Hades.Subspace

/-! Partial-round activity for the pinned BN254 width-three permutation.

`BN254.lean` counts sixteen active S-boxes, all in the eight external rounds, and
charges nothing to the fifty-six internal rounds. This file counts those too.

The internal matrix leaves no nonzero difference inactive for three consecutive
rounds, so every window of three internal rounds applies the S-box to a nonzero
difference at least once. Fifty-six rounds hold eighteen disjoint windows.

The same count is carried into the independently keyed trail bound. As in
`BN254.lean`, that bound concerns one trail and an additional independent uniform
key per round. It says nothing about the fixed public constants alone, nor about
a differential. -/

set_option autoImplicit false

namespace Poseidon2.BN254

/-- No nonzero difference stays off the S-box coordinate through three internal
rounds. The three conditions read `a 0 = 0`, `2 a 0 + a 1 + a 2 = 0` and
`6 a 0 + 5 a 1 + 6 a 2 = 0`, and the proof combines them using ring identities
only. -/
theorem internal_inactive_trivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 3)) 3 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  have h0 := ha 0 (by norm_num) 0 (by simp)
  have h1 := ha 1 (by norm_num) 0 (by simp)
  have h2 := ha 2 (by norm_num) 0 (by simp)
  simp only [pow_zero, pow_one, Module.End.one_apply, LinearEquiv.coe_coe] at h0 h1
  rw [Module.End.pow_apply] at h2
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    LinearEquiv.coe_coe, id_eq] at h2
  simp [internal] at h1 h2
  funext i
  fin_cases i
  · change a 0 = 0
    exact h0
  · change a 1 = 0
    linear_combination (-6 : F) * h0 + (6 : F) * h1 - h2
  · change a 2 = 0
    linear_combination (4 : F) * h0 - (5 : F) * h1 + h2

/-- Two rounds are not enough: some nonzero difference survives them. The window
length three in `internal_inactive_trivial` therefore cannot be shortened. -/
theorem internal_inactive_two_nontrivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 3)) 2 ≠ ⊥ :=
  Hades.inactiveSpace_ne_bot _ _ 2 (by simp)

theorem middle_linear (j : Nat) (hj : j < 56) : (rounds (4 + j)).lin = internal := by
  simp [rounds, Hades.hadesSchedule, linear, show ¬(4 + j < 4) by omega,
    show ¬(60 ≤ 4 + j) by omega]

theorem middle_mask (j : Nat) (hj : j < 56) : (rounds (4 + j)).mask = {0} := by
  simp [rounds, Hades.hadesSchedule, Hades.hadesMask_middle 4 56 4 _ hj]

/-- **Thirty-four active S-boxes.** Every distinct input pair incurs sixteen in the
external rounds and at least eighteen in the internal rounds.

The internal contribution is one per disjoint window of three rounds. It is a lower
bound and is not claimed to be attained. -/
theorem activity_with_partial {x y : State} (hxy : x ≠ y) :
    34 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 64 := by
  have h := Hades.outer_middle_bound rounds (fun h => hxy (external.injective h))
    4 56 4 4 3
    (fun j hj => by simp [rounds, Hades.hadesSchedule, Hades.hadesMask_prefix 4 56 4 _ hj])
    (fun j hj => by simp [rounds, Hades.hadesSchedule, Hades.hadesMask_suffix 4 56 4 _ hj])
    (fun j hj => by simpa [rounds, Hades.hadesSchedule] using full_prefix j hj)
    (fun j hj => by simpa [rounds, Hades.hadesSchedule] using full_suffix j hj)
    internal {0} middle_linear middle_mask internal_inactive_trivial
  exact h

theorem linear_middle (j : Nat) (hj : j < 56) : linear (4 + j) = internal := by
  simp [linear, show ¬(4 + j < 4) by omega, show ¬(60 ≤ 4 + j) by omega]

/-- Exact trail bound for the additional-independent-key model only, with the
internal rounds charged. The exponent keeps its round-count arithmetic, as in
`independent_key_probability`; `probability_exponent_with_partial` evaluates it. -/
theorem independent_key_probability_with_partial {T : Nat → State} (h0 : T 0 ≠ 0)
    (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values)
        (4 + 56 + 4) T x * 2 ^ (251 * ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 56 / 3))
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) := by
  have hd : 4 * 2 ^ 251 ≤ Fintype.card F := by rw [ZMod.card]; decide
  exact
    Hades.hades_probability_with_middle (Idx := Fin 3) (K := F) (u := 4) (d := 251)
      4 56 4 4 3 {0} (fun _ _ => sbox) linear values
      (fun _ _ _ => sbox_uniform) hd full_prefix full_suffix
      internal linear_middle internal_inactive_trivial h0 x

/-- The displayed bound's concrete exponent. -/
theorem probability_exponent_with_partial :
    251 * ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 56 / 3) = 8534 := by
  decide

end Poseidon2.BN254
