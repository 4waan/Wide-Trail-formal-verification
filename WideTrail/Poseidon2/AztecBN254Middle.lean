/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.AztecBN254
import WideTrail.Hades.Automaton
import WideTrail.Poseidon2.Certificates.AztecBN254Automaton

/-!
# Aztec and Noir BN254, width four: forty-four charged S-boxes

`WideTrail.Poseidon2.AztecBN254` charges the `56` partial rounds of the pinned Aztec and Noir
width-four permutation through windows: no nonzero difference stays inactive through `4`
consecutive partial rounds, so the partial rounds charge at least `56 / 4 = 14` S-boxes, and two
distinct inputs incur at least `34` charged S-box applications. This file proves that every trail
through `14` consecutive partial rounds charges at least `6` S-boxes, so the `56` partial rounds,
four disjoint windows of `14`, charge at least `24`, and the count is at least `20 + 24 = 44`. As
a lower bound, `44` supersedes `34`; the theorems of `WideTrail.Poseidon2.AztecBN254` are
unchanged.

The window bound is a forward-space automaton certificate (`WideTrail.Hades.Automaton`) with
`255` states, each a set of differences given by the linear functionals that vanish on it. Every
trail can be followed through the states, the difference entering each round lying in the set of
the current state, and the potential of the current state drops by one at every inactive round
and grows by at most one at every active round. The start potential is `3`, so `14` rounds with
`s` active rounds satisfy `14 - s ≤ 3 + s`, that is `s ≥ (14 + 1 - 3) / 2 = 6`. The certificate
data and its kernel check are in `WideTrail.Poseidon2.Certificates.AztecBN254Automaton`; the
internal layer it uses is `diag(d) + J` with the stored array `d` (`internalDiag`), whose diagonal
entries are `d_i + 1`, as in `internal_eq_mulVec`.

## Results, for the pinned round constants and for every round-constant table

* `middle_bound_window`: every trail (`Hades.IsTrail`) through `14` consecutive rounds with the
  internal layer and mask `{0}`, from a nonzero difference, charges at least `6` S-boxes.
  `Checks/AztecBN254Middle.lean` exhibits such a trail with exactly `6` active rounds, so `6` is
  the largest middle bound for `14` rounds.
* `middle_bound`: every such trail through `56` consecutive rounds charges at least `24`
  S-boxes, by four windows of `14` (`Hades.MiddleBound.add`). `middle_bound_diag`,
  `middle_bound_window_diag`: the same for `diagPlusOnes 1 internalDiag`, which is that layer.
  `Checks/AztecBN254Middle.lean` exhibits a trail through the `56` rounds with exactly `27` active
  rounds, so no middle bound above `27` holds for them.
* `isTrail_activity_middle_general`, `activity_middle_general`, `activity_middle`: every trail in
  the `IsTrail` model through the `64` rounds from a nonzero difference, and so every pair of
  distinct inputs, incurs at least `44` charged S-box applications: at least `20` in the external
  rounds and at least `24` in the internal rounds. `Checks/AztecBN254Middle.lean` exhibits a
  trail in the `IsTrail` model through the `64` rounds that charges exactly `47`, so no argument
  that uses only `IsTrail` gives more than `47`.
* `independent_key_probability_middle`, `independent_key_probability_middle_general`: for every
  nonzero trail `T`, `keyCount * 2^11044 ≤ |F^4|^(4 + 56 + 4)`, charging `251` bits per charged
  S-box (`251` is the largest `d` with `4 * 2^d ≤ p`), and `11044 = 251 * 44`.
* `independent_key_probability_middle_exact`, `independent_key_probability_middle_sharp` and their
  `_general` forms: `keyCount * p^44 ≤ 4^44 * |F^4|^(4 + 56 + 4)` and
  `keyCount * 2^11070 ≤ |F^4|^(4 + 56 + 4)`. `11070` is the largest exponent this arithmetic
  gives for `44` charged S-boxes (`middle_sharp_exponent_bound`; `Checks/AztecBN254Middle.lean`
  shows that `11071` fails).

A computation outside Lean, not checked in Lean, gives exactly `27` for the `56` partial rounds:
it enumerates the forward spaces of the first `28` rounds and the backward spaces of the last
`28`, finds by a meet-in-the-middle test of their `603,881,476` pairs that no trail through the
`56` rounds has `26` or fewer active rounds, and the trail of `Checks/AztecBN254Middle.lean` has
`27`. With the outer rounds this would give `47` in all. Nothing in Lean claims it: the lower
bounds proved here are `24` and `44`.

## What is not claimed

The counts are lower bounds on charged S-boxes for every trail in the `IsTrail` model, and hence
for every pair of distinct inputs; they are not claimed to be attained, and `24` is not claimed to
be the least number of S-boxes charged in the `56` partial rounds. The trails of the checks are
trails in that model; they are not claimed to be realised by an input pair or a key. The
probability statements concern one trail in the model with an additional independent uniform key
per round: not the permutation with its fixed constants, not a differential, and not any one key.
-/

set_option autoImplicit false

open Poseidon2.BN254 (modulus F field_card sbox sbox_uniform)
open Poseidon2.Certificates.AztecBN254 (fieldModulus internalRows states automaton_check
  start_pot)

namespace Poseidon2.AztecBN254

/-! ### The middle bound -/

/-- The certificate's prime is the instance's modulus. -/
theorem fieldModulus_eq : fieldModulus = modulus :=
  rfl

/-- The matrix `diag(d) + J` of `internal_eq_mulVec`, with the stored array `d = internalDiag`,
is the matrix of the certificate's table `internalRows`, entry by entry, by `decide`. -/
theorem internalMatrix_eq_mat :
    (Matrix.diagonal internalDiag + Matrix.of fun _ _ => (1 : F)) =
      Hades.AutomatonCheck.mat modulus 4 internalRows := by
  ext i k
  fin_cases i <;> fin_cases k <;> decide

/-- The internal layer acts as the matrix of `internalRows`. -/
theorem internal_eq_mat_mulVec (v : State) :
    internal.toLinearMap v = (Hades.AutomatonCheck.mat modulus 4 internalRows).mulVec v := by
  rw [← internalMatrix_eq_mat]
  exact internal_eq_mulVec v

/-- **Six charged S-boxes in every window of fourteen partial rounds.** Every trail through `14`
consecutive rounds with the internal layer `diag(d) + J` and mask `{0}`, from a nonzero
difference, charges at least `6` S-boxes. The proof is the automaton certificate
`Certificates.AztecBN254.automaton_check`, whose start state has potential `3`. A lower bound in
the `IsTrail` model. -/
theorem middle_bound_window :
    Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 4)) 14 6 := by
  have h := Hades.MiddleBound.of_automatonCheck (p := modulus) internal.toLinearMap 0 14
    internalRows 0 states internal_eq_mat_mulVec automaton_check
  rwa [start_pot] at h

/-- **Twenty-four charged S-boxes in the partial rounds.** Every trail through `56` consecutive
rounds with the internal layer and mask `{0}`, from a nonzero difference, charges at least `24`
S-boxes: the `56` rounds are four disjoint windows of `14`, each charging at least `6`
(`middle_bound_window`, `Hades.MiddleBound.add`). A lower bound in the `IsTrail` model. -/
theorem middle_bound :
    Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 4)) 56 24 :=
  (middle_bound_window.add middle_bound_window).add (middle_bound_window.add middle_bound_window)

/-- **The window bound for `diagPlusOnes 1 internalDiag`**, which is the internal layer
(`internal_toLinearMap`). -/
theorem middle_bound_window_diag :
    Hades.MiddleBound (diagPlusOnes (1 : F) internalDiag) ({0} : Finset (Fin 4)) 14 6 := by
  rw [← internal_toLinearMap]
  exact middle_bound_window

/-- **The middle bound for `diagPlusOnes 1 internalDiag`**, which is the internal layer
(`internal_toLinearMap`). -/
theorem middle_bound_diag :
    Hades.MiddleBound (diagPlusOnes (1 : F) internalDiag) ({0} : Finset (Fin 4)) 56 24 := by
  rw [← internal_toLinearMap]
  exact middle_bound

/-! ### Activity -/

/-- The linear maps of the internal rounds, as linear maps. -/
theorem linear_middle_toLinearMap (j : ℕ) (hj : j < 56) :
    (linear (4 + j) : Module.End F State) = internal.toLinearMap := by
  rw [linear_middle hj]

/-- **Forty-four charged S-boxes for every trail, for every round-constant table.** Every trail
in the `IsTrail` model through the `64` rounds, from a nonzero difference, charges at least `44`
S-boxes: at least `20` in the external rounds and at least `24` in the internal rounds
(`middle_bound`). -/
theorem isTrail_activity_middle_general (table : ℕ → State) {T : ℕ → State}
    (hT : Hades.IsTrail (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) T 64)
    (h0 : T 0 ≠ 0) :
    44 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      T 0 64 :=
  hT.outer_middle_bound_of 4 56 4 5 24 h0
    (fun _ hj => Hades.hadesMask_prefix 4 56 4 _ hj)
    (fun _ hj => Hades.hadesMask_suffix 4 56 4 _ hj)
    full_prefix full_suffix internal.toLinearMap {0} linear_middle_toLinearMap
    (fun _ hj => Hades.hadesMask_middle 4 56 4 _ hj) middle_bound

/-- **Forty-four active S-boxes, for every round-constant table.** Two distinct inputs incur at
least `44` charged S-box applications over the `64` rounds that follow the initial external
layer: at least `20` in the external rounds and at least `24` in the internal rounds
(`middle_bound`). A lower bound; it is not claimed to be attained. As a lower bound it supersedes
the `34` of `activity_with_partial`. -/
theorem activity_middle_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    44 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      (Hades.differenceTrace (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (external x) (external y)) 0 64 :=
  isTrail_activity_middle_general table (Hades.differenceTrace_isTrail _ _ _ 64)
    (Hades.differenceTrace_ne_zero _ (fun h => hxy (external.injective h)) 0)

/-- **Forty-four active S-boxes** for the pinned permutation. -/
theorem activity_middle {x y : State} (hxy : x ≠ y) :
    44 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 64 :=
  activity_middle_general values hxy

/-! ### The independent-key trail bounds -/

/-- **Trail bound in whole bits, for every round-constant table.** In the model with an
additional independent uniform key per round, the number of key sequences realising a fixed
nonzero trail `T`, times `2^11044`, is at most the number of all key sequences. Here `u = 4`
(`sbox_uniform`), each of the `44` charged S-boxes is charged `251` bits (`4 * 2^251 ≤ p`), and
`11044 = 251 * 44`. This concerns one trail in that model only: not the permutation with its
fixed constants, and not a differential. -/
theorem independent_key_probability_middle_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) (4 + 56 + 4)
        T x * 2 ^ 11044
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_probability_with_middle_bound (Idx := Fin 4) (K := F) (u := 4) (d := 251)
    4 56 4 5 24 {0} (fun _ _ => sbox) linear table (fun _ _ _ => sbox_uniform)
    four_mul_two_pow_le_card full_prefix full_suffix internal.toLinearMap
    linear_middle_toLinearMap middle_bound h0 x
  rwa [show 251 * ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 24) = 11044 by norm_num] at h

/-- **Trail bound in whole bits** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * 2^11044 ≤ |F^4|^(4 + 56 + 4)`. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 56 + 4) T x * 2 ^ 11044
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_middle_general values h0 x

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^44` (`p = modulus`), is at most `4^44` times the number of all
key sequences. Here `u = 4` (`sbox_uniform`), and the `44` charged S-boxes are counted as in
`activity_middle_general`. This concerns one trail in that model only: not the permutation with
its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) (4 + 56 + 4)
        T x * modulus ^ 44
      ≤ 4 ^ 44 * Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_probability_with_middle_bound_exact (Idx := Fin 4) (K := F) (u := 4)
    4 56 4 5 24 {0} (fun _ _ => sbox) linear table (fun _ _ _ => sbox_uniform) full_prefix
    full_suffix internal.toLinearMap linear_middle_toLinearMap middle_bound h0 x
  rwa [field_card, show (4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 24 = 44 by norm_num] at h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * p^44 ≤ 4^44 * |F^4|^(4 + 56 + 4)`. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 56 + 4) T x * modulus ^ 44
      ≤ 4 ^ 44 * Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_middle_exact_general values h0 x

set_option exponentiation.threshold 12000 in
/-- `2^11070 * 4^44 ≤ p^44`, by `decide`. `Checks/AztecBN254Middle.lean` shows that
`2^11071 * 4^44 ≤ p^44` fails, so `11070` is the largest such exponent. -/
theorem middle_sharp_exponent_bound : 2 ^ 11070 * 4 ^ 44 ≤ modulus ^ 44 := by
  decide

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^11070`, is at
most the number of all key sequences. It follows from
`independent_key_probability_middle_exact_general` and `middle_sharp_exponent_bound`, and `11070`
is the largest exponent that this arithmetic gives. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) (4 + 56 + 4)
        T x * 2 ^ 11070
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  Hades.mul_le_of_ratio (independent_key_probability_middle_exact_general table h0 x)
    middle_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model: for every
nonzero trail `T`, `keyCount * 2^11070 ≤ |F^4|^(4 + 56 + 4)`. This concerns one trail in that
model only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 56 + 4) T x * 2 ^ 11070
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_middle_sharp_general values h0 x

end Poseidon2.AztecBN254
