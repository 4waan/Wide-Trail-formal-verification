/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BN254Middle
import WideTrail.Hades.Automaton
import WideTrail.Poseidon2.Certificates.BN254Automaton

/-!
# HorizenLabs BN254, width three: forty-three charged S-boxes

`WideTrail.Poseidon2.BN254Middle` charges the `56` partial rounds of the pinned BN254 width-three
permutation through windows: no nonzero difference stays inactive through `3` consecutive partial
rounds, so the partial rounds charge at least `56 / 3 = 18` S-boxes, and two distinct inputs incur
at least `34` charged S-box applications. This file proves that every trail through the `56`
partial rounds charges at least `27` S-boxes, so the count is at least `16 + 27 = 43`. As a lower
bound, `43` supersedes `34`; the theorems of `WideTrail.Poseidon2.BN254` and
`WideTrail.Poseidon2.BN254Middle` are unchanged.

The middle bound is a forward-space automaton certificate (`WideTrail.Hades.Automaton`) with
`57` states, each a set of differences given by the linear functionals that vanish on it. Every
trail can be followed through the states, the difference entering each round lying in the set of
the current state, and the potential of the current state drops by one at every inactive round
and grows by at most one at every active round. The start potential is `2`, so `56` rounds with
`s` active rounds satisfy `56 - s ≤ 2 + s`, that is `s ≥ (56 + 1 - 2) / 2 = 27`. The certificate
data and its kernel check are in `WideTrail.Poseidon2.Certificates.BN254Automaton`.

## Results, for the pinned round constants and for every round-constant table

* `middle_bound`: every trail (`Hades.IsTrail`) through `56` consecutive rounds with the internal
  layer and mask `{0}`, from a nonzero difference, charges at least `27` S-boxes.
  `middle_bound_diag`: the same for `diag (1, 1, 2) + J`, which is that layer.
  `Checks/BN254MiddleSharp.lean` exhibits a trail through the `56` rounds with exactly `27` active
  rounds, so `27` is the largest middle bound for these rounds.
* `isTrail_activity_middle_general`, `activity_middle_general`, `activity_middle`: every trail in
  the `IsTrail` model through the `64` rounds from a nonzero difference, and so every pair of
  distinct inputs, incurs at least `43` charged S-box applications: at least `16` in the external
  rounds and at least `27` in the internal rounds. `Checks/BN254MiddleSharp.lean` exhibits a trail
  in the `IsTrail` model through the `64` rounds that charges exactly `43`, so no argument that
  uses only `IsTrail` gives more.
* `independent_key_probability_middle`, `independent_key_probability_middle_general`: for every
  nonzero trail `T`, `keyCount * 2^10793 ≤ |F^3|^(4 + 56 + 4)`, charging `251` bits per charged
  S-box (`251` is the largest `d` with `4 * 2^d ≤ p`), and `10793 = 251 * 43`.
* `independent_key_probability_middle_exact`, `independent_key_probability_middle_sharp` and their
  `_general` forms: `keyCount * p^43 ≤ 4^43 * |F^3|^(4 + 56 + 4)` and
  `keyCount * 2^10818 ≤ |F^3|^(4 + 56 + 4)`. `10818` is the largest exponent this arithmetic
  gives (`middle_sharp_exponent_bound`; `Checks/BN254MiddleSharp.lean` shows that `10819`
  fails).

## What is not claimed

The counts are lower bounds on charged S-boxes for every trail in the `IsTrail` model, and hence
for every pair of distinct inputs. The trails of the checks that attain `27` and `43` are trails
in that model; they are not claimed to be realised by an input pair or a key, so `43` is not
claimed to be the least number of S-boxes an actual input pair incurs. The probability statements
concern one trail in the model with an additional independent uniform key per round: not the
permutation with its fixed constants, not a differential, and not any one key.
-/

set_option autoImplicit false

open Poseidon2.Certificates.BN254 (fieldModulus internalRows states automaton_check start_pot)

namespace Poseidon2.BN254

/-! ### The middle bound -/

/-- The certificate's prime is the instance's modulus. -/
theorem fieldModulus_eq : fieldModulus = modulus :=
  rfl

/-- The internal matrix is the matrix of the certificate's table `internalRows`, entry by entry,
by `decide`. -/
theorem internalMatrix_eq_mat :
    internalMatrix = Hades.AutomatonCheck.mat modulus 3 internalRows := by
  ext i k
  fin_cases i <;> fin_cases k <;> decide

/-- The internal layer acts as the matrix of `internalRows`. -/
theorem internal_eq_mat_mulVec (v : State) :
    internal.toLinearMap v = (Hades.AutomatonCheck.mat modulus 3 internalRows).mulVec v := by
  rw [← internalMatrix_eq_mat]
  exact internal_eq_mulVec v

/-- **Twenty-seven charged S-boxes in the partial rounds.** Every trail through `56` consecutive
rounds with the internal layer `[[2, 1, 1], [1, 2, 1], [1, 1, 3]]` and mask `{0}`, from a nonzero
difference, charges at least `27` S-boxes. The proof is the automaton certificate
`Certificates.BN254.automaton_check`, whose start state has potential `2`. A lower bound in the
`IsTrail` model. -/
theorem middle_bound :
    Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 3)) 56 27 := by
  have h := Hades.MiddleBound.of_automatonCheck (p := modulus) internal.toLinearMap 0 56
    internalRows 0 states internal_eq_mat_mulVec automaton_check
  rwa [start_pot] at h

/-- **The same for `diag (1, 1, 2) + J`**, which is the internal layer (`internal_toLinearMap_eq`).
-/
theorem middle_bound_diag :
    Hades.MiddleBound (diagPlusOnes (1 : F) internalDiag) ({0} : Finset (Fin 3)) 56 27 := by
  rw [← internal_toLinearMap_eq]
  exact middle_bound

/-! ### Activity -/

/-- The linear maps of the internal rounds, as linear maps. -/
theorem linear_middle_toLinearMap (j : ℕ) (hj : j < 56) :
    (linear (4 + j) : Module.End F State) = internal.toLinearMap := by
  rw [linear_middle j hj]

/-- **Forty-three charged S-boxes for every trail, for every round-constant table.** Every trail
in the `IsTrail` model through the `64` rounds, from a nonzero difference, charges at least `43`
S-boxes: at least `16` in the external rounds and at least `27` in the internal rounds
(`middle_bound`). -/
theorem isTrail_activity_middle_general (table : ℕ → State) {T : ℕ → State}
    (hT : Hades.IsTrail (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) T 64)
    (h0 : T 0 ≠ 0) :
    43 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      T 0 64 :=
  hT.outer_middle_bound_of 4 56 4 4 27 h0
    (fun _ hj => Hades.hadesMask_prefix 4 56 4 _ hj)
    (fun _ hj => Hades.hadesMask_suffix 4 56 4 _ hj)
    full_prefix full_suffix internal.toLinearMap {0} linear_middle_toLinearMap
    (fun _ hj => Hades.hadesMask_middle 4 56 4 _ hj) middle_bound

/-- **Forty-three active S-boxes, for every round-constant table.** Two distinct inputs incur at
least `43` charged S-box applications over the `64` rounds that follow the initial external
layer: at least `16` in the external rounds and at least `27` in the internal rounds
(`middle_bound`). A lower bound; it is not claimed to be attained by an input pair. As a lower
bound it supersedes the `34` of `activity_with_partial`. -/
theorem activity_middle_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    43 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      (Hades.differenceTrace (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (external x) (external y)) 0 64 :=
  isTrail_activity_middle_general table (Hades.differenceTrace_isTrail _ _ _ 64)
    (Hades.differenceTrace_ne_zero _ (fun h => hxy (external.injective h)) 0)

/-- **Forty-three active S-boxes** for the pinned permutation. -/
theorem activity_middle {x y : State} (hxy : x ≠ y) :
    43 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 64 :=
  activity_middle_general values hxy

/-! ### The independent-key trail bounds -/

/-- **Trail bound in whole bits, for every round-constant table.** In the model with an
additional independent uniform key per round, the number of key sequences realising a fixed
nonzero trail `T`, times `2^10793`, is at most the number of all key sequences. Here `u = 4`
(`sbox_uniform`), each of the `43` charged S-boxes is charged `251` bits (`4 * 2^251 ≤ p`), and
`10793 = 251 * 43`. This concerns one trail in that model only: not the permutation with its
fixed constants, and not a differential. -/
theorem independent_key_probability_middle_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) (4 + 56 + 4)
        T x * 2 ^ 10793
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) := by
  have hd : 4 * 2 ^ 251 ≤ Fintype.card F := by
    rw [field_card]
    decide
  have h := Hades.hades_probability_with_middle_bound (Idx := Fin 3) (K := F) (u := 4) (d := 251)
    4 56 4 4 27 {0} (fun _ _ => sbox) linear table (fun _ _ _ => sbox_uniform) hd full_prefix
    full_suffix internal.toLinearMap linear_middle_toLinearMap middle_bound h0 x
  rwa [show 251 * ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 27) = 10793 by norm_num] at h

/-- **Trail bound in whole bits** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * 2^10793 ≤ |F^3|^(4 + 56 + 4)`. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values) (4 + 56 + 4)
        T x * 2 ^ 10793
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_middle_general values h0 x

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^43` (`p = modulus`), is at most `4^43` times the number of all
key sequences. Here `u = 4` (`sbox_uniform`), and the `43` charged S-boxes are counted as in
`activity_middle_general`. This concerns one trail in that model only: not the permutation with
its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) (4 + 56 + 4)
        T x * modulus ^ 43
      ≤ 4 ^ 43 * Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_probability_with_middle_bound_exact (Idx := Fin 3) (K := F) (u := 4)
    4 56 4 4 27 {0} (fun _ _ => sbox) linear table (fun _ _ _ => sbox_uniform) full_prefix
    full_suffix internal.toLinearMap linear_middle_toLinearMap middle_bound h0 x
  rwa [field_card, show (4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 27 = 43 by norm_num] at h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * p^43 ≤ 4^43 * |F^3|^(4 + 56 + 4)`. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values) (4 + 56 + 4)
        T x * modulus ^ 43
      ≤ 4 ^ 43 * Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_middle_exact_general values h0 x

set_option exponentiation.threshold 11000 in
/-- `2^10818 * 4^43 ≤ p^43`, by `decide`. `Checks/BN254MiddleSharp.lean` shows that
`2^10819 * 4^43 ≤ p^43` fails, so `10818` is the largest such exponent. -/
theorem middle_sharp_exponent_bound : 2 ^ 10818 * 4 ^ 43 ≤ modulus ^ 43 := by
  decide

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^10818`, is at
most the number of all key sequences. It follows from
`independent_key_probability_middle_exact_general` and `middle_sharp_exponent_bound`, and `10818`
is the largest exponent that this arithmetic gives. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) (4 + 56 + 4)
        T x * 2 ^ 10818
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) :=
  Hades.mul_le_of_ratio (independent_key_probability_middle_exact_general table h0 x)
    middle_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model: for every
nonzero trail `T`, `keyCount * 2^10818 ≤ |F^3|^(4 + 56 + 4)`. This concerns one trail in that
model only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values) (4 + 56 + 4)
        T x * 2 ^ 10818
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_middle_sharp_general values h0 x

end Poseidon2.BN254
