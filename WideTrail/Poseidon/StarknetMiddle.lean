/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon.Starknet
import WideTrail.Hades.Automaton
import WideTrail.Poseidon.Certificates.StarknetAutomaton

/-!
# Starknet's Poseidon: fifty-seven charged S-boxes

`WideTrail.Poseidon.Starknet` charges the `83` partial rounds of Starknet's Poseidon permutation
through windows: no nonzero difference stays inactive through `3` consecutive partial rounds, so
the partial rounds charge at least `83 / 3 = 27` S-boxes, and two distinct inputs incur at least
`43` charged S-box applications. This file proves that every trail through the `83` partial
rounds charges at least `41` S-boxes, so the count is at least `16 + 41 = 57`. As a lower bound,
`57` supersedes `43`; the theorems of `WideTrail.Poseidon.Starknet` are unchanged.

The middle bound is a forward-space automaton certificate (`WideTrail.Hades.Automaton`) with
`84` states, each a set of differences given by the linear functionals that vanish on it. Every
trail can be followed through the states, the difference entering each round lying in the set of
the current state, and the potential of the current state drops by one at every inactive round
and grows by at most one at every active round. The start potential is `2`, so `83` rounds with
`s` active rounds satisfy `83 - s ≤ 2 + s`, that is `s ≥ (83 + 1 - 2) / 2 = 41`. The certificate
data and its kernel check are in `WideTrail.Poseidon.Certificates.StarknetAutomaton`. The partial
rounds have the S-box on coordinate `2` and the matrix `M = diag (2, -2, -3) + J`
(`mds_toLinearMap_eq`); there is no linear layer before round `0`.

## Results, for the pinned round constants and for every round-constant table

* `middle_bound`: every trail (`Hades.IsTrail`) through `83` consecutive rounds with the linear
  layer `M` and mask `{2}`, from a nonzero difference, charges at least `41` S-boxes.
  `middle_bound_diag`: the same for `diag (2, -2, -3) + J`, which is `M`.
  `Checks/StarknetMiddle.lean` exhibits a trail through the `83` rounds with exactly `41` active
  rounds, so `41` is the largest middle bound for these rounds.
* `isTrail_activity_middle_general`, `activity_middle_general`, `activity_middle`: every trail in
  the `IsTrail` model through the `91` rounds from a nonzero difference, and so every pair of
  distinct inputs, incurs at least `57` charged S-box applications: at least `16` in the full
  rounds and at least `41` in the partial rounds. `Checks/StarknetMiddle.lean` exhibits a trail in
  the `IsTrail` model through the `91` rounds that charges exactly `57`, so no argument that uses
  only `IsTrail` gives more.
* `independent_key_probability_middle`, `independent_key_probability_middle_general`: for every
  nonzero trail `T`, `keyCount * 2^14250 ≤ |F^3|^(4 + 83 + 4)`, charging `250` bits per charged
  S-box (`250` is the largest `d` with `2 * 2^d ≤ p`), and `14250 = 250 * 57`.
* `independent_key_probability_middle_exact`, `independent_key_probability_middle_sharp` and their
  `_general` forms: `keyCount * p^57 ≤ 2^57 * |F^3|^(4 + 83 + 4)` and
  `keyCount * 2^14250 ≤ |F^3|^(4 + 83 + 4)`. `14250` is the largest exponent this arithmetic gives
  for `57` charged S-boxes (`middle_sharp_exponent_bound`; `Checks/StarknetMiddle.lean` shows that
  `14251` fails): since `p` is barely above `2^251`, the exact ratio gives the same exponent as
  the whole-bit charge.

## What is not claimed

The counts are lower bounds on charged S-boxes for every trail in the `IsTrail` model, and hence
for every pair of distinct inputs. The trails of the checks that attain `41` and `57` are trails
in that model; they are not claimed to be realised by an input pair or a key, so `57` is not
claimed to be the least number of S-boxes an actual input pair incurs. The probability statements
concern one trail in the model with an additional independent uniform key per round: not the
permutation with its fixed constants, not a differential, and not any one key.
-/

set_option autoImplicit false

open Poseidon.Certificates.Starknet (fieldModulus mdsRows states automaton_check start_pot)

namespace Poseidon.Starknet

/-! ### The middle bound -/

/-- The certificate's prime is the instance's modulus. -/
theorem fieldModulus_eq : fieldModulus = modulus :=
  rfl

/-- The matrix `M` is the matrix of the certificate's table `mdsRows`, entry by entry, by
`decide`. -/
theorem mdsMatrix_eq_mat : mdsMatrix = Hades.AutomatonCheck.mat modulus 3 mdsRows := by
  ext i k
  fin_cases i <;> fin_cases k <;> decide

/-- The linear layer acts as the matrix of `mdsRows`. -/
theorem mds_eq_mat_mulVec (v : State) :
    mds.toLinearMap v = (Hades.AutomatonCheck.mat modulus 3 mdsRows).mulVec v := by
  rw [← mdsMatrix_eq_mat]
  exact mds_eq_mulVec v

/-- **Forty-one charged S-boxes in the partial rounds.** Every trail through `83` consecutive
rounds with the linear layer `M = [[3, 1, 1], [1, -1, 1], [1, 1, -2]]` and mask `{2}`, from a
nonzero difference, charges at least `41` S-boxes. The proof is the automaton certificate
`Certificates.Starknet.automaton_check`, whose start state has potential `2`. A lower bound in
the `IsTrail` model. -/
theorem middle_bound :
    Hades.MiddleBound mds.toLinearMap ({2} : Finset (Fin 3)) 83 41 := by
  have h := Hades.MiddleBound.of_automatonCheck (p := modulus) mds.toLinearMap 2 83
    mdsRows 0 states mds_eq_mat_mulVec automaton_check
  rwa [start_pot] at h

/-- **The same for `diag (2, -2, -3) + J`**, which is `M` (`mds_toLinearMap_eq`). -/
theorem middle_bound_diag :
    Hades.MiddleBound (Poseidon2.diagPlusOnes (1 : F) mdsDiag) ({2} : Finset (Fin 3)) 83 41 := by
  rw [← mds_toLinearMap_eq]
  exact middle_bound

/-! ### Activity -/

/-- **Fifty-seven charged S-boxes for every trail, for every round-constant table.** Every trail
in the `IsTrail` model through the `91` rounds, from a nonzero difference, charges at least `57`
S-boxes: at least `16` in the full rounds and at least `41` in the partial rounds
(`middle_bound`). -/
theorem isTrail_activity_middle_general (table : ℕ → State) {T : ℕ → State}
    (hT : Hades.IsTrail (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table)
      T 91)
    (h0 : T 0 ≠ 0) :
    57 ≤ Hades.scheduledWeight
      (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) T 0 91 :=
  hT.outer_middle_bound_of 4 83 4 4 41 h0
    (fun _ hj => Hades.hadesMask_prefix 4 83 4 _ hj)
    (fun _ hj => Hades.hadesMask_suffix 4 83 4 _ hj)
    (fun _ _ => mds_branch) (fun _ _ => mds_branch) mds.toLinearMap {2} (fun _ _ => rfl)
    (fun _ hj => Hades.hadesMask_middle 4 83 4 _ hj) middle_bound

/-- **Fifty-seven active S-boxes, for every round-constant table.** Two distinct inputs incur at
least `57` charged S-box applications over the `91` rounds: at least `16` in the full rounds and
at least `41` in the partial rounds (`middle_bound`). A lower bound; it is not claimed to be
attained by an input pair. As a lower bound it supersedes the `43` of `activity_with_partial`. -/
theorem activity_middle_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    57 ≤ Hades.scheduledWeight
      (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table)
      (Hades.differenceTrace
        (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) x y) 0 91 :=
  isTrail_activity_middle_general table (Hades.differenceTrace_isTrail _ _ _ 91)
    (Hades.differenceTrace_ne_zero _ hxy 0)

/-- **Fifty-seven active S-boxes** for the pinned permutation. -/
theorem activity_middle {x y : State} (hxy : x ≠ y) :
    57 ≤ Hades.scheduledWeight rounds (Hades.differenceTrace rounds x y) 0 91 :=
  activity_middle_general values hxy

/-! ### The independent-key trail bounds -/

/-- **Trail bound in whole bits, for every round-constant table.** In the model with an
additional independent uniform key per round, the number of key sequences realising a fixed
nonzero trail `T`, times `2^14250`, is at most the number of all key sequences. Here `u = 2`
(`sbox_uniform`), each of the `57` charged S-boxes is charged `250` bits (`2 * 2^250 ≤ p`), and
`14250 = 250 * 57`. This concerns one trail in that model only: not the permutation with its
fixed constants, and not a differential. -/
theorem independent_key_probability_middle_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table)
        (4 + 83 + 4) T x * 2 ^ 14250
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 83 + 4) := by
  have h := Hades.hades_probability_with_middle_bound (Idx := Fin 3) (K := F) (u := 2) (d := 250)
    4 83 4 4 41 {2} (fun _ _ => sbox) (fun _ => mds) table (fun _ _ _ => sbox_uniform)
    two_mul_two_pow_le_card (fun _ _ => mds_branch) (fun _ _ => mds_branch) mds.toLinearMap
    (fun _ _ => rfl) middle_bound h0 x
  rwa [show 250 * ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 41) = 14250 by norm_num] at h

/-- **Trail bound in whole bits** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * 2^14250 ≤ |F^3|^(4 + 83 + 4)`. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 83 + 4) T x * 2 ^ 14250
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 83 + 4) :=
  independent_key_probability_middle_general values h0 x

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^57` (`p = modulus`), is at most `2^57` times the number of all
key sequences. Here `u = 2` (`sbox_uniform`), and the `57` charged S-boxes are counted as in
`activity_middle_general`. This concerns one trail in that model only: not the permutation with
its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table)
        (4 + 83 + 4) T x * modulus ^ 57
      ≤ 2 ^ 57 * Fintype.card (Fin 3 → F) ^ (4 + 83 + 4) := by
  have h := Hades.hades_probability_with_middle_bound_exact (Idx := Fin 3) (K := F) (u := 2)
    4 83 4 4 41 {2} (fun _ _ => sbox) (fun _ => mds) table (fun _ _ _ => sbox_uniform)
    (fun _ _ => mds_branch) (fun _ _ => mds_branch) mds.toLinearMap (fun _ _ => rfl)
    middle_bound h0 x
  rwa [field_card, show (4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 41 = 57 by norm_num] at h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * p^57 ≤ 2^57 * |F^3|^(4 + 83 + 4)`. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 83 + 4) T x * modulus ^ 57
      ≤ 2 ^ 57 * Fintype.card (Fin 3 → F) ^ (4 + 83 + 4) :=
  independent_key_probability_middle_exact_general values h0 x

set_option exponentiation.threshold 15000 in
/-- `2^14250 * 2^57 ≤ p^57`, by `decide`. `Checks/StarknetMiddle.lean` shows that
`2^14251 * 2^57 ≤ p^57` fails, so `14250` is the largest such exponent. -/
theorem middle_sharp_exponent_bound : 2 ^ 14250 * 2 ^ 57 ≤ modulus ^ 57 := by
  decide

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^14250`, is at
most the number of all key sequences. It follows from
`independent_key_probability_middle_exact_general` and `middle_sharp_exponent_bound`, and `14250`
is the largest exponent that this arithmetic gives; it equals the whole-bit exponent of
`independent_key_probability_middle_general`. This concerns one trail in that model only: not
the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table)
        (4 + 83 + 4) T x * 2 ^ 14250
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 83 + 4) :=
  Hades.mul_le_of_ratio (independent_key_probability_middle_exact_general table h0 x)
    middle_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model: for every
nonzero trail `T`, `keyCount * 2^14250 ≤ |F^3|^(4 + 83 + 4)`. This concerns one trail in that
model only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 83 + 4) T x * 2 ^ 14250
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 83 + 4) :=
  independent_key_probability_middle_sharp_general values h0 x

end Poseidon.Starknet
