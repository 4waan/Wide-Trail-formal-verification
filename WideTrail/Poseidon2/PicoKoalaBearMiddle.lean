/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.PicoKoalaBear
import WideTrail.Poseidon2.KoalaBearMiddle
import WideTrail.Poseidon2.Certificates.PicoKoalaBearRelations

/-!
# Pico KoalaBear: thirty-five charged S-boxes

`WideTrail.Poseidon2.PicoKoalaBear` charges the `20` partial rounds of the Pico v3.2.0 KoalaBear
permutation through windows: no nonzero difference stays inactive through `16` consecutive
partial rounds, so the partial rounds charge at least `20 / 16 = 1` S-box, and two distinct inputs
incur at least `33` charged S-box applications. This file proves that every trail through the
`20` partial rounds charges at least `3` S-boxes, so the count is at least `35`. As a lower bound,
`35` supersedes `33`; the theorems of `WideTrail.Poseidon2.PicoKoalaBear` are unchanged.

The middle bound is a window-relation certificate (`WideTrail.Hades.WindowRelation`) for
`diag d + J` with Pico's diagonal `d = PicoKoalaBear.diag`, whose data and kernel check are in
`WideTrail.Poseidon2.Certificates.PicoKoalaBearRelations`; the window criterion comes from
`PicoKoalaBear.inactive_trivial`. The internal layer has no scale factor, so the bound for
`diag d + J` is the bound for the code's layer. Field, S-box and exponent arithmetic are those of
SP1's KoalaBear instance and are reused from `WideTrail.Poseidon2.KoalaBearMiddle`
(`KoalaBear.middle_sharp_exponent_bound`).

## Results

* `middle_bound`, `internal_middle_bound`: every trail (`Hades.IsTrail`) through `20` consecutive
  partial rounds with `diag d + J`, from a nonzero difference, charges at least `3` S-boxes.
  `Checks/KoalaBearMiddle.lean` exhibits a trail through `20` rounds with linear map `diag d + J`
  (the code's layer) and mask `{0}` whose active rounds are exactly `0`, `2` and `4`, so `3` is the
  largest middle bound for these rounds.
* `activity_middle`, `activity_middle_general`: two distinct inputs incur at least `35` charged
  S-box applications over the `28` rounds, `32` in the full rounds and `3` in the partial rounds,
  for the pinned round constants and for every round-constant table.
* `independent_key_probability_middle`, `independent_key_probability_middle_general`: for every
  nonzero trail `T`, `keyCount * 2^1015 ≤ |F^16|^(8 + 20)` (`29` bits per charged S-box,
  `1015 = 29 * 35`).
* `independent_key_probability_middle_exact`, `independent_key_probability_middle_sharp` and
  their `_general` forms: `keyCount * p^35 ≤ 2^35 * |F^16|^(8 + 20)` and
  `keyCount * 2^1049 ≤ |F^16|^(8 + 20)`; `1049` is the largest exponent this arithmetic gives.

## What is not claimed

The counts are lower bounds on charged S-box applications in the `IsTrail` model, for actual input
pairs; they are not claimed to be attained, and the trail with three active partial rounds of the
checks is a trail in that model, not claimed to be realised by an input pair. The probability
statements concern one trail in the model with an additional independent uniform key per round:
not the permutation with its fixed constants, not a differential, and not any one key. Nothing is
said about the full rounds beyond the existing count of `32`.
-/

set_option autoImplicit false

open Poseidon2.KoalaBear (F State modulus field_card sbox sbox_uniform m4Primes_ne_zero)
open Poseidon2.Certificates.PicoKoalaBear (diagonal psi gamma singles pairs relations_check)

namespace Poseidon2.PicoKoalaBear

/-! ### The middle bound -/

/-- Pico's diagonal is the list `diagonal` of the certificate, entry by entry, by `decide`. -/
theorem diag_eq_diagonal : ∀ k : Fin 16, diag k = Hades.RelationCheck.ent modulus diagonal k := by
  decide

/-- No nonzero difference stays inactive through `20` consecutive partial rounds with
`diag d + J` (from `inactive_trivial` for `16`). -/
theorem inactive_twenty :
    Hades.inactiveSpace (diagPlusOnes (1 : F) diag) ({0} : Finset (Fin 16)) 20 = ⊥ :=
  eq_bot_iff.mpr ((Hades.inactiveSpace_anti _ _ (by norm_num)).trans inactive_trivial.le)

/-- **Three charged S-boxes in the partial rounds.** Every trail through `20` consecutive partial
rounds with `diag d + J`, `d = PicoKoalaBear.diag`, from a nonzero difference, charges at least
`3` S-boxes. The proof is the relation certificate `Certificates.PicoKoalaBear.relations_check`.
A lower bound in the `IsTrail` model. -/
theorem middle_bound :
    Hades.MiddleBound (diagPlusOnes (1 : F) diag) ({0} : Finset (Fin 16)) 20 3 :=
  Hades.MiddleBound.of_relationCheck (p := modulus) _ 0 20 16 diagonal psi gamma singles pairs
    diag_eq_diagonal relations_check inactive_twenty

/-- **The same for the code's internal layer**, which is `diag d + J` itself. -/
theorem internal_middle_bound :
    Hades.MiddleBound internal.toLinearMap ({0} : Finset (Fin 16)) 20 3 := by
  rw [internal_toLinearMap]
  exact middle_bound

/-! ### Activity -/

/-- **Thirty-five active S-boxes, for every round-constant table.** Two distinct inputs incur at
least `35` charged S-box applications over the `28` rounds: `32` in the full rounds and `3` in the
partial rounds (`middle_bound`). A lower bound; it is not claimed to be attained. As a lower bound
it supersedes the `33` of `activity_general`. -/
theorem activity_middle_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    35 ≤ Hades.scheduledWeight (Plonky3.Diag.rounds conditions 20 sbox table)
      (Hades.differenceTrace (Plonky3.Diag.rounds conditions 20 sbox table) (external x)
        (external y)) 0 28 :=
  Plonky3.Diag.activity_with_middle_bound conditions m4Primes_ne_zero 20 sbox table middle_bound
    hxy

/-- **Thirty-five active S-boxes** for the pinned permutation. -/
theorem activity_middle {x y : State} (hxy : x ≠ y) :
    35 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 28 :=
  activity_middle_general values hxy

/-! ### The independent-key trail bounds -/

/-- **Trail bound in whole bits, for every round-constant table.** In the model with an
additional independent uniform key per round, the number of key sequences realising a fixed
nonzero trail `T`, times `2^1015`, is at most the number of all key sequences. Here `u = 2`
(`KoalaBear.sbox_uniform`), each of the `35` charged S-boxes is charged `29` bits
(`KoalaBear.two_mul_two_pow_le_card`), and `1015 = 29 * 35`. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) T x * 2 ^ 1015
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) := by
  have h := Plonky3.Diag.independent_key_probability_with_middle_bound conditions
    m4Primes_ne_zero 20 sbox table sbox_uniform KoalaBear.two_mul_two_pow_le_card middle_bound h0 x
  rwa [show 29 * (32 + 3) = 1015 by norm_num] at h

/-- **Trail bound in whole bits** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * 2^1015 ≤ |F^16|^(8 + 20)`. This concerns one trail in that model only: not
the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * 2 ^ 1015 ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_middle_general values h0 x

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^35` (`p = modulus`), is at most `2^35` times the number of all
key sequences. Here `u = 2` (`KoalaBear.sbox_uniform`), and the `35` charged S-boxes are counted
as in `activity_middle_general`. This concerns one trail in that model only: not the permutation
with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) T x * modulus ^ 35
      ≤ 2 ^ 35 * Fintype.card (Fin 16 → F) ^ (8 + 20) := by
  have h := Plonky3.Diag.independent_key_probability_with_middle_bound_exact conditions
    m4Primes_ne_zero 20 sbox table sbox_uniform middle_bound h0 x
  rwa [field_card, show 32 + 3 = 35 by norm_num] at h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the same model: for every nonzero
trail `T`, `keyCount * p^35 ≤ 2^35 * |F^16|^(8 + 20)`. This concerns one trail in that model only:
not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * modulus ^ 35
      ≤ 2 ^ 35 * Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_middle_exact_general values h0 x

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^1049`, is at most
the number of all key sequences. It follows from `independent_key_probability_middle_exact_general`
and `KoalaBear.middle_sharp_exponent_bound` (`2^1049 * 2^35 ≤ p^35`); `1049` is the largest
exponent that this arithmetic gives. This concerns one trail in that model only: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.Diag.rounds conditions 20 sbox table) (8 + 20) T x * 2 ^ 1049
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Hades.mul_le_of_ratio (independent_key_probability_middle_exact_general table h0 x)
    KoalaBear.middle_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model: for every
nonzero trail `T`, `keyCount * 2^1049 ≤ |F^16|^(8 + 20)`. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_middle_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * 2 ^ 1049 ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_middle_sharp_general values h0 x

end Poseidon2.PicoKoalaBear
