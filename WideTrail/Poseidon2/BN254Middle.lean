/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BN254
import WideTrail.Hades.Subspace
import WideTrail.Hades.Dimension
import WideTrail.Hades.Hull

/-! Partial-round activity for the pinned BN254 width-three permutation.

`BN254.lean` counts sixteen active S-boxes, all in the eight external rounds, and
charges nothing to the fifty-six internal rounds. This file counts those too.

The internal matrix leaves no nonzero difference inactive for three consecutive
rounds, so every window of three internal rounds applies the S-box to a nonzero
difference at least once. Fifty-six rounds hold eighteen disjoint windows.

The internal matrix is `diag (1, 1, 2) + J` (`internal_toLinearMap_eq`), and its diagonal
entries off coordinate `0` are distinct (`internalDiag_injOn`). So the general criterion
`Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff` gives a second proof of the three-round
statement (`internal_inactive_trivial_by_criterion`), and exactly `3 - r` dimensions of
differences stay inactive through `r ≤ 3` consecutive internal rounds
(`finrank_internal_inactive`).

The same count is carried into the independently keyed trail bound. As in
`BN254.lean`, that bound concerns one trail and an additional independent uniform
key per round. It says nothing about the fixed public constants alone, nor about
a differential.

The last section bounds a differential in the same model
(`independent_key_differential_exact`, `independent_key_differential_sharp`): for every
nonzero input difference, the key count over the `64` rounds that follow the initial
external layer, times `p^3`, is at most `4^3` times the number of all key sequences, and
times `2^754` it is at most that number. Only `3` S-boxes of the first two external rounds
are charged, one fewer than the branch number `4`. This too says nothing about the fixed
public constants alone, or about any one key. -/

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

/-! ### The exact ratio and the sharp exponent

`independent_key_probability_with_partial` charges `251` bits per charged S-box, the largest
`d` with `4 * 2^d ≤ p`, so `8534` bits over the `34` charged S-boxes. Keeping the ratio `p / 4`
exact (`independent_key_probability_exact`) gives `8554` bits
(`independent_key_probability_sharp`), since `34 * log2 (p / 4) ≈ 8554.3`. Both charge the
`34` S-boxes of `independent_key_probability_with_partial` (`16` in the external rounds and
`56 / 3 = 18` in the internal rounds), of which `independent_key_probability_exact` is the
exact-ratio form. No exact-ratio form of the `16`-S-box bound `independent_key_probability` of
`BN254.lean` is stated. The sample space is the same: one trail, an additional independent
uniform key per round. -/

namespace Poseidon2.BN254

/-- **Trail bound as an exact ratio**, for the additional-independent-key model only: for every
nonzero trail `T`, the number of key sequences realising `T`, times `p^34` (`p = modulus`), is
at most `4^34` times the number of all key sequences. Here `u = 4` (`sbox_uniform`), and the
`34` charged S-boxes (`16` in the external rounds, `56 / 3 = 18` in the internal rounds) are
counted as in `activity_with_partial`: this is the exact-ratio form of
`independent_key_probability_with_partial`, not of the `16`-S-box `independent_key_probability`.
The exponent keeps its round-count arithmetic, as in `independent_key_probability_with_partial`.
This concerns one trail in that model: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_exact {T : Nat → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values)
        (4 + 56 + 4) T x * modulus ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 56 / 3)
      ≤ 4 ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 56 / 3)
        * Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_probability_with_middle_exact (Idx := Fin 3) (K := F) (u := 4)
    4 56 4 4 3 {0} (fun _ _ => sbox) linear values
    (fun _ _ _ => sbox_uniform) full_prefix full_suffix
    internal linear_middle internal_inactive_trivial h0 x
  rw [field_card] at h
  exact h

set_option exponentiation.threshold 9000 in
/-- `2^8554 * 4^34 ≤ p^34`, by `decide`. `BN254Checks.lean` shows that `2^8555 * 4^34 ≤ p^34`
fails, so `8554` is the largest such exponent. -/
theorem sharp_exponent_bound :
    2 ^ 8554 * 4 ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 56 / 3)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 56 / 3) := by
  decide

/-- **Trail bound with the sharp exponent**, in the same model: for every nonzero trail `T`, the
number of key sequences realising `T`, times `2^8554`, is at most the number of all key
sequences. It follows from `independent_key_probability_exact` and `sharp_exponent_bound`, and
`8554` is the largest exponent that this arithmetic gives. This concerns one trail in that model
only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_sharp {T : Nat → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values)
        (4 + 56 + 4) T x * 2 ^ 8554
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) :=
  Hades.mul_le_of_ratio (independent_key_probability_exact h0 x) sharp_exponent_bound
    (pow_pos (by norm_num) _)

end Poseidon2.BN254

/-! ### The internal matrix as `diag (1, 1, 2) + J`, and the diagonal criterion

`internal_inactive_trivial` is proved by combining the three conditions with explicit ring
identities. The internal matrix `[[2, 1, 1], [1, 2, 1], [1, 1, 3]]` is `diag (1, 1, 2) + J`
(`internal_toLinearMap_eq`), the Poseidon2 internal-layer form `diagPlusOnes 1 internalDiag`.
Its diagonal entries off coordinate `0`, namely `1` and `2`, are distinct in `F`
(`internalDiag_injOn`), so the general criterion `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff`
gives a second proof of the same statement (`internal_inactive_trivial_by_criterion`), and the
space of differences that stay inactive through `r ≤ 3` consecutive internal rounds has
dimension exactly `3 - r` (`finrank_internal_inactive`).

These are statements about inactive differences of the internal rounds only: they are the
linear-algebra fact behind "at most `2` consecutive internal rounds can be linearized", not a
proof of resistance to subspace trails in general, and they say nothing about the external
rounds. -/

namespace Poseidon2.BN254

/-- The diagonal `(1, 1, 2)` of the internal matrix, written as `diag (1, 1, 2) + J`. -/
def internalDiag : Fin 3 → F := ![1, 1, 2]

/-- **The internal layer is `diag (1, 1, 2) + J`.** -/
theorem internal_toLinearMap_eq : internal.toLinearMap = diagPlusOnes (1 : F) internalDiag := by
  refine LinearMap.ext fun x => ?_
  funext i
  rw [diagPlusOnes_apply, Fin.sum_univ_three]
  fin_cases i <;> simp [internal, internalDiag] <;> ring

/-- The entries `1` and `2` of the diagonal off coordinate `0` are distinct in `F`. -/
theorem internalDiag_injOn : Set.InjOn internalDiag {i | i ≠ 0} := fun i hi j hj h =>
  (by decide : ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → internalDiag i = internalDiag j → i = j)
    i j hi hj h

/-- **No nonzero difference stays off the S-box coordinate through three internal rounds**:
the statement of `internal_inactive_trivial`, proved by the diagonal criterion. -/
theorem internal_inactive_trivial_by_criterion :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 3)) 3 = ⊥ := by
  have h := (Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff (one_ne_zero : (1 : F) ≠ 0)
    internalDiag (0 : Fin 3)).mpr internalDiag_injOn
  rw [Fintype.card_fin] at h
  rw [internal_toLinearMap_eq]
  exact h

/-- **Exactly `3 - r` dimensions of differences stay off the S-box coordinate through `r`
consecutive internal rounds**, for `r ≤ 3`. -/
theorem finrank_internal_inactive {r : ℕ} (hr : r ≤ 3) :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 3)) r) =
      3 - r := by
  have h := Hades.finrank_inactiveSpace_diagPlusOnes (one_ne_zero : (1 : F) ≠ 0) internalDiag
    (0 : Fin 3) internalDiag_injOn (r := r) (by rw [Fintype.card_fin]; exact hr)
  rw [Fintype.card_fin] at h
  rw [internal_toLinearMap_eq]
  exact h

end Poseidon2.BN254

/-! ### The independent-key differential bound

The trail bounds above concern one trail. `independent_key_differential_exact` bounds a
differential, the sum over all trails from a nonzero input difference `a` to an output difference
`b`, in the same model with an additional independent uniform key per round
(`Hades.hades_differential_bound`). It charges `3` S-boxes of the first two external rounds, one
fewer than the branch number `4` of the external matrix (`external_branch`), at the ratio `p / 4`
each; the other rounds are not charged. Since `3 * log2 (p / 4) ≈ 754.8`, the sharp exponent is
`754` (`independent_key_differential_sharp`). Nothing here concerns the permutation with its
fixed constants. -/

namespace Poseidon2.BN254

/-- **Differential bound as an exact ratio**, for the additional-independent-key model only: for
every nonzero input difference `a`, every output difference `b` and every input `x`, the number of
key sequences under which `(x, x + a)` has output difference `b` after the `64` rounds, times
`p^3` (`p = modulus`), is at most `4^3` times the number of all key sequences. Here `u = 4`
(`sbox_uniform`) and the branch number is `4` (`external_branch`). This concerns the
key-averaged differential only: not the permutation with its fixed constants, and not any one
key. -/
theorem independent_key_differential_exact {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values)
        (4 + 56 + 4) a b x * modulus ^ 3
      ≤ 4 ^ 3 * Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_differential_bound (Idx := Fin 3) (K := F) (u := 4) 4 56 4 4
    (by norm_num) {0} (fun _ _ => sbox) linear values (fun _ _ _ => sbox_uniform)
    (full_prefix 0 (by norm_num)) ha b x
  rw [field_card, show (4 : ℕ) - 1 = 3 from rfl] at h
  exact h

set_option exponentiation.threshold 1000 in
/-- `2^754 * 4^3 ≤ p^3`, by `decide`. `BN254Checks.lean` shows that `2^755 * 4^3 ≤ p^3` fails,
so `754` is the largest such exponent. -/
theorem differential_sharp_exponent_bound : 2 ^ 754 * 4 ^ 3 ≤ modulus ^ 3 := by
  decide

/-- **Differential bound with the sharp exponent**, in the same model: for every nonzero input
difference `a`, the key count of the differential `(a, b)`, times `2^754`, is at most the number
of all key sequences. It follows from `independent_key_differential_exact` and
`differential_sharp_exponent_bound`, and `754` is the largest exponent that this arithmetic
gives. This concerns the key-averaged differential only: not the permutation with its fixed
constants, and not any one key. -/
theorem independent_key_differential_sharp {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values)
        (4 + 56 + 4) a b x * 2 ^ 754
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) :=
  Hades.mul_le_of_ratio (independent_key_differential_exact ha b x)
    differential_sharp_exponent_bound (pow_pos (by norm_num) _)

end Poseidon2.BN254
