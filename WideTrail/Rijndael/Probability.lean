/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Rijndael.MixColumns
import WideTrail.Differential.AESConcrete
import WideTrail.Differential.Hull

/-!
# Rijndael-256: trail probabilities, two-round differentials and the final round

Every probability in this file is in the **independent-key model** of `Differential/Markov.lean`,
`Differential/Scheduled.lean` and `Differential/Hull.lean`: round `n` maps `z` to
`lam n (γ n (z + k n))`, and a probability is the number of key vectors `k` that realise an
event, divided by the number of all key vectors, `|X| ^ r` for `r` rounds. The keys are
independent and uniform. No key schedule is used anywhere.

## The state space

`card_state256`: the Rijndael-256 state `GridIdx 4 8 → GF256` has `2 ^ 256` elements, so the
key vectors of `r` rounds number `(2 ^ 256) ^ r`. Each bound below has the shape
`count · 2 ^ e ≤ (2 ^ 256) ^ r`, which reads as a probability of at most `2 ^ (-e)` without
division.

## Trail probabilities

`rijndael256Lin` is `MixColumns ∘ ShiftRows` at offsets `0, 1, 3, 4` (the linear layer of
`rijndael256LinSpec`) as an additive bijection. For a bricklayer `bricklayer s` of injective
S-boxes of differential uniformity at most `4` (each active S-box then costs a factor `2⁻⁶`,
since `4 · 2⁶ = 256`) and every sequence of differences `T` with `T 0 ≠ 0`:

| statement                               | rounds | S-boxes charged | per trail |
| --------------------------------------- | ------ | --------------- | --------- |
| `rijndael256_four_round_prob`           | `4`    | `25`            | `2⁻¹⁵⁰`   |
| `rijndael256_eight_round_prob`          | `8`    | `50`            | `2⁻³⁰⁰`   |
| `rijndael256_fourteen_round_prob`       | `14`   | `80`            | `2⁻⁴⁸⁰`   |
| `rijndael256_fourteen_round_prob_final` | `14`   | `80`            | `2⁻⁴⁸⁰`   |

The last column bounds the key-averaged probability of each such trail. The third column is the
lower bound on active S-boxes that the proof charges at `2⁻⁶` each: a trail with a nonzero count
is a trail of `rijndael256LinSpec` (`isTrail_of_trailKeyCount_ne_zero`), so the bounds of
`Rijndael/MixColumns.lean` apply to it.

`rijndael256_rounds_prob` is the statement at every round count `r`, with exponent
`6 · (r / 4 · 25 + 5 · [2 ≤ r % 4])`. Eight is the first round count at which that exponent
exceeds `256`, the block length (`Checks/Probability.lean`). The active-S-box counts are those
of `Rijndael/MixColumns.lean`; the S-box enters only through injectivity and its uniformity.
The `_probability` forms below state the same bounds for the AES S-box, which satisfies both
hypotheses (`AES.sbox_injective`, `AES.sbox_uniform`).

A trail bound bounds one summand of a differential: the count of key vectors under which one
input pair follows one sequence of differences. It is not a bound on a differential, and it is
not a bound on any probability of the cipher under one fixed key.

## The final round

The cipher's last round has no `MixColumns`. `lastRoundSchedule lam last R` is the schedule with
the linear map `lam` in rounds `0 … R - 2` and `last` in round `R - 1`, and `Scheduled` counts
key vectors for such schedules. `trailKeyCount_lastRoundSchedule` shows that the count for this
schedule equals the count for the uniform schedule `lam` on the sequence `relabelLast`, which
agrees with `T` except at index `R`, where it is `lam (last⁻¹ (T R))`. The relabelled sequence
starts with the same difference, and its weights in rounds `0 … R - 1` are those of `T`, so every
uniform bound carries over.

* `rijndael256_fourteen_round_prob_final`: fourteen rounds of Rijndael-256 with `ShiftRows`
  alone (`shiftRows256`) as the linear map of round `13`, at most `2⁻⁴⁸⁰` per trail.
* `aes128_ten_round_prob_final`, `aes192_twelve_round_prob_final`,
  `aes256_fourteen_round_prob_final`: the bounds `2⁻³³⁰`, `2⁻⁴⁵⁰` and `2⁻⁴⁸⁰` of
  `aes128_ten_round_prob`, `aes192_twelve_round_prob` and `aes256_fourteen_round_prob`, with
  `ShiftRows` alone (`aesShiftRows`) in the last round.

The schedule adds a key before the S-box layer of every round and has no key addition after the
last linear map. A key added there would not change any difference.

## Two-round differentials

`rijndael256_two_round_differential` and `aes128_two_round_differential`: with the AES S-box in
both rounds, every two-round differential `(a, b)` with `a ≠ 0` has key-averaged probability at
most `2⁻²⁴`. This bounds the differential itself, the sum over all two-round trails from `a` to
`b`. It is `Scheduled.bricklayer_two_round_bound` with branch number `5` and uniformity `4`:
`4` of the at least `5` active S-boxes are charged `2⁻⁶` each. The bound is coarse. For AES the
exact maximum two-round expected differential probability, averaged over independent round keys,
is `53 / 2³⁴`, about `2^(-28.27)` and between `2⁻²⁹` and `2⁻²⁸` (Keliher and Sui, ePrint
2005/321, abstract); for Rijndael-256 no exact value is used or claimed here.

`rijndael256_differential` and `aes128_differential` state the same bound for `R ≥ 2` rounds
and any linear maps after round `0`; only rounds `0` and `1` are charged, and the other rounds
enter only through bijectivity.

## What is not claimed

No bound here is claimed to be attained. Nothing here is about the key schedule, a fixed key,
related keys, differentials over more than two charged rounds, linear cryptanalysis, or any
attack. The bounds `2⁻¹⁵⁰` over four rounds and `2⁻³⁰⁰` over eight are the trail bounds the
designers of Rijndael state for every block length (proposal, §8.2.1); here they are theorems
in the independent-key model. None of this is new cryptanalysis.
-/

set_option autoImplicit false
-- The exponents here reach `480` and the moduli `(2 ^ 256) ^ 14`; `rw` would otherwise emit a
-- notice for declining to evaluate such powers as numerals, which it should decline to do.
set_option exponentiation.threshold 4000

namespace Rijndael

/-! ### The state space -/

/-- The Rijndael-256 state has `32` byte positions. -/
theorem card_gridIdx48 : Fintype.card (GridIdx 4 8) = 32 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- The Rijndael-256 state space has `2 ^ 256` elements, so a key vector for `r` rounds of the
independent-key model ranges over `(2 ^ 256) ^ r` values. -/
theorem card_state256 : Fintype.card (GridIdx 4 8 → GF256) = 2 ^ 256 := by
  rw [Fintype.card_fun, card_gf256, card_gridIdx48]
  norm_num

/-! ### The linear layer as an additive bijection -/

/-- `MixColumns ∘ ShiftRows` of Rijndael-256 (offsets `0, 1, 3, 4`) as an additive bijection of
the state: the linear layer of `rijndael256LinSpec`. -/
noncomputable def rijndael256Lin : (GridIdx 4 8 → GF256) ≃+ (GridIdx 4 8 → GF256) :=
  linAddEquiv (linSpec_lin_add 8 shiftOff256 shiftOff256_injective) rijndael256LinSpec.lin_nondeg

theorem rijndael256Lin_apply (b : GridIdx 4 8 → GF256) :
    rijndael256Lin b = rijndael256LinSpec.lin b := rfl

/-- `rijndael256Lin` has branch number at least `5` over the whole state. -/
theorem rijndael256Lin_isBranchBound : isBranchBound id rijndael256Lin 5 :=
  fun a ha => rijndael256LinSpec_lin_isBranchBound a ha

/-- `aesLin`, `MixColumns ∘ ShiftRows` of AES, has branch number at least `5` over the whole
state: `lin_isBranchBound` at width `4` with offsets `0, 1, 2, 3`. -/
theorem aesLin_isBranchBound : isBranchBound id aesLin 5 :=
  fun a ha => lin_isBranchBound 4 id a ha

/-- A bricklayer of bijective S-boxes is bijective. -/
theorem bricklayer_bijective {Idx K : Type*} {s : Idx → K → K}
    (hs : ∀ i, Function.Bijective (s i)) : Function.Bijective (bricklayer s) :=
  Function.Bijective.piMap hs

/-! ### Trail probabilities -/

section Trail

variable {s : GridIdx 4 8 → GF256 → GF256}

/-- **Rijndael-256 at every round count: each trail has key-averaged probability at most
`2 ^ (-6 · (r / 4 · 25 + 5 · [2 ≤ r % 4]))`** in the independent-key model, for S-boxes that are
injective with differential uniformity at most `4`. -/
theorem rijndael256_rounds_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) (r : ℕ) :
    trailKeyCount rijndael256Lin (bricklayer s) r T x
        * 2 ^ (6 * (r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0)))
      ≤ (2 ^ 256) ^ r := by
  have h := trailKeyCount_le_of_spec rijndael256LinSpec (d := 6) hs hu aes_uniformity_clears
    (fun b => rijndael256Lin_apply b) (r := r) h0 x
  rwa [rijndael256LinSpec_fourRoundBound, rijndael256LinSpec_branch, card_state256] at h

/-- **Four rounds of Rijndael-256: each differential trail with a nonzero input difference
(`T 0 ≠ 0`) has probability at most `2⁻¹⁵⁰`, averaged over independent uniform round keys** (the
independent-key model), for injective S-boxes of differential uniformity at most `4`. At least
`25` active S-boxes, each charged `2⁻⁶`. -/
theorem rijndael256_four_round_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) :
    trailKeyCount rijndael256Lin (bricklayer s) 4 T x * 2 ^ 150 ≤ (2 ^ 256) ^ 4 := by
  have h := rijndael256_rounds_prob hs hu h0 x 4
  have he : 6 * (4 / 4 * 25 + (if 2 ≤ 4 % 4 then 5 else 0)) = 150 := by decide
  rwa [he] at h

/-- **Eight rounds of Rijndael-256: each differential trail with a nonzero input difference
(`T 0 ≠ 0`) has probability at most `2⁻³⁰⁰`** in the independent-key model, for injective S-boxes
of differential uniformity at most `4`. At least `50` active S-boxes, each charged `2⁻⁶`; eight
is the first round count at which the exponent of `rijndael256_rounds_prob` exceeds the block
length `256`. -/
theorem rijndael256_eight_round_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) :
    trailKeyCount rijndael256Lin (bricklayer s) 8 T x * 2 ^ 300 ≤ (2 ^ 256) ^ 8 := by
  have h := rijndael256_rounds_prob hs hu h0 x 8
  have he : 6 * (8 / 4 * 25 + (if 2 ≤ 8 % 4 then 5 else 0)) = 300 := by decide
  rwa [he] at h

/-- **Fourteen rounds of Rijndael-256: each differential trail with a nonzero input difference
(`T 0 ≠ 0`) has probability at most `2⁻⁴⁸⁰`** in the independent-key model, for injective S-boxes
of differential uniformity at most `4`. At least `80` active S-boxes, each charged `2⁻⁶`. Every
round of this statement includes `MixColumns`; `rijndael256_fourteen_round_prob_final` is the
form with the real last round. -/
theorem rijndael256_fourteen_round_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) :
    trailKeyCount rijndael256Lin (bricklayer s) 14 T x * 2 ^ 480 ≤ (2 ^ 256) ^ 14 := by
  have h := rijndael256_rounds_prob hs hu h0 x 14
  have he : 6 * (14 / 4 * 25 + (if 2 ≤ 14 % 4 then 5 else 0)) = 480 := by decide
  rwa [he] at h

end Trail

/-! ### Two-round differentials -/

/-- The arithmetic of the two-round bound at `|K| = 256`, uniformity `4` and branch number `5`:
`256⁴ = 2⁸ · 2²⁴` and `4⁴ = 2⁸`, so `D · 256⁴ ≤ 4⁴ · N` gives `D · 2²⁴ ≤ N`. -/
theorem mul_two_pow_24_le {D N : ℕ}
    (h : D * Fintype.card GF256 ^ (5 - 1) ≤ 4 ^ (5 - 1) * N) : D * 2 ^ 24 ≤ N := by
  rw [card_gf256] at h
  have e1 : (256 : ℕ) ^ (5 - 1) = 2 ^ 8 * 2 ^ 24 := by norm_num
  have e2 : (4 : ℕ) ^ (5 - 1) = 2 ^ 8 := by norm_num
  rw [e1, e2, mul_comm (2 ^ 8) (2 ^ 24), ← mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right (h.trans_eq (mul_comm _ _)) (by norm_num)

/-- **Rijndael-256: every two-round differential with a nonzero input difference has
probability at most `2⁻²⁴`, averaged over independent uniform round keys** (the independent-key
model), with the AES S-box in both rounds. This bounds the differential, the sum over all
two-round trails from `a` to `b`. The bound is coarse: it charges `4` of the at least `5` active
S-boxes at `2⁻⁶` each. For AES the exact maximum two-round expected differential probability,
averaged over independent round keys, is `53 / 2³⁴`, about `2^(-28.27)` (Keliher and Sui, ePrint
2005/321); no exact value for Rijndael-256 is used or claimed. -/
theorem rijndael256_two_round_differential {a : GridIdx 4 8 → GF256} (ha : a ≠ 0)
    (b x : GridIdx 4 8 → GF256) :
    Scheduled.diffKeyCount (fun _ => rijndael256Lin) (fun _ => bricklayer fun _ => AES.sbox)
        2 a b x * 2 ^ 24
      ≤ (2 ^ 256) ^ 2 := by
  have h := Scheduled.bricklayer_two_round_bound (fun _ => rijndael256Lin)
    (fun _ _ => AES.sbox) (fun _ _ _ => AES.sboxEquiv.bijective)
    (fun _ _ _ => AES.sbox_uniform) rijndael256Lin_isBranchBound ha b x
  rw [card_state256] at h
  exact mul_two_pow_24_le h

/-- **Rijndael-256 over `R ≥ 2` rounds: every differential with a nonzero input difference has
probability at most `2⁻²⁴`** in the independent-key model, with the AES S-box in every round,
`rijndael256Lin` in round `0`, and any additive bijections `lam n` in the other rounds (for
example the uniform schedule, or `lastRoundSchedule` with `ShiftRows` last). Only rounds `0` and
`1` are charged; the other rounds enter only through bijectivity. The bound is coarse, as in
`rijndael256_two_round_differential`. -/
theorem rijndael256_differential (lam : ℕ → (GridIdx 4 8 → GF256) ≃+ (GridIdx 4 8 → GF256))
    (hlam : lam 0 = rijndael256Lin) {R : ℕ} (hR : 2 ≤ R) {a : GridIdx 4 8 → GF256} (ha : a ≠ 0)
    (b x : GridIdx 4 8 → GF256) :
    Scheduled.diffKeyCount lam (fun _ => bricklayer fun _ => AES.sbox) R a b x * 2 ^ 24
      ≤ (2 ^ 256) ^ R := by
  have hB : isBranchBound id (lam 0) 5 := by
    rw [hlam]
    exact rijndael256Lin_isBranchBound
  have h := Scheduled.diffKeyCount_bound_of_two_rounds lam (fun _ => bricklayer fun _ => AES.sbox)
    (fun _ _ => AES.sbox) R 0 hR
    (fun _ _ => bricklayer_bijective fun _ => AES.sboxEquiv.bijective)
    (fun n _ _ => diffCount_bricklayer _) (fun _ _ _ _ => AES.sboxEquiv.bijective)
    (fun _ _ _ _ => AES.sbox_uniform) hB ha b x
  rw [card_state256] at h
  exact mul_two_pow_24_le h

/-- **AES-128: every two-round differential with a nonzero input difference has probability at
most `2⁻²⁴`, averaged over independent uniform round keys** (the independent-key model), with the
AES S-box in both rounds. The same coarse bound as `rijndael256_two_round_differential`: the
exact maximum two-round expected differential probability of AES, averaged over independent round
keys, is `53 / 2³⁴`, about `2^(-28.27)` (Keliher and Sui, ePrint 2005/321), below the bound
here. -/
theorem aes128_two_round_differential {a : SquareIdx 4 → GF256} (ha : a ≠ 0)
    (b x : SquareIdx 4 → GF256) :
    Scheduled.diffKeyCount (fun _ => aesLin) (fun _ => bricklayer fun _ => AES.sbox) 2 a b x
        * 2 ^ 24
      ≤ (2 ^ 128) ^ 2 := by
  have h := Scheduled.bricklayer_two_round_bound (fun _ => aesLin)
    (fun _ _ => AES.sbox) (fun _ _ _ => AES.sboxEquiv.bijective)
    (fun _ _ _ => AES.sbox_uniform) aesLin_isBranchBound ha b x
  rw [card_aesState] at h
  exact mul_two_pow_24_le h

/-- **AES over `R ≥ 2` rounds: every differential with a nonzero input difference has
probability at most `2⁻²⁴`** in the independent-key model, with the AES S-box in every round,
`aesLin` in round `0` and any additive bijections in the other rounds. Only rounds `0` and `1`
are charged. The bound is coarse, as in `aes128_two_round_differential`. -/
theorem aes128_differential (lam : ℕ → (SquareIdx 4 → GF256) ≃+ (SquareIdx 4 → GF256))
    (hlam : lam 0 = aesLin) {R : ℕ} (hR : 2 ≤ R) {a : SquareIdx 4 → GF256} (ha : a ≠ 0)
    (b x : SquareIdx 4 → GF256) :
    Scheduled.diffKeyCount lam (fun _ => bricklayer fun _ => AES.sbox) R a b x * 2 ^ 24
      ≤ (2 ^ 128) ^ R := by
  have hB : isBranchBound id (lam 0) 5 := by
    rw [hlam]
    exact aesLin_isBranchBound
  have h := Scheduled.diffKeyCount_bound_of_two_rounds lam (fun _ => bricklayer fun _ => AES.sbox)
    (fun _ _ => AES.sbox) R 0 hR
    (fun _ _ => bricklayer_bijective fun _ => AES.sboxEquiv.bijective)
    (fun n _ _ => diffCount_bricklayer _) (fun _ _ _ _ => AES.sboxEquiv.bijective)
    (fun _ _ _ _ => AES.sbox_uniform) hB ha b x
  rw [card_aesState] at h
  exact mul_two_pow_24_le h

/-! ### The final round -/

section LastRound

variable {X : Type*} [AddCommGroup X]

/-- The bundle permutation `p` acting on states, `transpose p`, as an additive bijection. -/
def transposeAddEquiv {Idx K : Type*} [AddCommGroup K] (p : Equiv.Perm Idx) :
    (Idx → K) ≃+ (Idx → K) where
  toFun := transpose p
  invFun := transpose p.symm
  left_inv a := funext fun i => by simp [transpose]
  right_inv a := funext fun i => by simp [transpose]
  map_add' _ _ := rfl

/-- `ShiftRows` of Rijndael-256 alone (offsets `0, 1, 3, 4`), without `MixColumns`: the linear
map of the cipher's last round. -/
def shiftRows256 : (GridIdx 4 8 → GF256) ≃+ (GridIdx 4 8 → GF256) :=
  transposeAddEquiv (shiftRowsPerm 4 8 shiftOff256)

/-- `ShiftRows` of AES alone (offsets `0, 1, 2, 3`), without `MixColumns`: the linear map of the
cipher's last round. -/
def aesShiftRows : (SquareIdx 4 → GF256) ≃+ (SquareIdx 4 → GF256) :=
  transposeAddEquiv (rowShiftPerm 4)

/-- The full linear layer of Rijndael-256 is `MixColumns` after `shiftRows256`: the last round
drops exactly `MixColumns`. -/
theorem rijndael256Lin_eq_mixColumns_shiftRows256 (b : GridIdx 4 8 → GF256) :
    rijndael256Lin b = mixColumns 8 (shiftRows256 b) := rfl

/-- The full linear layer of AES is `MixColumns` after `aesShiftRows`. -/
theorem aesLin_eq_aesMixColumns_aesShiftRows (b : SquareIdx 4 → GF256) :
    aesLin b = aesMixColumns (aesShiftRows b) := rfl

/-- The linear maps of an `R`-round schedule whose last round differs: `last` in round `R - 1`
and `lam` in every other round. -/
def lastRoundSchedule (lam last : X ≃+ X) (R : ℕ) : ℕ → X ≃+ X :=
  fun n => if n + 1 = R then last else lam

theorem lastRoundSchedule_of_ne {lam last : X ≃+ X} {R n : ℕ} (h : n + 1 ≠ R) :
    lastRoundSchedule lam last R n = lam := if_neg h

theorem lastRoundSchedule_last (lam last : X ≃+ X) (r : ℕ) :
    lastRoundSchedule lam last (r + 1) r = last := if_pos rfl

/-- The sequence `T` with its entry `R` replaced by `lam (last⁻¹ (T R))`: the difference that
round `R - 1` would output if its linear map were `lam` instead of `last`. -/
def relabelLast (lam last : X ≃+ X) (R : ℕ) (T : ℕ → X) : ℕ → X :=
  Function.update T R (lam (last.symm (T R)))

theorem relabelLast_of_ne (lam last : X ≃+ X) {R n : ℕ} (T : ℕ → X) (h : n ≠ R) :
    relabelLast lam last R T n = T n := Function.update_of_ne h _ _

/-- **A different last linear map only relabels the last difference.** In the independent-key
model, the number of key vectors under which the input pair `(x, x + T 0)` follows `T` through
`R ≥ 1` rounds with `lam` in rounds `0 … R - 2` and `last` in round `R - 1` equals the number for
the uniform schedule `lam` and the sequence `relabelLast lam last R T`, which agrees with `T`
except at index `R`. -/
theorem trailKeyCount_lastRoundSchedule [Fintype X] [DecidableEq X] (lam last : X ≃+ X)
    (γ : X → X) {R : ℕ} (hR : 0 < R) (T : ℕ → X) (x : X) :
    Scheduled.trailKeyCount (lastRoundSchedule lam last R) (fun _ => γ) R T x
      = trailKeyCount lam γ R (relabelLast lam last R T) x := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  rw [Scheduled.trailKeyCount_eq_prod, trailKeyCount_eq_prod, Finset.prod_range_succ,
    Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.mp hn
    rw [lastRoundSchedule_of_ne (by omega), relabelLast_of_ne lam last T (by omega),
      relabelLast_of_ne lam last T (by omega)]
  · rw [lastRoundSchedule_last, relabelLast_of_ne lam last T (by omega), relabelLast,
      Function.update_self, AddEquiv.symm_apply_apply]

theorem relabelLast_zero (lam last : X ≃+ X) {R : ℕ} (hR : 0 < R) (T : ℕ → X) :
    relabelLast lam last R T 0 = T 0 := relabelLast_of_ne lam last T (by omega)

end LastRound

section Final

variable {s : GridIdx 4 8 → GF256 → GF256}

/-- **Fourteen rounds of Rijndael-256 with the real last round: each differential trail with a
nonzero input difference (`T 0 ≠ 0`) has probability at most `2⁻⁴⁸⁰`, averaged over independent
uniform round keys** (the independent-key model), for injective S-boxes of differential
uniformity at most `4`. Rounds `0 … 12` apply `MixColumns ∘ ShiftRows` and round `13` applies
`ShiftRows` alone (`shiftRows256`); every round adds a key before its S-box layer. The count is
that of the uniform schedule on a sequence that differs from `T` only in its last entry
(`trailKeyCount_lastRoundSchedule`), so the at least `80` active S-boxes of rounds `0 … 13` are
charged as in `rijndael256_fourteen_round_prob`. -/
theorem rijndael256_fourteen_round_prob_final (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule rijndael256Lin shiftRows256 14)
        (fun _ => bricklayer s) 14 T x * 2 ^ 480
      ≤ (2 ^ 256) ^ 14 := by
  rw [trailKeyCount_lastRoundSchedule _ _ _ (by norm_num)]
  exact rijndael256_fourteen_round_prob hs hu
    (by rwa [relabelLast_zero _ _ (by norm_num)]) x

end Final

section AESFinal

variable {s : SquareIdx 4 → GF256 → GF256}

/-- **Ten rounds of AES-128 with the real last round: each differential trail with a nonzero
input difference (`T 0 ≠ 0`) has probability at most `2⁻³³⁰`, averaged over independent uniform
round keys** (the independent-key model), for injective S-boxes of differential uniformity at
most `4`. Rounds `0 … 8` apply `MixColumns ∘ ShiftRows` and round `9` applies `ShiftRows` alone
(`aesShiftRows`); the bound and the at least `55` active S-boxes are those of
`aes128_ten_round_prob`. -/
theorem aes128_ten_round_prob_final (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule aesLin aesShiftRows 10)
        (fun _ => bricklayer s) 10 T x * 2 ^ 330
      ≤ (2 ^ 128) ^ 10 := by
  rw [trailKeyCount_lastRoundSchedule _ _ _ (by norm_num), ← card_aesState]
  exact aes128_ten_round_prob hs hu (by rwa [relabelLast_zero _ _ (by norm_num)]) x

/-- **Twelve rounds of AES-192 with the real last round: each differential trail with a nonzero
input difference (`T 0 ≠ 0`) has probability at most `2⁻⁴⁵⁰`, averaged over independent uniform
round keys** (the independent-key model), for injective S-boxes of differential uniformity at
most `4`. Round `11` applies `ShiftRows` alone; the bound and the at least `75` active S-boxes are
those of `aes192_twelve_round_prob`. -/
theorem aes192_twelve_round_prob_final (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule aesLin aesShiftRows 12)
        (fun _ => bricklayer s) 12 T x * 2 ^ 450
      ≤ (2 ^ 128) ^ 12 := by
  rw [trailKeyCount_lastRoundSchedule _ _ _ (by norm_num), ← card_aesState]
  exact aes192_twelve_round_prob hs hu (by rwa [relabelLast_zero _ _ (by norm_num)]) x

/-- **Fourteen rounds of AES-256 with the real last round: each differential trail with a
nonzero input difference (`T 0 ≠ 0`) has probability at most `2⁻⁴⁸⁰`, averaged over independent
uniform round keys** (the independent-key model), for injective S-boxes of differential
uniformity at most `4`. Round `13` applies `ShiftRows` alone; the bound and the at least `80`
active S-boxes are those of `aes256_fourteen_round_prob`. -/
theorem aes256_fourteen_round_prob_final (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule aesLin aesShiftRows 14)
        (fun _ => bricklayer s) 14 T x * 2 ^ 480
      ≤ (2 ^ 128) ^ 14 := by
  rw [trailKeyCount_lastRoundSchedule _ _ _ (by norm_num), ← card_aesState]
  exact aes256_fourteen_round_prob hs hu (by rwa [relabelLast_zero _ _ (by norm_num)]) x

end AESFinal

/-! ### With the AES S-box

The bounds above for `s = fun _ => AES.sbox`, whose injectivity and uniformity `4` are proved
(`AES.sbox_injective`, `AES.sbox_uniform`). Still in the independent-key model. -/

/-- Four rounds of Rijndael-256 with the AES S-box: each trail with `T 0 ≠ 0` has probability
at most `2⁻¹⁵⁰`, averaged over independent uniform round keys (the independent-key model). -/
theorem rijndael256_four_round_probability {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) :
    trailKeyCount rijndael256Lin (bricklayer fun _ => AES.sbox) 4 T x * 2 ^ 150
      ≤ (2 ^ 256) ^ 4 :=
  rijndael256_four_round_prob (fun _ => AES.sbox_injective) (fun _ => AES.sbox_uniform) h0 x

/-- Eight rounds of Rijndael-256 with the AES S-box: each trail with `T 0 ≠ 0` has probability
at most `2⁻³⁰⁰`, averaged over independent uniform round keys (the independent-key model). -/
theorem rijndael256_eight_round_probability {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) :
    trailKeyCount rijndael256Lin (bricklayer fun _ => AES.sbox) 8 T x * 2 ^ 300
      ≤ (2 ^ 256) ^ 8 :=
  rijndael256_eight_round_prob (fun _ => AES.sbox_injective) (fun _ => AES.sbox_uniform) h0 x

/-- Fourteen rounds of Rijndael-256 with the AES S-box: each trail with `T 0 ≠ 0` has
probability at most `2⁻⁴⁸⁰`, averaged over independent uniform round keys (the independent-key
model). -/
theorem rijndael256_fourteen_round_probability {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0)
    (x : GridIdx 4 8 → GF256) :
    trailKeyCount rijndael256Lin (bricklayer fun _ => AES.sbox) 14 T x * 2 ^ 480
      ≤ (2 ^ 256) ^ 14 :=
  rijndael256_fourteen_round_prob (fun _ => AES.sbox_injective) (fun _ => AES.sbox_uniform) h0 x

/-- Fourteen rounds of Rijndael-256 with the AES S-box and `ShiftRows` alone in the last round:
each trail with `T 0 ≠ 0` has probability at most `2⁻⁴⁸⁰`, averaged over independent uniform round
keys (the independent-key model). -/
theorem rijndael256_fourteen_round_probability_final {T : ℕ → GridIdx 4 8 → GF256}
    (h0 : T 0 ≠ 0) (x : GridIdx 4 8 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule rijndael256Lin shiftRows256 14)
        (fun _ => bricklayer fun _ => AES.sbox) 14 T x * 2 ^ 480
      ≤ (2 ^ 256) ^ 14 :=
  rijndael256_fourteen_round_prob_final (fun _ => AES.sbox_injective)
    (fun _ => AES.sbox_uniform) h0 x

/-- AES-128 with the AES S-box and `ShiftRows` alone in the last round: each ten-round trail with
`T 0 ≠ 0` has probability at most `2⁻³³⁰`, averaged over independent uniform round keys (the
independent-key model). -/
theorem aes128_ten_round_probability_final {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule aesLin aesShiftRows 10)
        (fun _ => bricklayer fun _ => AES.sbox) 10 T x * 2 ^ 330
      ≤ (2 ^ 128) ^ 10 :=
  aes128_ten_round_prob_final (fun _ => AES.sbox_injective) (fun _ => AES.sbox_uniform) h0 x

/-- AES-192 with the AES S-box and `ShiftRows` alone in the last round: each twelve-round trail
with `T 0 ≠ 0` has probability at most `2⁻⁴⁵⁰`, averaged over independent uniform round keys (the
independent-key model). -/
theorem aes192_twelve_round_probability_final {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule aesLin aesShiftRows 12)
        (fun _ => bricklayer fun _ => AES.sbox) 12 T x * 2 ^ 450
      ≤ (2 ^ 128) ^ 12 :=
  aes192_twelve_round_prob_final (fun _ => AES.sbox_injective) (fun _ => AES.sbox_uniform) h0 x

/-- AES-256 with the AES S-box and `ShiftRows` alone in the last round: each fourteen-round trail
with `T 0 ≠ 0` has probability at most `2⁻⁴⁸⁰`, averaged over independent uniform round keys (the
independent-key model). -/
theorem aes256_fourteen_round_probability_final {T : ℕ → SquareIdx 4 → GF256} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    Scheduled.trailKeyCount (lastRoundSchedule aesLin aesShiftRows 14)
        (fun _ => bricklayer fun _ => AES.sbox) 14 T x * 2 ^ 480
      ≤ (2 ^ 128) ^ 14 :=
  aes256_fourteen_round_prob_final (fun _ => AES.sbox_injective) (fun _ => AES.sbox_uniform) h0 x

end Rijndael
