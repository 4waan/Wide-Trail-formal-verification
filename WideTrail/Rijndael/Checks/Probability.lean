/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Rijndael.Probability
import WideTrail.Rijndael.Checks.MixColumns

/-!
# Checks for the Rijndael-256 and AES probability bounds

Controls for `Rijndael/Probability.lean`. All counts are in the independent-key model of that
file.

* `exponent_seven_fails`: `4 · 2⁷ = 512 > 256`, so the hypothesis `u · 2 ^ d ≤ |K|` of
  `trailKeyCount_le_of_spec` fails at `u = 4`, `d = 7`. `sbox_diff_clears_iff`: a differential
  uniformity bound `u` of the AES S-box with `u · 2 ^ d ≤ 256` exists exactly when `d ≤ 6`,
  because the S-box attains uniformity `4` (`AES.sbox_uniformity_witness`,
  `sbox_uniformity_ge`). So the per-S-box exponent `6` behind `150`, `300` and `480` cannot be
  raised to `7` by this argument (`not_exists_sbox_diff_clears_seven`).
* `trailExponent_le_of_lt_eight`, `trailExponent_eight`: the exponent
  `6 · (r / 4 · 25 + 5 · [2 ≤ r % 4])` of `rijndael256_rounds_prob` is at most `256` for
  `r < 8` and is `300` at `r = 8`, so eight is the first round count at which it exceeds the
  block length. `trailExponent_values` gives `150`, `300` and `480` at `4`, `8` and `14`.
  `rounds_prob_trailExponent` restates `rijndael256_rounds_prob` with `trailExponent r` as its
  exponent, so these checks are about the exponent the theorem proves.
* `trailKeyCount_zero_seq`, `four_round_prob_needs_h0`, `final_prob_needs_h0`: the zero sequence
  is followed under every key vector, so its count is `(2 ^ 256) ^ 4` over four rounds and
  `(2 ^ 256) ^ 14` over the fourteen rounds of the final-round schedule, and the hypothesis
  `T 0 ≠ 0` of `rijndael256_four_round_probability` and of
  `rijndael256_fourteen_round_probability_final` is needed.
* `diffKeyCount_zero_zero`, `two_round_differential_needs_ha`: the differential `(0, 0)` has
  count `(2 ^ 256) ^ 2`, so the hypothesis `a ≠ 0` of `rijndael256_two_round_differential` is
  needed.
* `final_schedule_of_lt`, `final_schedule_last_ne`: in the schedule of
  `rijndael256_fourteen_round_prob_final`, rounds `0 … 12` use `rijndael256Lin` and round `13`
  does not: on one active byte, `shiftRows256` gives one active byte
  (`weight_shiftRows256_e30`) and `rijndael256Lin` gives four.
* `medp_between`, `medp_below_coarse`: arithmetic on the cited value `53 / 2³⁴` of the AES
  two-round MEDP (Keliher and Sui, ePrint 2005/321): `2⁻²⁹ < 53 / 2³⁴ ≤ 2⁻²⁸`, and the bound
  `2⁻²⁴` of `aes128_two_round_differential` exceeds it by more than a factor `2⁴`.

## What is not claimed

These are checks of hypotheses and of single values. They do not show that any bound of
`Rijndael/Probability.lean` is attained, they compute no differential probability of the cipher,
and `medp_between` only checks arithmetic on a value cited from the literature; nothing here
computes a MEDP.
-/

set_option autoImplicit false
set_option exponentiation.threshold 4000

namespace Rijndael.Checks

/-! ### The exponent `6` per active S-box -/

/-- **`4 · 2⁷ > 256`**: uniformity `4` does not clear `2⁷` per active S-box. -/
theorem exponent_seven_fails : ¬ 4 * 2 ^ 7 ≤ Fintype.card GF256 := by
  rw [card_gf256]
  norm_num

/-- Every differential uniformity bound of the AES S-box is at least `4`: the differential
`(01, 1f)` has count `4` (`AES.sbox_uniformity_witness`). -/
theorem sbox_uniformity_ge (u : ℕ) (hu : IsDiffUniform AES.sbox u) : 4 ≤ u := by
  have h := hu ⟨1#8⟩ (by decide +kernel) ⟨0x1f#8⟩
  rwa [AES.sbox_uniformity_witness] at h

/-- **A differential uniformity bound of the AES S-box clears `2 ^ d` exactly when `d ≤ 6`**:
there is a `u` with `IsDiffUniform AES.sbox u` and `u · 2 ^ d ≤ |GF256|` if and only if
`d ≤ 6`. -/
theorem sbox_diff_clears_iff (d : ℕ) :
    (∃ u, IsDiffUniform AES.sbox u ∧ u * 2 ^ d ≤ Fintype.card GF256) ↔ d ≤ 6 := by
  rw [card_gf256]
  constructor
  · rintro ⟨u, hu, hd⟩
    have h4 := sbox_uniformity_ge u hu
    by_contra h
    have h7 : 2 ^ 7 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h512 : 4 * 2 ^ 7 ≤ u * 2 ^ d := Nat.mul_le_mul h4 h7
    norm_num at h512
    omega
  · intro hd
    refine ⟨4, AES.sbox_uniform, ?_⟩
    calc 4 * 2 ^ d ≤ 4 * 2 ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hd)
      _ = 256 := by norm_num

/-- **`d = 7` fails**: no differential uniformity bound `u` of the AES S-box has
`u · 2⁷ ≤ |GF256|`. -/
theorem not_exists_sbox_diff_clears_seven :
    ¬ ∃ u, IsDiffUniform AES.sbox u ∧ u * 2 ^ 7 ≤ Fintype.card GF256 := fun h =>
  absurd ((sbox_diff_clears_iff 7).mp h) (by decide)

/-! ### The exponents at each round count -/

/-- The exponent of `rijndael256_rounds_prob` at `r` rounds. -/
def trailExponent (r : ℕ) : ℕ := 6 * (r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0))

theorem trailExponent_values :
    trailExponent 4 = 150 ∧ trailExponent 8 = 300 ∧ trailExponent 14 = 480 := by decide

/-- Below eight rounds the exponent is at most the block length `256`. -/
theorem trailExponent_le_of_lt_eight : ∀ r < 8, trailExponent r ≤ 256 := by decide

/-- At eight rounds it is `300 > 256`. -/
theorem trailExponent_eight : 256 < trailExponent 8 := by decide

/-- **`rijndael256_rounds_prob` with the exponent `trailExponent r`**: `trailExponent` is the
exponent of that theorem, so the values above are the exponents it proves. In the
independent-key model, for injective S-boxes of differential uniformity at most `4` and
`T 0 ≠ 0`. -/
theorem rounds_prob_trailExponent {s : GridIdx 4 8 → GF256 → GF256}
    (hs : ∀ i, Function.Injective (s i)) (hu : ∀ i, IsDiffUniform (s i) 4)
    {T : ℕ → GridIdx 4 8 → GF256} (h0 : T 0 ≠ 0) (x : GridIdx 4 8 → GF256) (r : ℕ) :
    trailKeyCount rijndael256Lin (bricklayer s) r T x * 2 ^ trailExponent r ≤ (2 ^ 256) ^ r :=
  rijndael256_rounds_prob hs hu h0 x r

/-! ### The hypotheses `T 0 ≠ 0` and `a ≠ 0` are needed -/

section Zero

variable {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]

/-- The zero sequence is followed under every key vector: its count is `|X| ^ r`. -/
theorem trailKeyCount_zero_seq (lam : X ≃+ X) (γ : X → X) (r : ℕ) {T : ℕ → X}
    (hT : ∀ n, T n = 0) (x : X) : trailKeyCount lam γ r T x = Fintype.card X ^ r := by
  rw [trailKeyCount_eq_prod]
  simp [hT, diffCount_zero_left]

/-- The differential `(0, 0)` holds under every key vector: its count is `|X| ^ r`. -/
theorem diffKeyCount_zero_zero (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ) {a b : X}
    (ha : a = 0) (hb : b = 0) (x : X) :
    Scheduled.diffKeyCount lam γ r a b x = Fintype.card X ^ r := by
  subst ha hb
  simp [Scheduled.diffKeyCount]

end Zero

/-- **The hypothesis `T 0 ≠ 0` of `rijndael256_four_round_probability` is needed**: for the zero
sequence the count is `(2 ^ 256) ^ 4`. -/
theorem four_round_prob_needs_h0 :
    ¬ ∀ (T : ℕ → GridIdx 4 8 → GF256) (x : GridIdx 4 8 → GF256),
      trailKeyCount rijndael256Lin (bricklayer fun _ => AES.sbox) 4 T x * 2 ^ 150
        ≤ (2 ^ 256) ^ 4 := fun h => by
  have h' := h (fun _ => 0) 0
  have e : trailKeyCount rijndael256Lin (bricklayer fun _ => AES.sbox) 4 (fun _ => 0) 0
      = Fintype.card (GridIdx 4 8 → GF256) ^ 4 :=
    trailKeyCount_zero_seq _ _ _ (fun _ => rfl) _
  rw [e, card_state256] at h'
  exact absurd h' (by decide +kernel)

/-- **The hypothesis `a ≠ 0` of `rijndael256_two_round_differential` is needed**: the
differential `(0, 0)` has count `(2 ^ 256) ^ 2`. -/
theorem two_round_differential_needs_ha :
    ¬ ∀ a b x : GridIdx 4 8 → GF256,
      Scheduled.diffKeyCount (fun _ => rijndael256Lin) (fun _ => bricklayer fun _ => AES.sbox)
          2 a b x * 2 ^ 24
        ≤ (2 ^ 256) ^ 2 := fun h => by
  have h' := h 0 0 0
  rw [diffKeyCount_zero_zero _ _ _ (a := (0 : GridIdx 4 8 → GF256))
    (b := (0 : GridIdx 4 8 → GF256)) rfl rfl, card_state256] at h'
  exact absurd h' (by decide +kernel)

/-- **The hypothesis `T 0 ≠ 0` of `rijndael256_fourteen_round_probability_final` is needed**: in
the final-round schedule the zero sequence relabels to itself (`relabelLast`), so its count is
`(2 ^ 256) ^ 14`. -/
theorem final_prob_needs_h0 :
    ¬ ∀ (T : ℕ → GridIdx 4 8 → GF256) (x : GridIdx 4 8 → GF256),
      Scheduled.trailKeyCount (lastRoundSchedule rijndael256Lin shiftRows256 14)
          (fun _ => bricklayer fun _ => AES.sbox) 14 T x * 2 ^ 480
        ≤ (2 ^ 256) ^ 14 := fun h => by
  have h' := h (fun _ => 0) 0
  have e1 := trailKeyCount_lastRoundSchedule rijndael256Lin shiftRows256
    (bricklayer fun _ => AES.sbox) (R := 14) (by decide) (fun _ => 0) 0
  have e : relabelLast rijndael256Lin shiftRows256 14 (fun _ => 0) = fun _ => 0 := by
    funext n
    by_cases hn : n = 14
    · subst hn
      rw [relabelLast, Function.update_self, map_zero, map_zero]
    · exact relabelLast_of_ne _ _ _ hn
  have e2 : trailKeyCount rijndael256Lin (bricklayer fun _ => AES.sbox) 14
      (fun _ => (0 : GridIdx 4 8 → GF256)) 0 = Fintype.card (GridIdx 4 8 → GF256) ^ 14 :=
    trailKeyCount_zero_seq _ _ _ (fun _ => rfl) _
  have e3 : Scheduled.trailKeyCount (lastRoundSchedule rijndael256Lin shiftRows256 14)
      (fun _ => bricklayer fun _ => AES.sbox) 14 (fun _ => 0) 0 = (2 ^ 256) ^ 14 := by
    rw [e1, e, e2, card_state256]
  rw [e3] at h'
  exact absurd h' (by decide +kernel)

/-! ### The last round of the final-round schedule -/

/-- Rounds `0 … 12` of the schedule of `rijndael256_fourteen_round_prob_final` use the full
linear layer. -/
theorem final_schedule_of_lt (n : ℕ) (hn : n < 13) :
    lastRoundSchedule rijndael256Lin shiftRows256 14 n = rijndael256Lin :=
  lastRoundSchedule_of_ne (by omega)

/-- `ShiftRows` alone keeps one active byte alone. -/
theorem weight_shiftRows256_e30 : weight (shiftRows256 e30) = 1 := by decide +kernel

/-- **Round `13` of that schedule is not `rijndael256Lin`**: on one active byte, `shiftRows256`
gives one active byte and `rijndael256Lin` gives four (`weight_rijndael256Lin_e30`). -/
theorem final_schedule_last_ne :
    lastRoundSchedule rijndael256Lin shiftRows256 14 13 ≠ rijndael256Lin := by
  intro h
  have hl : lastRoundSchedule rijndael256Lin shiftRows256 14 13 = shiftRows256 := if_pos rfl
  rw [hl] at h
  have hw : weight (shiftRows256 e30) = weight (rijndael256Lin e30) := by rw [h]
  rw [weight_shiftRows256_e30, rijndael256Lin_apply, weight_rijndael256Lin_e30] at hw
  omega

/-! ### The cited two-round value -/

/-- `2⁻²⁹ < 53 / 2³⁴ ≤ 2⁻²⁸`, in integers: `2²⁸ · 53 ≤ 2³⁴ < 2²⁹ · 53`. -/
theorem medp_between : 2 ^ 28 * 53 ≤ 2 ^ 34 ∧ 2 ^ 34 < 2 ^ 29 * 53 := by norm_num

/-- `2⁴ · 53 / 2³⁴ < 2⁻²⁴`, in integers: the coarse bound exceeds the cited value by more than a
factor `2⁴`. -/
theorem medp_below_coarse : 2 ^ 4 * (53 * 2 ^ 24) < 2 ^ 34 := by norm_num

end Rijndael.Checks
