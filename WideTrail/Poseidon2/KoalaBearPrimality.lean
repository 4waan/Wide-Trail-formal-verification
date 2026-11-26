/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-!
# A Lucas certificate for the KoalaBear prime

The KoalaBear prime is `p = 2130706433 = 0x7f000001 = 2^31 - 2^24 + 1` (`p3-koala-bear`
`0.4.3-succinct` `src/koala_bear.rs:19`; `slop-koala-bear` `6.10.0` pins that version in its
`Cargo.toml:41-42`). This file proves `Nat.Prime 2130706433` by Lucas' test
(`lucas_primality`):

* `p - 1 = 2^24 * 127`, and the witness is `3`, which is also Plonky3's `generator()` for this
  field (`src/koala_bear.rs:175-177`);
* `3^(p - 1) = 1`, `3^((p - 1) / 2) = p - 1` and `3^((p - 1) / 127) = 1828256994` in `ZMod p`,
  so `3` has order exactly `p - 1`;
* the factor `127` is certified the same way (`126 = 2 * 3^2 * 7`, witness `3`), and `2`, `3`,
  `7` by `norm_num`.

The modular powers are evaluated by `reduce_mod_char`, the remaining comparisons by `decide`.
Nothing beyond primality is claimed here.
-/

set_option autoImplicit false

namespace Poseidon2.KoalaBear

/-- `127` is prime: `126 = 2 * 3^2 * 7`, witness `3`. -/
theorem prime_127 : Nat.Prime 127 := by
  refine lucas_primality 127 (3 : ZMod 127) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 127 - 1 = 2 ^ 1 * 3 ^ 2 * 7 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 2 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 2) 3 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 1 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 1) 7 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd7, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

/-- **The KoalaBear prime.** `2130706433 - 1 = 2^24 * 127`, witness `3`. -/
theorem prime_2130706433 : Nat.Prime 2130706433 := by
  refine lucas_primality 2130706433 (3 : ZMod 2130706433) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2130706433 - 1 = 2 ^ 24 * 127 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 24 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 24) 2 (by decide)⟩
    have hd127 : q ∣ 127 ^ 1 ↔ q = 127 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_127,
        fun h => by subst q; exact dvd_pow_self (n := 1) 127 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd127] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

end Poseidon2.KoalaBear
