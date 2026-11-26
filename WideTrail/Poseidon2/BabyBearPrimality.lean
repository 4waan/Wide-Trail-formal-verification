/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-!
# Primality of the BabyBear modulus

The BabyBear prime is `P = 0x78000001 = 2013265921 = 2^31 - 2^27 + 1` (`p3-baby-bear`
`0.2.3-succinct` `src/baby_bear.rs:16`), the field of SP1 `5.2.4` (`sp1-primitives` `5.2.4`
`src/lib.rs:5`). This file proves `Nat.Prime 2013265921` by a kernel-checked Lucas
certificate, in the style of `WideTrail.Poseidon2.BN254Primality`.

`P - 1 = 2^27 * 3 * 5`, and the witness is `31`, which has order exactly `P - 1` modulo `P`:
`31^(P - 1) = 1`, and `31^((P - 1) / q) ≠ 1` for `q = 2, 3, 5`. The prime factors `2`, `3`, `5`
are certified by `norm_num`. The witness `31` is also the multiplicative generator the code
declares (`p3-baby-bear` `src/baby_bear.rs:170-172`, `from_canonical_u32(0x1f)`); only the
order computation above is used here, not that declaration.

What is not claimed: nothing beyond the primality of this one integer.
-/

set_option autoImplicit false

namespace Poseidon2.BabyBear

/-- **The BabyBear modulus `2013265921 = 2^31 - 2^27 + 1` is prime.** Lucas certificate with
witness `31` and `P - 1 = 2^27 * 3 * 5`. -/
theorem prime_2013265921 : Nat.Prime 2013265921 := by
  refine lucas_primality 2013265921 (31 : ZMod 2013265921) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2013265921 - 1 = 2 ^ 27 * 3 ^ 1 * 5 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 27 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 27) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd5, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

end Poseidon2.BabyBear
