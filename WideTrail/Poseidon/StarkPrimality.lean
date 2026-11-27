/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-!
# The STARK field and its primality certificate

The field of Starknet's Poseidon permutation is `ZMod p` for the STARK prime
`p = 2^251 + 17 * 2^192 + 1`
`= 3618502788666131213697322783095070105623107215331596699973092056135872020481`
(`0x800000000000011000000000000000000000000000000000000000000000001`, `252` bits). It is
`DEFAULT_PRIME` of starkware-libs/cairo-lang tag `v0.14.0.1` (commit
`66355d7d99f1962ff9ccba8d0dbacbce3bd79bf8`), `src/starkware/cairo/lang/cairo_constants.py:1`,
which `PoseidonParams.get_default_poseidon_params` passes as `field_prime`
(`src/starkware/cairo/common/poseidon_utils.py:116`).

## Results

* `modulus_eq`: `modulus = 2^251 + 17 * 2^192 + 1`.
* `modulus_sub_one_eq`: `modulus - 1 = 2^192 * 5 * 7 * 98714381 * 166848103`.
* `StarkPrimality.prime_3618…481`: `modulus` is prime, by a Lucas certificate with witness `3`
  (`lucas_primality`). The factors `98714381` and `166848103` of `p - 1` and the primes below
  them carry their own Lucas certificates (`prime_211`, `prime_829`, `prime_8291`,
  `prime_1233929`, `prime_2467859`, `prime_4935719`, `prime_9269339`, `prime_98714381`,
  `prime_166848103`); primes below `100` are proved by `norm_num`. The deepest chain is
  `98714381 → 4935719 → 2467859 → 1233929 → {17, 43, 211}`. The witnesses and factorisations
  were computed outside Lean; every check is done by the kernel (`reduce_mod_char`, `decide`).
* The global instance `Fact (Nat.Prime modulus)`, so that `F = ZMod modulus` is a field, and
  `field_card : Fintype.card F = modulus`.

## What is not claimed

This file proves that the modulus is prime and nothing else about the field. It says nothing
about how the implementations represent field elements (several use a Montgomery form with
`R = 2^256` internally).
-/

set_option autoImplicit false

namespace Poseidon.StarkPrimality

set_option maxRecDepth 8000

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_211 : Nat.Prime 211 := by
  refine lucas_primality 211 (2 : ZMod 211) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 211 - 1 = 2 ^ 1 * 3 ^ 1 * 5 ^ 1 * 7 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 1 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 1) 7 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd5, hd7, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_1233929 : Nat.Prime 1233929 := by
  refine lucas_primality 1233929 (6 : ZMod 1233929) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1233929 - 1 = 2 ^ 3 * 17 ^ 1 * 43 ^ 1 * 211 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 3 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 3) 2 (by decide)⟩
    have hp17 : Nat.Prime 17 := by norm_num
    have hd17 : q ∣ 17 ^ 1 ↔ q = 17 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp17,
        fun h => by subst q; exact dvd_pow_self (n := 1) 17 (by decide)⟩
    have hp43 : Nat.Prime 43 := by norm_num
    have hd43 : q ∣ 43 ^ 1 ↔ q = 43 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp43,
        fun h => by subst q; exact dvd_pow_self (n := 1) 43 (by decide)⟩
    have hd211 : q ∣ 211 ^ 1 ↔ q = 211 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_211,
        fun h => by subst q; exact dvd_pow_self (n := 1) 211 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd17, hd43, hd211, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_2467859 : Nat.Prime 2467859 := by
  refine lucas_primality 2467859 (2 : ZMod 2467859) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 2467859 - 1 = 2 ^ 1 * 1233929 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hd1233929 : q ∣ 1233929 ^ 1 ↔ q = 1233929 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_1233929,
        fun h => by subst q; exact dvd_pow_self (n := 1) 1233929 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd1233929] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_4935719 : Nat.Prime 4935719 := by
  refine lucas_primality 4935719 (17 : ZMod 4935719) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4935719 - 1 = 2 ^ 1 * 2467859 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hd2467859 : q ∣ 2467859 ^ 1 ↔ q = 2467859 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_2467859,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2467859 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd2467859] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_98714381 : Nat.Prime 98714381 := by
  refine lucas_primality 98714381 (2 : ZMod 98714381) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 98714381 - 1 = 2 ^ 2 * 5 ^ 1 * 4935719 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hd4935719 : q ∣ 4935719 ^ 1 ↔ q = 4935719 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_4935719,
        fun h => by subst q; exact dvd_pow_self (n := 1) 4935719 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd5, hd4935719, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_829 : Nat.Prime 829 := by
  refine lucas_primality 829 (2 : ZMod 829) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 829 - 1 = 2 ^ 2 * 3 ^ 2 * 23 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 2 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 2) 3 (by decide)⟩
    have hp23 : Nat.Prime 23 := by norm_num
    have hd23 : q ∣ 23 ^ 1 ↔ q = 23 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp23,
        fun h => by subst q; exact dvd_pow_self (n := 1) 23 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd23, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_8291 : Nat.Prime 8291 := by
  refine lucas_primality 8291 (2 : ZMod 8291) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 8291 - 1 = 2 ^ 1 * 5 ^ 1 * 829 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hd829 : q ∣ 829 ^ 1 ↔ q = 829 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_829,
        fun h => by subst q; exact dvd_pow_self (n := 1) 829 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd5, hd829, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_9269339 : Nat.Prime 9269339 := by
  refine lucas_primality 9269339 (6 : ZMod 9269339) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 9269339 - 1 = 2 ^ 1 * 13 ^ 1 * 43 ^ 1 * 8291 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp13 : Nat.Prime 13 := by norm_num
    have hd13 : q ∣ 13 ^ 1 ↔ q = 13 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp13,
        fun h => by subst q; exact dvd_pow_self (n := 1) 13 (by decide)⟩
    have hp43 : Nat.Prime 43 := by norm_num
    have hd43 : q ∣ 43 ^ 1 ↔ q = 43 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp43,
        fun h => by subst q; exact dvd_pow_self (n := 1) 43 (by decide)⟩
    have hd8291 : q ∣ 8291 ^ 1 ↔ q = 8291 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_8291,
        fun h => by subst q; exact dvd_pow_self (n := 1) 8291 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd13, hd43, hd8291, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_166848103 : Nat.Prime 166848103 := by
  refine lucas_primality 166848103 (6 : ZMod 166848103) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 166848103 - 1 = 2 ^ 1 * 3 ^ 2 * 9269339 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 2 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 2) 3 (by decide)⟩
    have hd9269339 : q ∣ 9269339 ^ 1 ↔ q = 9269339 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_9269339,
        fun h => by subst q; exact dvd_pow_self (n := 1) 9269339 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd9269339, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_3618502788666131213697322783095070105623107215331596699973092056135872020481 :
    Nat.Prime 3618502788666131213697322783095070105623107215331596699973092056135872020481 := by
  refine lucas_primality
    3618502788666131213697322783095070105623107215331596699973092056135872020481 (3 : ZMod
    3618502788666131213697322783095070105623107215331596699973092056135872020481) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3618502788666131213697322783095070105623107215331596699973092056135872020481 - 1 =
      2 ^ 192 * 5 ^ 1 * 7 ^ 1 * 98714381 ^ 1 * 166848103 ^ 1 := by
      decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 192 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 192) 2 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 1 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 1) 7 (by decide)⟩
    have hd98714381 : q ∣ 98714381 ^ 1 ↔ q = 98714381 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_98714381,
        fun h => by subst q; exact dvd_pow_self (n := 1) 98714381 (by decide)⟩
    have hd166848103 : q ∣ 166848103 ^ 1 ↔ q = 166848103 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_166848103,
        fun h => by subst q; exact dvd_pow_self (n := 1) 166848103 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd5, hd7, hd98714381, hd166848103, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide
end Poseidon.StarkPrimality

namespace Poseidon.Starknet

/-- **The STARK prime** `p = 2^251 + 17 * 2^192 + 1`, `DEFAULT_PRIME` of cairo-lang `v0.14.0.1`
(commit `66355d7d99f1962ff9ccba8d0dbacbce3bd79bf8`)
`src/starkware/cairo/lang/cairo_constants.py:1`, the `field_prime` of the default Poseidon
parameters (`src/starkware/cairo/common/poseidon_utils.py:116`). The same modulus is `F251` of
CryptoExperts/poseidon commit `68a88df9cb894fe1e0ee8b1b1b5825602c83635a`
`sage/poseidon.sage:7` and the `Stark252PrimeField` of lambdaworks-crypto `0.13.0`
(`src/hash/poseidon/starknet/parameters.rs:7`). -/
def modulus : Nat :=
  3618502788666131213697322783095070105623107215331596699973092056135872020481

/-- The modulus in the form `2^251 + 17 * 2^192 + 1` of `cairo_constants.py:1`. -/
theorem modulus_eq : modulus = 2 ^ 251 + 17 * 2 ^ 192 + 1 := by decide

/-- The factorisation of `p - 1` used by the Lucas certificate. -/
theorem modulus_sub_one_eq : modulus - 1 = 2 ^ 192 * 5 * 7 * 98714381 * 166848103 := by decide

/-- **The modulus is prime**, by the Lucas certificate above. -/
theorem modulus_prime : Nat.Prime modulus :=
  StarkPrimality.prime_3618502788666131213697322783095070105623107215331596699973092056135872020481

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- The STARK field `ZMod p`. -/
abbrev F := ZMod modulus

theorem field_card : Fintype.card F = modulus := ZMod.card modulus

end Poseidon.Starknet
