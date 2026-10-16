import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! Kernel-checked Lucas certificates for the BN254 scalar-field modulus. -/

namespace Poseidon2.Primality

set_option maxRecDepth 8000

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_107 : Nat.Prime 107 := by
  refine lucas_primality 107 (2 : ZMod 107) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 107 - 1 = 2 ^ 1 * 53 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp53 : Nat.Prime 53 := by norm_num
    have hd53 : q ∣ 53 ^ 1 ↔ q = 53 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp53,
        fun h => by subst q; exact dvd_pow_self (n := 1) 53 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd53] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_137 : Nat.Prime 137 := by
  refine lucas_primality 137 (3 : ZMod 137) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 137 - 1 = 2 ^ 3 * 17 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 3 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 3) 2 (by decide)⟩
    have hp17 : Nat.Prime 17 := by norm_num
    have hd17 : q ∣ 17 ^ 1 ↔ q = 17 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp17,
        fun h => by subst q; exact dvd_pow_self (n := 1) 17 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd17] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_223 : Nat.Prime 223 := by
  refine lucas_primality 223 (3 : ZMod 223) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 223 - 1 = 2 ^ 1 * 3 ^ 1 * 37 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp37 : Nat.Prime 37 := by norm_num
    have hd37 : q ∣ 37 ^ 1 ↔ q = 37 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp37,
        fun h => by subst q; exact dvd_pow_self (n := 1) 37 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd37, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_229 : Nat.Prime 229 := by
  refine lucas_primality 229 (6 : ZMod 229) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 229 - 1 = 2 ^ 2 * 3 ^ 1 * 19 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp19 : Nat.Prime 19 := by norm_num
    have hd19 : q ∣ 19 ^ 1 ↔ q = 19 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp19,
        fun h => by subst q; exact dvd_pow_self (n := 1) 19 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd19, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_379 : Nat.Prime 379 := by
  refine lucas_primality 379 (2 : ZMod 379) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 379 - 1 = 2 ^ 1 * 3 ^ 3 * 7 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 3 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 3) 3 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 1 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 1) 7 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd7, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_409 : Nat.Prime 409 := by
  refine lucas_primality 409 (21 : ZMod 409) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 409 - 1 = 2 ^ 3 * 3 ^ 1 * 17 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 3 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 3) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp17 : Nat.Prime 17 := by norm_num
    have hd17 : q ∣ 17 ^ 1 ↔ q = 17 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp17,
        fun h => by subst q; exact dvd_pow_self (n := 1) 17 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd17, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_449 : Nat.Prime 449 := by
  refine lucas_primality 449 (3 : ZMod 449) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 449 - 1 = 2 ^ 6 * 7 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 6 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 6) 2 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 1 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 1) 7 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd7] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_491 : Nat.Prime 491 := by
  refine lucas_primality 491 (2 : ZMod 491) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 491 - 1 = 2 ^ 1 * 5 ^ 1 * 7 ^ 2 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 2 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 2) 7 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd5, hd7, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_661 : Nat.Prime 661 := by
  refine lucas_primality 661 (2 : ZMod 661) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 661 - 1 = 2 ^ 2 * 3 ^ 1 * 5 ^ 1 * 11 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hp11 : Nat.Prime 11 := by norm_num
    have hd11 : q ∣ 11 ^ 1 ↔ q = 11 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp11,
        fun h => by subst q; exact dvd_pow_self (n := 1) 11 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd5, hd11, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_823 : Nat.Prime 823 := by
  refine lucas_primality 823 (3 : ZMod 823) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 823 - 1 = 2 ^ 1 * 3 ^ 1 * 137 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hd137 : q ∣ 137 ^ 1 ↔ q = 137 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_137,
        fun h => by subst q; exact dvd_pow_self (n := 1) 137 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd137, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_853 : Nat.Prime 853 := by
  refine lucas_primality 853 (2 : ZMod 853) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 853 - 1 = 2 ^ 2 * 3 ^ 1 * 71 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp71 : Nat.Prime 71 := by norm_num
    have hd71 : q ∣ 71 ^ 1 ↔ q = 71 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp71,
        fun h => by subst q; exact dvd_pow_self (n := 1) 71 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd71, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_983 : Nat.Prime 983 := by
  refine lucas_primality 983 (5 : ZMod 983) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 983 - 1 = 2 ^ 1 * 491 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hd491 : q ∣ 491 ^ 1 ↔ q = 491 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_491,
        fun h => by subst q; exact dvd_pow_self (n := 1) 491 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd491] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_1637 : Nat.Prime 1637 := by
  refine lucas_primality 1637 (2 : ZMod 1637) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1637 - 1 = 2 ^ 2 * 409 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hd409 : q ∣ 409 ^ 1 ↔ q = 409 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_409,
        fun h => by subst q; exact dvd_pow_self (n := 1) 409 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd409] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_3691 : Nat.Prime 3691 := by
  refine lucas_primality 3691 (2 : ZMod 3691) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 3691 - 1 = 2 ^ 1 * 3 ^ 2 * 5 ^ 1 * 41 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 2 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 2) 3 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hp41 : Nat.Prime 41 := by norm_num
    have hd41 : q ∣ 41 ^ 1 ↔ q = 41 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp41,
        fun h => by subst q; exact dvd_pow_self (n := 1) 41 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd5, hd41, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_4999 : Nat.Prime 4999 := by
  refine lucas_primality 4999 (3 : ZMod 4999) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 4999 - 1 = 2 ^ 1 * 3 ^ 1 * 7 ^ 2 * 17 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 2 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 2) 7 (by decide)⟩
    have hp17 : Nat.Prime 17 := by norm_num
    have hd17 : q ∣ 17 ^ 1 ↔ q = 17 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp17,
        fun h => by subst q; exact dvd_pow_self (n := 1) 17 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd7, hd17, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_5501 : Nat.Prime 5501 := by
  refine lucas_primality 5501 (2 : ZMod 5501) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5501 - 1 = 2 ^ 2 * 5 ^ 3 * 11 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 3 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 3) 5 (by decide)⟩
    have hp11 : Nat.Prime 11 := by norm_num
    have hd11 : q ∣ 11 ^ 1 ↔ q = 11 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp11,
        fun h => by subst q; exact dvd_pow_self (n := 1) 11 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd5, hd11, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_11003 : Nat.Prime 11003 := by
  refine lucas_primality 11003 (2 : ZMod 11003) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 11003 - 1 = 2 ^ 1 * 5501 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hd5501 : q ∣ 5501 ^ 1 ↔ q = 5501 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_5501,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5501 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd5501] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_20963 : Nat.Prime 20963 := by
  refine lucas_primality 20963 (2 : ZMod 20963) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 20963 - 1 = 2 ^ 1 * 47 ^ 1 * 223 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp47 : Nat.Prime 47 := by norm_num
    have hd47 : q ∣ 47 ^ 1 ↔ q = 47 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp47,
        fun h => by subst q; exact dvd_pow_self (n := 1) 47 (by decide)⟩
    have hd223 : q ∣ 223 ^ 1 ↔ q = 223 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_223,
        fun h => by subst q; exact dvd_pow_self (n := 1) 223 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd47, hd223, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_41927 : Nat.Prime 41927 := by
  refine lucas_primality 41927 (5 : ZMod 41927) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 41927 - 1 = 2 ^ 1 * 20963 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hd20963 : q ∣ 20963 ^ 1 ↔ q = 20963 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_20963,
        fun h => by subst q; exact dvd_pow_self (n := 1) 20963 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd20963] at hd
    rcases hd with rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_93001 : Nat.Prime 93001 := by
  refine lucas_primality 93001 (14 : ZMod 93001) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 93001 - 1 = 2 ^ 3 * 3 ^ 1 * 5 ^ 3 * 31 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 3 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 3) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 3 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 3) 5 (by decide)⟩
    have hp31 : Nat.Prime 31 := by norm_num
    have hd31 : q ∣ 31 ^ 1 ↔ q = 31 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp31,
        fun h => by subst q; exact dvd_pow_self (n := 1) 31 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd5, hd31, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_237073 : Nat.Prime 237073 := by
  refine lucas_primality 237073 (15 : ZMod 237073) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 237073 - 1 = 2 ^ 4 * 3 ^ 1 * 11 ^ 1 * 449 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 4 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 4) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 1 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3 (by decide)⟩
    have hp11 : Nat.Prime 11 := by norm_num
    have hd11 : q ∣ 11 ^ 1 ↔ q = 11 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp11,
        fun h => by subst q; exact dvd_pow_self (n := 1) 11 (by decide)⟩
    have hd449 : q ∣ 449 ^ 1 ↔ q = 449 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_449,
        fun h => by subst q; exact dvd_pow_self (n := 1) 449 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd11, hd449, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_1593227 : Nat.Prime 1593227 := by
  refine lucas_primality 1593227 (2 : ZMod 1593227) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1593227 - 1 = 2 ^ 1 * 19 ^ 1 * 41927 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp19 : Nat.Prime 19 := by norm_num
    have hd19 : q ∣ 19 ^ 1 ↔ q = 19 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp19,
        fun h => by subst q; exact dvd_pow_self (n := 1) 19 (by decide)⟩
    have hd41927 : q ∣ 41927 ^ 1 ↔ q = 41927 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_41927,
        fun h => by subst q; exact dvd_pow_self (n := 1) 41927 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd19, hd41927, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_405928799 : Nat.Prime 405928799 := by
  refine lucas_primality 405928799 (22 : ZMod 405928799) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 405928799 - 1 = 2 ^ 1 * 11 ^ 1 * 4999 ^ 1 * 3691 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp11 : Nat.Prime 11 := by norm_num
    have hd11 : q ∣ 11 ^ 1 ↔ q = 11 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp11,
        fun h => by subst q; exact dvd_pow_self (n := 1) 11 (by decide)⟩
    have hd4999 : q ∣ 4999 ^ 1 ↔ q = 4999 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_4999,
        fun h => by subst q; exact dvd_pow_self (n := 1) 4999 (by decide)⟩
    have hd3691 : q ∣ 3691 ^ 1 ↔ q = 3691 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_3691,
        fun h => by subst q; exact dvd_pow_self (n := 1) 3691 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd11, hd4999, hd3691, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_639533339 : Nat.Prime 639533339 := by
  refine lucas_primality 639533339 (2 : ZMod 639533339) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 639533339 - 1 = 2 ^ 1 * 229 ^ 1 * 853 ^ 1 * 1637 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hd229 : q ∣ 229 ^ 1 ↔ q = 229 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_229,
        fun h => by subst q; exact dvd_pow_self (n := 1) 229 (by decide)⟩
    have hd853 : q ∣ 853 ^ 1 ↔ q = 853 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_853,
        fun h => by subst q; exact dvd_pow_self (n := 1) 853 (by decide)⟩
    have hd1637 : q ∣ 1637 ^ 1 ↔ q = 1637 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_1637,
        fun h => by subst q; exact dvd_pow_self (n := 1) 1637 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd229, hd853, hd1637, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_12048837557 : Nat.Prime 12048837557 := by
  refine lucas_primality 12048837557 (2 : ZMod 12048837557) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 12048837557 - 1 = 2 ^ 2 * 7 ^ 2 * 661 ^ 1 * 93001 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp7 : Nat.Prime 7 := by norm_num
    have hd7 : q ∣ 7 ^ 2 ↔ q = 7 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp7,
        fun h => by subst q; exact dvd_pow_self (n := 2) 7 (by decide)⟩
    have hd661 : q ∣ 661 ^ 1 ↔ q = 661 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_661,
        fun h => by subst q; exact dvd_pow_self (n := 1) 661 (by decide)⟩
    have hd93001 : q ∣ 93001 ^ 1 ↔ q = 93001 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_93001,
        fun h => by subst q; exact dvd_pow_self (n := 1) 93001 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd7, hd661, hd93001, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_5156902474397 : Nat.Prime 5156902474397 := by
  refine lucas_primality 5156902474397 (2 : ZMod 5156902474397) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 5156902474397 - 1 = 2 ^ 2 * 107 ^ 1 * 12048837557 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hd107 : q ∣ 107 ^ 1 ↔ q = 107 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_107,
        fun h => by subst q; exact dvd_pow_self (n := 1) 107 (by decide)⟩
    have hd12048837557 : q ∣ 12048837557 ^ 1 ↔ q = 12048837557 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_12048837557,
        fun h => by subst q; exact dvd_pow_self (n := 1) 12048837557 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd107, hd12048837557, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_1670836401704629 : Nat.Prime 1670836401704629 := by
  refine lucas_primality 1670836401704629 (2 : ZMod 1670836401704629) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 1670836401704629 - 1 = 2 ^ 2 * 3 ^ 4 * 5156902474397 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 2 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 2) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 4 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 4) 3 (by decide)⟩
    have hd5156902474397 : q ∣ 5156902474397 ^ 1 ↔ q = 5156902474397 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_5156902474397,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5156902474397 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd5156902474397, or_assoc] at hd
    rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_65865678001877903 : Nat.Prime 65865678001877903 := by
  refine lucas_primality 65865678001877903 (5 : ZMod 65865678001877903) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 65865678001877903 - 1 = 2 ^ 1 * 83 ^ 1 * 379 ^ 1 * 1637 ^ 1 * 639533339 ^ 1 := by
      decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 1 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 1) 2 (by decide)⟩
    have hp83 : Nat.Prime 83 := by norm_num
    have hd83 : q ∣ 83 ^ 1 ↔ q = 83 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp83,
        fun h => by subst q; exact dvd_pow_self (n := 1) 83 (by decide)⟩
    have hd379 : q ∣ 379 ^ 1 ↔ q = 379 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_379,
        fun h => by subst q; exact dvd_pow_self (n := 1) 379 (by decide)⟩
    have hd1637 : q ∣ 1637 ^ 1 ↔ q = 1637 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_1637,
        fun h => by subst q; exact dvd_pow_self (n := 1) 1637 (by decide)⟩
    have hd639533339 : q ∣ 639533339 ^ 1 ↔ q = 639533339 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_639533339,
        fun h => by subst q; exact dvd_pow_self (n := 1) 639533339 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd83, hd379, hd1637, hd639533339, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_13818364434197438864469338081 : Nat.Prime 13818364434197438864469338081 := by
  refine lucas_primality 13818364434197438864469338081 (3 : ZMod 13818364434197438864469338081) ?_
    ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 13818364434197438864469338081 - 1 = 2 ^ 5 * 5 ^ 1 * 823 ^ 1 * 1593227 ^ 1 *
      65865678001877903 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 5 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 5) 2 (by decide)⟩
    have hp5 : Nat.Prime 5 := by norm_num
    have hd5 : q ∣ 5 ^ 1 ↔ q = 5 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp5,
        fun h => by subst q; exact dvd_pow_self (n := 1) 5 (by decide)⟩
    have hd823 : q ∣ 823 ^ 1 ↔ q = 823 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_823,
        fun h => by subst q; exact dvd_pow_self (n := 1) 823 (by decide)⟩
    have hd1593227 : q ∣ 1593227 ^ 1 ↔ q = 1593227 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_1593227,
        fun h => by subst q; exact dvd_pow_self (n := 1) 1593227 (by decide)⟩
    have hd65865678001877903 : q ∣ 65865678001877903 ^ 1 ↔ q = 65865678001877903 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_65865678001877903,
        fun h => by subst q; exact dvd_pow_self (n := 1) 65865678001877903 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd5, hd823, hd1593227, hd65865678001877903, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

set_option maxHeartbeats 4000000 in
-- Lucas checks use modular exponentiation over the stated prime factors.
theorem prime_21888242871839275222246405745257275088548364400416034343698204186575808495617 :
  Nat.Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  refine lucas_primality
    21888242871839275222246405745257275088548364400416034343698204186575808495617 (5 : ZMod
    21888242871839275222246405745257275088548364400416034343698204186575808495617) ?_ ?_
  · reduce_mod_char
  · intro q hq hd
    have hfac : 21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1
      = 2 ^ 28 * 3 ^ 2 * 13 ^ 1 * 29 ^ 1 * 983 ^ 1 * 237073 ^ 1 * 11003 ^ 1 * 405928799 ^ 1 *
      1670836401704629 ^ 1 * 13818364434197438864469338081 ^ 1 := by decide
    have hp2 : Nat.Prime 2 := by norm_num
    have hd2 : q ∣ 2 ^ 28 ↔ q = 2 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp2,
        fun h => by subst q; exact dvd_pow_self (n := 28) 2 (by decide)⟩
    have hp3 : Nat.Prime 3 := by norm_num
    have hd3 : q ∣ 3 ^ 2 ↔ q = 3 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp3,
        fun h => by subst q; exact dvd_pow_self (n := 2) 3 (by decide)⟩
    have hp13 : Nat.Prime 13 := by norm_num
    have hd13 : q ∣ 13 ^ 1 ↔ q = 13 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp13,
        fun h => by subst q; exact dvd_pow_self (n := 1) 13 (by decide)⟩
    have hp29 : Nat.Prime 29 := by norm_num
    have hd29 : q ∣ 29 ^ 1 ↔ q = 29 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq hp29,
        fun h => by subst q; exact dvd_pow_self (n := 1) 29 (by decide)⟩
    have hd983 : q ∣ 983 ^ 1 ↔ q = 983 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_983,
        fun h => by subst q; exact dvd_pow_self (n := 1) 983 (by decide)⟩
    have hd237073 : q ∣ 237073 ^ 1 ↔ q = 237073 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_237073,
        fun h => by subst q; exact dvd_pow_self (n := 1) 237073 (by decide)⟩
    have hd11003 : q ∣ 11003 ^ 1 ↔ q = 11003 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_11003,
        fun h => by subst q; exact dvd_pow_self (n := 1) 11003 (by decide)⟩
    have hd405928799 : q ∣ 405928799 ^ 1 ↔ q = 405928799 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_405928799,
        fun h => by subst q; exact dvd_pow_self (n := 1) 405928799 (by decide)⟩
    have hd1670836401704629 : q ∣ 1670836401704629 ^ 1 ↔ q = 1670836401704629 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_1670836401704629,
        fun h => by subst q; exact dvd_pow_self (n := 1) 1670836401704629 (by decide)⟩
    have hd13818364434197438864469338081 : q ∣ 13818364434197438864469338081 ^ 1 ↔ q =
      13818364434197438864469338081 := by
      exact ⟨Nat.prime_eq_prime_of_dvd_pow hq prime_13818364434197438864469338081,
        fun h => by subst q; exact dvd_pow_self (n := 1) 13818364434197438864469338081 (by decide)⟩
    rw [hfac] at hd
    simp only [hq.dvd_mul, hd2, hd3, hd13, hd29, hd983, hd237073, hd11003, hd405928799,
      hd1670836401704629, hd13818364434197438864469338081, or_assoc] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char
      <;> decide

end Poseidon2.Primality
