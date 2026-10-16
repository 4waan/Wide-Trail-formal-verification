import Mathlib.FieldTheory.Finite.Basic

/-! Executable power S-box inverses certified by finite-field arithmetic. -/

set_option autoImplicit false

namespace Sbox

section Fermat

variable {K : Type*} [Field K]

theorem pow_inverse_of_fermat (q e d k : Nat) (he : 0 < e) (hd : 0 < d)
    (hexp : e * d = (q - 1) * k + 1)
    (hfermat : ∀ x : K, x ≠ 0 → x ^ (q - 1) = 1) (x : K) : (x ^ e) ^ d = x := by
  by_cases hx : x = 0
  · simp [hx, ne_of_gt he, ne_of_gt hd]
  · rw [← pow_mul, hexp, pow_add, pow_mul, hfermat x hx]
    simp

/-- The executable equivalence carries no enumeration of the field. -/
def powerEquivOfFermat (q e d k : Nat) (he : 0 < e) (hd : 0 < d)
    (hexp : e * d = (q - 1) * k + 1)
    (hfermat : ∀ x : K, x ≠ 0 → x ^ (q - 1) = 1) : K ≃ K where
  toFun x := x ^ e
  invFun x := x ^ d
  left_inv := pow_inverse_of_fermat q e d k he hd hexp hfermat
  right_inv := pow_inverse_of_fermat q d e k hd he
    (by rw [Nat.mul_comm]; exact hexp) hfermat

end Fermat

variable {K : Type*} [Field K] [Fintype K]

theorem pow_inverse (e d k : Nat) (he : 0 < e) (hd : 0 < d)
    (hexp : e * d = (Fintype.card K - 1) * k + 1) (x : K) : (x ^ e) ^ d = x := by
  by_cases hx : x = 0
  · simp [hx, ne_of_gt he, ne_of_gt hd]
  · rw [← pow_mul, hexp, pow_add, pow_mul, FiniteField.pow_card_sub_one_eq_one x hx]
    simp

def powerEquiv (e d k : Nat) (he : 0 < e) (hd : 0 < d)
    (hexp : e * d = (Fintype.card K - 1) * k + 1) : K ≃ K where
  toFun x := x ^ e
  invFun x := x ^ d
  left_inv := pow_inverse e d k he hd hexp
  right_inv := pow_inverse d e k hd he (by rw [Nat.mul_comm]; exact hexp)

end Sbox
