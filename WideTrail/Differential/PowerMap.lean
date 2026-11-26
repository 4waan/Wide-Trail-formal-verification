/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Differential.Polynomial

/-!
# Differential uniformity of power maps

`Polynomial.lean` bounds the fifth-power S-box by writing its difference polynomial out
coefficient by coefficient. This file does the same for every exponent at once.

For an input difference `a ≠ 0`, the inputs with `(x + a) ^ d - x ^ d = b` are roots of
`(X + C a) ^ d - X ^ d - C b`. The `X ^ d` terms cancel, so this polynomial has degree at
most `d - 1`, and its coefficient at `X ^ k` is `a ^ (d - k) * (d choose k)` for
`0 < k < d`. One such coefficient being nonzero makes the polynomial nonzero, and then it
has at most `d - 1` roots.

* `pow_uniform_of_choose`: `x ↦ x ^ d` has differential uniformity at most `d - 1` over
  every finite field in which some binomial coefficient `d choose k` with `0 < k < d` is
  nonzero.
* `pow_uniform`: the case `k = 1`, i.e. `(d : K) ≠ 0` and `2 ≤ d`.
* `pow_three_uniform`, `pow_seven_uniform`: the exponents three and seven, with bounds two
  and six. The fifth-power case recovers `pow_five_uniform` from `Polynomial.lean`.

What is not claimed. The bound `d - 1` is an upper bound only. Whether it is attained
depends on the field: `Checks/PowerMap.lean` exhibits fields where it is and fields
where the maximum is smaller. The hypothesis `(d : K) ≠ 0` cannot simply be dropped:
when `d` is a power of the characteristic, `x ↦ x ^ d` is additive and one output
difference is reached by every input. Nothing here says anything about the
characteristic-dividing case beyond `pow_uniform_of_choose`.
-/

set_option autoImplicit false

namespace Sbox

open Polynomial

section DifferencePolynomial

variable {R : Type*} [CommRing R]

/-- Coefficients of the difference polynomial of `x ↦ x ^ d` strictly between `0` and
`d`. -/
theorem powDiff_coeff {d k : Nat} (hk0 : 0 < k) (hkd : k < d) (a b : R) :
    ((X + C a) ^ d - X ^ d - C b).coeff k = a ^ (d - k) * (d.choose k : R) := by
  simp [coeff_X_add_C_pow, coeff_X_pow, coeff_C, hkd.ne, hk0.ne']

/-- The difference polynomial of `x ↦ x ^ d` has degree at most `d - 1`: the two
`X ^ d` terms cancel. -/
theorem powDiff_natDegree_le (d : Nat) (a b : R) :
    ((X + C a) ^ d - X ^ d - C b).natDegree ≤ d - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hdn : d ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  rcases hdn.eq_or_lt with rfl | hlt
  · simp [coeff_X_add_C_pow, coeff_C, hn0]
  · simp [coeff_X_add_C_pow, coeff_X_pow, coeff_C, Nat.choose_eq_zero_of_lt hlt, hlt.ne',
      hn0]

end DifferencePolynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Power maps, general form.** If some binomial coefficient `d choose k` with
`0 < k < d` is nonzero in `K`, then `x ↦ x ^ d` has differential uniformity at most
`d - 1`. The coefficient of `X ^ k` in the difference polynomial is
`a ^ (d - k) * (d choose k)`, which is nonzero for `a ≠ 0`, so the polynomial is nonzero
of degree at most `d - 1`.

This hypothesis is weaker than `(d : K) ≠ 0`: for `d = 6` in characteristic two, `6` vanishes but
`6 choose 2 = 15` does not. By Lucas' theorem (not proved here) every such coefficient
vanishes only when `d` is a power of the characteristic, and then `x ↦ x ^ d` is
additive. -/
theorem pow_uniform_of_choose {d k : Nat} (hk0 : 0 < k) (hkd : k < d)
    (hk : (d.choose k : K) ≠ 0) : IsDiffUniform (fun x : K => x ^ d) (d - 1) := by
  intro a ha b
  have hp : (X + C a) ^ d - X ^ d - C b ≠ 0 := by
    intro h
    have hc := congrArg (fun q : K[X] => q.coeff k) h
    simp only [powDiff_coeff hk0 hkd, coeff_zero] at hc
    exact mul_ne_zero (pow_ne_zero _ ha) hk hc
  apply le_trans (diffCount_le_polynomial _ hp ?_) (powDiff_natDegree_le d a b)
  intro x hx
  simp [hx]

/-- **Power maps.** If `2 ≤ d` and `d` is nonzero in `K`, then `x ↦ x ^ d` has
differential uniformity at most `d - 1`. The difference polynomial has degree at most
`d - 1`, and its coefficient of `X` is `d * a ^ (d - 1)`, which is nonzero.

Neither hypothesis can be dropped. For `d = 1` the map is additive. For `d` equal to the
characteristic the map is additive as well; `Checks/PowerMap.lean` decides both cases
over small fields. -/
theorem pow_uniform (d : Nat) (hd : 2 ≤ d) (hdK : (d : K) ≠ 0) :
    IsDiffUniform (fun x : K => x ^ d) (d - 1) :=
  pow_uniform_of_choose (k := 1) Nat.one_pos hd (by rwa [Nat.choose_one_right])

/-- The fifth-power case of `pow_uniform` is exactly `pow_five_uniform`. -/
example (hfive : (5 : K) ≠ 0) : IsDiffUniform (fun x : K => x ^ 5) 4 :=
  pow_uniform 5 (by norm_num) (by exact_mod_cast hfive)

/-- The cube S-box has differential uniformity at most two when three is nonzero in the
field. -/
theorem pow_three_uniform (hthree : (3 : K) ≠ 0) : IsDiffUniform (fun x : K => x ^ 3) 2 :=
  pow_uniform 3 (by norm_num) (by exact_mod_cast hthree)

/-- The seventh-power S-box has differential uniformity at most six when seven is nonzero
in the field. -/
theorem pow_seven_uniform (hseven : (7 : K) ≠ 0) : IsDiffUniform (fun x : K => x ^ 7) 6 :=
  pow_uniform 7 (by norm_num) (by exact_mod_cast hseven)

end Sbox
