/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.MDS4
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

/-!
# Checks for the `MDSMat4` criterion

`WideTrail.Algebra.MDS4` proves that `m4 = circ(2, 3, 1, 1)` is MDS over a field `K`
exactly when `2, 3, 5, 7, 11, 17` are nonzero in `K`. The checks below test both
directions on concrete fields.

* Over `ZMod 11` the integer `11` vanishes. The order-`3` minor on rows `0, 1, 3` and
  columns `1, 2, 3` is singular, so `m4` is not MDS, and the state `(0, 1, 6, 2)` is sent to
  `(0, 0, 8, 0)`: weight `3 + 1 = 4 < 5`. In `ZMod 11` the integer `35` is nonzero, so
  `m4Equiv` exists there; invertibility alone does not give branch number `5`.
* Over `ZMod 7` the integer `7` vanishes. The order-`2` minor on rows `1, 2` and columns
  `2, 3` is singular, and the state `(0, 0, 1, 4)` is sent to `(5, 0, 0, 2)`, again weight
  `4`.
* Over `ZMod 13` the hypothesis holds, so the branch number is at least `5`; the unit
  vector `(0, 0, 0, 1)` has weight exactly `5`, so the bound is attained. (An exhaustive
  search over all `13 ^ 4` states outside Lean finds no state of weight below `5`; only the
  attaining witness is used here.)
* For the KoalaBear prime `2130706433 = 2 ^ 31 - 2 ^ 24 + 1` and the BabyBear prime
  `2013265921 = 2 ^ 31 - 2 ^ 27 + 1`, every element of `m4Primes` and of `m4Minors`, and
  `35`, is nonzero in `ZMod p`. These are facts about the ring `ZMod p` and use no
  primality. The instantiations `koalaBear_isMDS`, `babyBear_isMDS` and the branch bounds
  take primality as an instance argument `[Fact (Nat.Prime p)]`, which is needed for
  `ZMod p` to be a field; primality of these two numbers is not proved here.

The HorizenLabs reference implementation of Poseidon2 uses a different `4 × 4` matrix,
`[[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7], [1, 1, 4, 6]]` (`apply_hl_mat4`). It is not the
matrix of Plonky3's `MDSMat4`, which is the one `Poseidon2ExternalMatrixGeneral` uses and
the one formalised in `MDS4.lean`; `hlMat4_ne_m4` records that the two differ. Nothing
here is about the HorizenLabs matrix beyond `hlMat4_ne_m4`. That matrix is treated over
every field in `WideTrail.Poseidon2.HorizenLabsM4`, and
`Poseidon2.AztecBN254.Checks.mds4Checks_hlMat4_eq` proves that the integer matrix
`MDS4Checks.hlMat4` below is `Poseidon2.hlMat4 ℤ`.

All finite checks are kernel `decide`.
-/

set_option autoImplicit false

namespace Poseidon2.MDS4Checks

/-! ### Over `ZMod 11`: `11` vanishes and `m4` is not MDS -/

instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The order-`3` minor omitting row `2` and column `0` is `11` over `ℤ`, so it vanishes in
`ZMod 11`. -/
theorem minor_eleven :
    ((m4 (ZMod 11)).submatrix (Fin.succAbove 2) (Fin.succAbove 0)).det = 0 := by
  rw [Matrix.det_fin_three]
  decide

theorem not_isMDS_eleven : ¬ IsMDS (m4 (ZMod 11)) := fun h =>
  det_submatrix_ne_zero_of_isMDS h (Fin.strictMono_succAbove 2) (Fin.strictMono_succAbove 0)
    minor_eleven

/-- The same conclusion from the exact criterion `m4_isMDS_iff`. -/
theorem not_isMDS_eleven' : ¬ IsMDS (m4 (ZMod 11)) := by
  rw [m4_isMDS_iff]
  decide

/-- A state of weight `3` whose image has weight `1`. -/
def witnessEleven : Fin 4 → ZMod 11 := ![0, 1, 6, 2]

theorem m4_witnessEleven : (m4 (ZMod 11)).mulVec witnessEleven = ![0, 0, 8, 0] := by
  decide

theorem weight_witnessEleven :
    weight witnessEleven + weight ((m4 (ZMod 11)).mulVec witnessEleven) = 4 := by
  decide

theorem thirtyFive_ne_zero_eleven : (35 : ZMod 11) ≠ 0 := by decide

/-- **Invertibility does not suffice.** Over `ZMod 11`, `m4Equiv` is defined, but its branch
number is not `5`. -/
theorem not_isBranchBound_eleven :
    ¬ isBranchBound id (m4Equiv (ZMod 11) thirtyFive_ne_zero_eleven) 5 := by
  intro h
  have hw := h witnessEleven (by decide)
  rw [colWeight_id, colWeight_id, m4Equiv_apply, weight_witnessEleven] at hw
  omega

/-! ### Over `ZMod 7`: `7` vanishes at an order-`2` minor -/

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The order-`2` minor on rows `1, 2` and columns `2, 3` is `7` over `ℤ`. -/
theorem minor_seven : ((m4 (ZMod 7)).submatrix ![1, 2] ![2, 3]).det = 0 := by
  rw [Matrix.det_fin_two]
  decide

theorem not_isMDS_seven : ¬ IsMDS (m4 (ZMod 7)) := fun h =>
  det_submatrix_ne_zero_of_isMDS h
    (Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; decide))
    (Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; decide)) minor_seven

def witnessSeven : Fin 4 → ZMod 7 := ![0, 0, 1, 4]

theorem m4_witnessSeven : (m4 (ZMod 7)).mulVec witnessSeven = ![5, 0, 0, 2] := by
  decide

theorem not_isBranchBound_seven : ¬ isBranchBound id (m4 (ZMod 7)).mulVec 5 := by
  intro h
  have hw := h witnessSeven (by decide)
  rw [colWeight_id, colWeight_id] at hw
  have hw' : weight witnessSeven + weight ((m4 (ZMod 7)).mulVec witnessSeven) = 4 := by
    decide
  omega

/-! ### Over `ZMod 13`: the hypothesis holds and the bound is attained -/

instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by decide⟩

theorem primes_ne_zero_thirteen : ∀ p ∈ m4Primes, (p : ZMod 13) ≠ 0 := by decide

theorem isMDS_thirteen : IsMDS (m4 (ZMod 13)) := m4_isMDS primes_ne_zero_thirteen

theorem isBranchBound_thirteen : isBranchBound id (m4 (ZMod 13)).mulVec 5 :=
  m4_isBranchBound primes_ne_zero_thirteen

/-- The bound `5` is attained over `ZMod 13`. -/
theorem weight_unit_thirteen :
    weight (![0, 0, 0, 1] : Fin 4 → ZMod 13)
      + weight ((m4 (ZMod 13)).mulVec ![0, 0, 0, 1]) = 5 := by
  decide

/-! ### The KoalaBear and BabyBear primes -/

/-- KoalaBear, `p = 2130706433`: the hypothesis of `m4_isMDS`, as a fact about the ring
`ZMod p`. -/
theorem koalaBear_primes_ne_zero : ∀ p ∈ m4Primes, (p : ZMod 2130706433) ≠ 0 := by decide

theorem koalaBear_minors_ne_zero : ∀ n ∈ m4Minors, (n : ZMod 2130706433) ≠ 0 := by decide

theorem koalaBear_thirtyFive_ne_zero : (35 : ZMod 2130706433) ≠ 0 := by decide

/-- BabyBear, `p = 2013265921`: the hypothesis of `m4_isMDS`, as a fact about the ring
`ZMod p`. -/
theorem babyBear_primes_ne_zero : ∀ p ∈ m4Primes, (p : ZMod 2013265921) ≠ 0 := by decide

theorem babyBear_minors_ne_zero : ∀ n ∈ m4Minors, (n : ZMod 2013265921) ≠ 0 := by decide

theorem babyBear_thirtyFive_ne_zero : (35 : ZMod 2013265921) ≠ 0 := by decide

/-- `m4` is MDS over the KoalaBear field, given that `2130706433` is prime. -/
theorem koalaBear_isMDS [Fact (Nat.Prime 2130706433)] : IsMDS (m4 (ZMod 2130706433)) :=
  m4_isMDS koalaBear_primes_ne_zero

/-- Branch number at least `5` over the KoalaBear field, given that `2130706433` is prime. -/
theorem koalaBear_isBranchBound [Fact (Nat.Prime 2130706433)] :
    isBranchBound id (m4Equiv (ZMod 2130706433) koalaBear_thirtyFive_ne_zero) 5 :=
  m4Equiv_isBranchBound koalaBear_primes_ne_zero koalaBear_thirtyFive_ne_zero

/-- `m4` is MDS over the BabyBear field, given that `2013265921` is prime. -/
theorem babyBear_isMDS [Fact (Nat.Prime 2013265921)] : IsMDS (m4 (ZMod 2013265921)) :=
  m4_isMDS babyBear_primes_ne_zero

/-- Branch number at least `5` over the BabyBear field, given that `2013265921` is prime. -/
theorem babyBear_isBranchBound [Fact (Nat.Prime 2013265921)] :
    isBranchBound id (m4Equiv (ZMod 2013265921) babyBear_thirtyFive_ne_zero) 5 :=
  m4Equiv_isBranchBound babyBear_primes_ne_zero babyBear_thirtyFive_ne_zero

/-! ### The HorizenLabs matrix is a different matrix -/

/-- The matrix of HorizenLabs' `apply_hl_mat4`. It is not the Plonky3 `MDSMat4`. -/
def hlMat4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![5, 7, 1, 3;
     4, 6, 1, 1;
     1, 3, 5, 7;
     1, 1, 4, 6]

theorem hlMat4_ne_m4 : hlMat4 ≠ m4 ℤ := by decide

end Poseidon2.MDS4Checks
