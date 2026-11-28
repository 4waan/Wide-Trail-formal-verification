/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Algebra.GF256
import WideTrail.Linear.AESSpectrum
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# The trace of `GF(2⁸)` as a bit functional

The facts about the trace of `GF(2⁸)` that the AES S-box bound of `Linear/AESSbox.lean` uses,
split into their own module so that each file's kernel checks stay small. Everything is about the
type `GF256` of `Algebra/GF256.lean`; nothing here mentions a pairing, a Walsh value or the S-box.

* `forall_of_checkFrom`: a decidable statement about bytes holds for every byte once the kernel
  has checked it on `0, …, 255`, in four chunks of 64 (`checkFrom`). The 256-case statements
  below are proved this way.
* `bit z i ∈ ZMod 2` is bit `i` of the byte `z`, and `basis i` is the byte `2ⁱ`. Every byte is
  the sum of the basis bytes selected by its bits (`eq_sum_basis`, 256 cases), so an additive
  map out of `GF256` is determined by its values on the eight basis bytes (`addHom_ext`,
  `addHom_apply_eq_sum`).
* `trace : GF256 →+ ZMod 2` is the functional with mask `0xA0`, `z ↦ bit₅ z + bit₇ z`.
  `trace_eq_fieldTrace` identifies it with the absolute trace: for every `z`,
  `z + z² + z⁴ + ⋯ + z¹²⁸` is `1` when `trace z = 1` and `0` otherwise. The kernel checks the 256
  cases on the squaring chain `fieldTrace` (seven multiplications per byte; `GF256` keeps the
  default power, so `z ^ 128` would be evaluated by repeated multiplication), and the form with
  powers follows by `ring`.
* `trace_inv_eq_g`: `trace z⁻¹` is bit `z` of the table `Linear.AESSpectrum.gTab`
  (`Linear.AESSpectrum.g`), checked by the kernel on all 256 bytes (with `0⁻¹ = 0`).
* `phi c` is the byte whose bit `i` is `trace (c * 2ⁱ)` (`bit_phi`), so that `z ↦ trace (c * z)`
  is the linear function with mask `phi c`: `trace (c * z) = ∑ᵢ bitᵢ (phi c) · bitᵢ z`
  (`trace_mul_eq_sum`, by additivity in `z`), which is the parity
  `Linear.AESSpectrum.par8 (phi c ∧ z)` read in `ZMod 2` (`trace_mul_eq_par8`). The parity of a
  byte is the sum of its bits by a check on the 256 values (`natCast_par8`).

## What is not claimed

`trace` is fixed as the functional with mask `0xA0`; that it equals the absolute trace is the
256-case statement `trace_eq_fieldTrace`, and no other property of the absolute trace (such as
its Galois invariance) is proved. `phi` is not shown to be a bijection; the S-box bound does not
need it, since the spectrum of `Linear/AESSpectrum.lean` covers every mask.
-/

set_option autoImplicit false

namespace GF256

open Linear.AESSpectrum (par8 g)

/-! ### Checking all 256 bytes

A statement about every byte is checked by the kernel in four chunks of 64 bytes, each a
structural recursion on `ℕ`. Separate chunks keep the kernel's memory small. -/

/-- `checkFrom p base n` is `p base && p (base + 1) && ⋯ && p (base + n - 1)`. -/
def checkFrom (p : ℕ → Bool) (base : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => checkFrom p base n && p (base + n)

theorem checkFrom_spec {p : ℕ → Bool} {base : ℕ} :
    ∀ {n : ℕ}, checkFrom p base n = true → ∀ m, m < n → p (base + m) = true
  | 0, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | n + 1, h, m, hm => by
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
    · exact checkFrom_spec h.1 m hm
    · subst hm
      exact h.2

/-- A decidable property of bytes holds for every byte once the four chunks of the check on
`⟨BitVec.ofNat 8 n⟩`, `n < 256`, pass. -/
theorem forall_of_checkFrom {P : GF256 → Prop} [DecidablePred P]
    (h₀ : checkFrom (fun n => decide (P ⟨BitVec.ofNat 8 n⟩)) 0 64 = true)
    (h₁ : checkFrom (fun n => decide (P ⟨BitVec.ofNat 8 n⟩)) 64 64 = true)
    (h₂ : checkFrom (fun n => decide (P ⟨BitVec.ofNat 8 n⟩)) 128 64 = true)
    (h₃ : checkFrom (fun n => decide (P ⟨BitVec.ofNat 8 n⟩)) 192 64 = true) (z : GF256) :
    P z := by
  have hz : z = ⟨BitVec.ofNat 8 z.val.toNat⟩ := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlt : z.val.toNat < 256 := z.val.isLt
  have key : decide (P ⟨BitVec.ofNat 8 z.val.toNat⟩) = true := by
    generalize z.val.toNat = n at hlt
    by_cases c₀ : n < 64
    · simpa using checkFrom_spec h₀ n c₀
    by_cases c₁ : n < 128
    · simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt c₀)] using
        checkFrom_spec h₁ (n - 64) (by omega)
    by_cases c₂ : n < 192
    · simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt c₁)] using
        checkFrom_spec h₂ (n - 128) (by omega)
    · simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt c₂)] using
        checkFrom_spec h₃ (n - 192) (by omega)
  rw [hz]
  exact of_decide_eq_true key

/-! ### Bits and the basis -/

/-- Bit `i` of a byte, as an element of `ZMod 2`. -/
def bit (z : GF256) (i : Fin 8) : ZMod 2 := if z.val.getLsbD i then 1 else 0

theorem bit_add (x y : GF256) (i : Fin 8) : bit (x + y) i = bit x i + bit y i := by
  change (if (x.val ^^^ y.val).getLsbD i then (1 : ZMod 2) else 0) = _
  rw [BitVec.getLsbD_xor]
  unfold bit
  cases x.val.getLsbD i <;> cases y.val.getLsbD i <;> decide

@[simp] theorem bit_zero (i : Fin 8) : bit 0 i = 0 := by
  revert i
  decide

/-- The byte `2ⁱ`, the basis element `i` of `GF(2⁸)` over `GF(2)`. -/
def basis (i : Fin 8) : GF256 := ⟨pow2 i⟩

/-- **Every byte is the sum of the basis bytes selected by its bits.** Checked on all 256
bytes. -/
theorem eq_sum_basis (z : GF256) :
    z = ∑ i : Fin 8, if z.val.getLsbD i then basis i else 0 :=
  forall_of_checkFrom (P := fun z => z = ∑ i : Fin 8, if z.val.getLsbD i then basis i else 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) z

/-- An additive map out of `GF256` is the sum of its values on the basis bytes selected by the
bits of its argument. -/
theorem addHom_apply_eq_sum {M : Type*} [AddCommMonoid M] (f : GF256 →+ M) (z : GF256) :
    f z = ∑ i : Fin 8, if z.val.getLsbD i then f (basis i) else 0 := by
  conv_lhs => rw [eq_sum_basis z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- Two additive maps out of `GF256` that agree on the eight basis bytes are equal. -/
theorem addHom_ext {M : Type*} [AddCommMonoid M] {f f' : GF256 →+ M}
    (h : ∀ i, f (basis i) = f' (basis i)) : f = f' := by
  ext z
  rw [addHom_apply_eq_sum f, addHom_apply_eq_sum f']
  simp only [h]

/-- For an additive map into `ZMod 2`: `f z = ∑ᵢ bitᵢ z · f (2ⁱ)`. -/
theorem addHom_apply_eq_sum_bit (f : GF256 →+ ZMod 2) (z : GF256) :
    f z = ∑ i : Fin 8, bit z i * f (basis i) := by
  rw [addHom_apply_eq_sum f]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold bit
  split_ifs <;> simp

/-! ### The trace -/

/-- The trace of `GF(2⁸)`, as the functional with mask `0xA0`: `z ↦ bit₅ z + bit₇ z`. It equals
the absolute trace `z + z² + ⋯ + z¹²⁸` (`trace_eq_fieldTrace`). -/
def trace : GF256 →+ ZMod 2 where
  toFun z := bit z 5 + bit z 7
  map_zero' := by simp
  map_add' x y := by
    simp only [bit_add]
    exact add_add_add_comm _ _ _ _

theorem trace_apply (z : GF256) : trace z = bit z 5 + bit z 7 := rfl

/-- The absolute trace `z + z² + z⁴ + ⋯ + z¹²⁸` by a squaring chain: seven multiplications. -/
def fieldTrace (z : GF256) : GF256 :=
  let z2 := z * z
  let z4 := z2 * z2
  let z8 := z4 * z4
  let z16 := z8 * z8
  let z32 := z16 * z16
  let z64 := z32 * z32
  let z128 := z64 * z64
  z + z2 + z4 + z8 + z16 + z32 + z64 + z128

/-- **The squaring chain takes the value `trace z`**, on all 256 bytes. -/
theorem fieldTrace_eq (z : GF256) : fieldTrace z = if trace z = 1 then 1 else 0 :=
  forall_of_checkFrom (P := fun z => fieldTrace z = if trace z = 1 then 1 else 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) z

theorem fieldTrace_eq_pow (z : GF256) :
    fieldTrace z = z + z ^ 2 + z ^ 4 + z ^ 8 + z ^ 16 + z ^ 32 + z ^ 64 + z ^ 128 := by
  simp only [fieldTrace]
  ring

/-- **The functional with mask `0xA0` is the absolute trace**: `z + z² + ⋯ + z¹²⁸` is `1` when
`trace z = 1` and `0` when `trace z = 0`. -/
theorem trace_eq_fieldTrace (z : GF256) :
    z + z ^ 2 + z ^ 4 + z ^ 8 + z ^ 16 + z ^ 32 + z ^ 64 + z ^ 128
      = if trace z = 1 then 1 else 0 := by
  rw [← fieldTrace_eq_pow, fieldTrace_eq]

/-- **The table `gTab` is the truth table of `z ↦ trace z⁻¹`** (with `0⁻¹ = 0`), on all 256
bytes. -/
theorem trace_inv_eq_g (z : GF256) : trace z⁻¹ = (g z.val.toNat : ZMod 2) :=
  forall_of_checkFrom (P := fun z => trace z⁻¹ = (g z.val.toNat : ZMod 2))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) z

/-! ### The mask of `z ↦ trace (c * z)` -/

/-- The byte whose bit `i` is `trace (c * 2ⁱ)`. -/
def phi (c : GF256) : GF256 :=
  ⟨BitVec.ofBoolListLE [decide (trace (c * basis 0) = 1), decide (trace (c * basis 1) = 1),
    decide (trace (c * basis 2) = 1), decide (trace (c * basis 3) = 1),
    decide (trace (c * basis 4) = 1), decide (trace (c * basis 5) = 1),
    decide (trace (c * basis 6) = 1), decide (trace (c * basis 7) = 1)]⟩

theorem bit_phi (c : GF256) (i : Fin 8) : bit (phi c) i = trace (c * basis i) := by
  have key : ∀ t : ZMod 2, (if decide (t = 1) = true then (1 : ZMod 2) else 0) = t := by decide
  unfold bit phi
  rw [BitVec.getLsbD_ofBoolListLE]
  match i with
  | 0 => exact key _
  | 1 => exact key _
  | 2 => exact key _
  | 3 => exact key _
  | 4 => exact key _
  | 5 => exact key _
  | 6 => exact key _
  | 7 => exact key _

/-- `z ↦ trace (c * z)` is the linear function with mask `phi c`. -/
theorem trace_mul_eq_sum (c z : GF256) :
    trace (c * z) = ∑ i : Fin 8, bit (phi c) i * bit z i := by
  have h := addHom_apply_eq_sum_bit (trace.comp (AddMonoidHom.mulLeft c)) z
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bit_phi, mul_comm]

/-- The parity `par8 x` of a byte `x < 256`, read in `ZMod 2`, is the sum of its bits. Checked on
all 256 values. -/
theorem natCast_par8 :
    ∀ x, x < 256 → ((par8 x : ℕ) : ZMod 2) = ∑ i : Fin 8, if x.testBit i then 1 else 0 := by
  decide +kernel

/-- **`trace (c * z)` is the parity of `phi c ∧ z`**, read in `ZMod 2`. -/
theorem trace_mul_eq_par8 (c z : GF256) :
    trace (c * z) = (par8 ((phi c).val.toNat &&& z.val.toNat) : ZMod 2) := by
  have hlt : (phi c).val.toNat &&& z.val.toNat < 256 :=
    lt_of_lt_of_eq (Nat.and_lt_two_pow _ z.val.isLt) (by norm_num)
  rw [natCast_par8 _ hlt, trace_mul_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_and, BitVec.testBit_toNat, BitVec.testBit_toNat]
  unfold bit
  cases (phi c).val.getLsbD i <;> cases z.val.getLsbD i <;> simp

end GF256
