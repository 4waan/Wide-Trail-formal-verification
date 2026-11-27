/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/

/-!
# The Walsh spectrum of `z ↦ Tr(z⁻¹)` on `GF(2⁸)`, on natural numbers

The kernel computation behind the AES S-box linearity bound (`AES.sbox_walsh_le` in
`Linear/AESSbox.lean`). This file imports nothing: every definition is a function on `Nat`, and
the kernel evaluates them with its natural-number arithmetic.

A byte `z` is the natural number `z < 256`. The data are:

* `gTab`, a natural number whose bits `0` to `255` are the table; `g z = (gTab >>> z) &&& 1` is
  bit `z` of it. `Linear/GF256Trace.lean` proves that `g z` is the trace of `z⁻¹` in `GF(2⁸)`
  (with `0⁻¹ = 0`), for the trace functional with mask `0xA0` (`GF256.trace_inv_eq_g`);
* `par8 x`, the parity of the low eight bits of `x`, by an xor fold. For a mask `w < 256`,
  `z ↦ par8 (w &&& z)` is the linear Boolean function with mask `w`;
* `mism w n`, the number of `z < n` with `par8 (w &&& z) ≠ g z`, by structural recursion on `n`.

The Walsh value of `g` at the mask `w`, `W_g(w) = ∑_{z < 256} (-1) ^ (g z + par8 (w &&& z))`, is
`256 - 2 · mism w 256`, so `|W_g(w)| ≤ t` is `specLe t w`: `256 ≤ 2 · mism w 256 + t` and
`2 · mism w 256 ≤ 256 + t`. Here `W_g(w)` is only a name for `256 - 2 · mism w 256`;
`Linear/AESSbox.lean` proves that the trace-pairing Walsh value of inversion at `(c, 1)` equals
`256 - 2 · mism (phi c) 256` (`AES.walsh_inv_one_eq_spectrum`).

## What is proved

* `chunk₀` to `chunk₃`: `specLe 32 w` for `w` in `[0, 64)`, `[64, 128)`, `[128, 192)` and
  `[192, 256)`, each by `decide +kernel` (`64 · 256` terms per chunk);
* `specLe_32`: `specLe 32 w` for every `w < 256`, and `spectrum_bound`, its arithmetic form
  `256 ≤ 2 · mism w 256 + 32 ∧ 2 · mism w 256 ≤ 288`: every Walsh value of `g` is at most `32` in
  absolute value;
* `mism_ac`: `mism 0xac 256 = 112`, so `W_g(0xac) = 32` and the bound `32` is attained (it is the
  mask of the witness `AES.sbox_walsh_attained`);
* `specLe_28_false`: with the value `32` lowered to `28` the check fails at `w = 0x0c`
  (`mism 0x0c 256 = 112`), so `not_forall_specLe_28`: not every mask passes `specLe 28`. The
  chunks are not vacuous.

## What is not claimed

Nothing here mentions `GF(2⁸)`, the S-box or a Walsh value: these are statements about natural
numbers. That `gTab` is the truth table of `Tr(z⁻¹)`, and that the trace-pairing Walsh values of
the AES S-box reduce to `256 - 2 · mism w 256`, are proved in `Linear/GF256Trace.lean` and
`Linear/AESSbox.lean`.
-/

set_option autoImplicit false

namespace Linear.AESSpectrum

/-- The parity of the low eight bits of `x`, by an xor fold: `0` or `1`. -/
def par8 (x : Nat) : Nat :=
  let y := x ^^^ (x >>> 4)
  let y := y ^^^ (y >>> 2)
  let y := y ^^^ (y >>> 1)
  y &&& 1

/-- The table as a natural number: for `z < 256`, bit `z` is the trace of `z⁻¹` in `GF(2⁸)`
(`GF256.trace_inv_eq_g`). -/
def gTab : Nat := 0x179e0454df3902364ee0d35eedff0f3fc68dfc48466822bc1e6d95830a718cd4

/-- Bit `z` of `gTab`, `0` or `1`. -/
def g (z : Nat) : Nat := (gTab >>> z) &&& 1

theorem par8_lt_two (x : Nat) : par8 x < 2 := by
  unfold par8
  rw [Nat.and_one_is_mod]
  exact Nat.mod_lt _ (by decide)

theorem g_lt_two (z : Nat) : g z < 2 := by
  unfold g
  rw [Nat.and_one_is_mod]
  exact Nat.mod_lt _ (by decide)

/-- The number of `z < n` at which `par8 (w &&& z)` and `g z` differ. -/
def mism (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mism w n + (par8 (w &&& n) ^^^ g n)

/-- `|256 - 2 · mism w 256| ≤ t`, written without subtraction. -/
def specLe (t w : Nat) : Bool :=
  256 ≤ 2 * mism w 256 + t && 2 * mism w 256 ≤ 256 + t

/-- `specLe t (base + m)` for every `m < n`, checked from `m = 0` up. -/
def allFrom (t base : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => allFrom t base n && specLe t (base + n)

theorem allFrom_spec {t base : Nat} :
    ∀ {n : Nat}, allFrom t base n = true → ∀ m, m < n → specLe t (base + m) = true
  | 0, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | n + 1, h, m, hm => by
    simp only [allFrom, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
    · exact allFrom_spec h.1 m hm
    · subst hm
      exact h.2

/-- Masks `0` to `63`. -/
theorem chunk₀ : allFrom 32 0 64 = true := by decide +kernel

/-- Masks `64` to `127`. -/
theorem chunk₁ : allFrom 32 64 64 = true := by decide +kernel

/-- Masks `128` to `191`. -/
theorem chunk₂ : allFrom 32 128 64 = true := by decide +kernel

/-- Masks `192` to `255`. -/
theorem chunk₃ : allFrom 32 192 64 = true := by decide +kernel

/-- **Every Walsh value of `g` is at most `32` in absolute value**: `specLe 32 w` for every
mask `w < 256`. -/
theorem specLe_32 (w : Nat) (hw : w < 256) : specLe 32 w = true := by
  by_cases h₀ : w < 64
  · simpa using allFrom_spec chunk₀ w h₀
  by_cases h₁ : w < 128
  · simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt h₀)] using
      allFrom_spec chunk₁ (w - 64) (by omega)
  by_cases h₂ : w < 192
  · simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt h₁)] using
      allFrom_spec chunk₂ (w - 128) (by omega)
  · simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt h₂)] using
      allFrom_spec chunk₃ (w - 192) (by omega)

/-- `specLe 32 w` in arithmetic form: `256 ≤ 2 · mism w 256 + 32` and `2 · mism w 256 ≤ 288`. -/
theorem spectrum_bound (w : Nat) (hw : w < 256) :
    256 ≤ 2 * mism w 256 + 32 ∧ 2 * mism w 256 ≤ 288 := by
  have h := specLe_32 w hw
  simp only [specLe, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- At the mask `0xac` the count is `112`: `W_g(0xac) = 256 - 224 = 32`. -/
theorem mism_ac : mism 0xac 256 = 112 := by decide +kernel

/-- **Negative control.** With `32` lowered to `28`, the check fails at the mask `0x0c`, where
`mism 0x0c 256 = 112` and `W_g(0x0c) = 32`. -/
theorem specLe_28_false : specLe 28 0x0c = false := by decide +kernel

/-- Not every mask passes the check with `28` in place of `32`. -/
theorem not_forall_specLe_28 : ¬ ∀ w, w < 256 → specLe 28 w = true := fun h => by
  have h12 := h 0x0c (by decide)
  rw [specLe_28_false] at h12
  exact Bool.false_ne_true h12

end Linear.AESSpectrum
