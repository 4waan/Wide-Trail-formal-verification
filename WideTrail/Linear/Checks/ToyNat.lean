/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/

/-!
# The two-bundle toy hull, recomputed on natural numbers

A numerical cross-check of the two-round hull bound on the two-bundle toy of `Checks/Toy.lean`,
over every pair of masks. This file imports nothing; the kernel evaluates a formula on `Nat`
that is written independently of the library's definitions.

The toy (see `Checks/Toy.lean`): two bundles of three bits; in each round the χ map on both
bundles, then `L (x₀, x₁) = (x₀ + x₁, x₀ + α x₁)` with `α` multiplication by `x` in
`GF(8) = F₂[x] / (x³ + x + 1)`. A mask `(m₀, m₁)` is encoded as `m₀ + 8 m₁`. The formula is

`elp u v = ∑_{c < 64} W(u₀, (Lᵀ c)₀)² · W(u₁, (Lᵀ c)₁)² · W(c₀, β₀)² · W(c₁, β₁)²`,
`β = Lᵀ v`,

the right side of `Linear.elpCount_two` for this toy, with `W(a, b)²` the squared Walsh value of
the χ map read from the table `tab` and `Lᵀ` the bit-pairing adjoint of `L`. The table, the
encoding and the identity of this formula with the typed one were computed outside Lean and are
not proved here.

* `all_le`: for every `u` with `1 ≤ u < 64` and every `v < 64`, `elp u v ≤ 2 ^ 20`: the bound of
  `Linear.Checks.toy_two_round_bound`, `elpCount · 8 ^ 4 ≤ 4 ^ 4 · 64 ^ 4`, at all `63 · 64`
  pairs. It is evaluated in eight chunks of input masks (`chunk₀` to `chunk₇`).
* `elp_max`: the value `2 ^ 20` is attained at `u = (7, 7)`, `v = (5, 2)`, where
  `Checks/Toy.lean` proves the typed count equal to `2 ^ 20` (`toy_elp_attained`).
* `not_all_le_pred`: with the bound lowered by one, the check of the last chunk fails; the
  chunks are not vacuous.

## What is not claimed

This is a numerical cross-check, not a proof about the typed definitions: nothing here is linked
by proof to `Linear.elpCount`, and the theorem `Linear.elpCount_two_round_bound` does not depend
on this file. The typed instance of the bound for every pair is `toy_two_round_bound` in
`Checks/Toy.lean`, proved from the theorem.
-/

set_option autoImplicit false

namespace Linear.ToyNat

/-- The squared Walsh values of the 3-bit χ map: byte `8 a + b` holds `W(a, b) ^ 2`. -/
def tab : Nat :=
  (0x1000001000101000000010101010000000100010100010001010101000000000 <<< 256)
    ||| 0x0010100000101000101000001010000010001000100010000000000000000040

/-- `W(a, b) ^ 2` for the 3-bit χ map. -/
def sq (a b : Nat) : Nat := (tab >>> (8 * (8 * a + b))) &&& 255

/-- The parity of the low three bits. -/
def par3 (x : Nat) : Nat := (x &&& 1) ^^^ ((x >>> 1) &&& 1) ^^^ ((x >>> 2) &&& 1)

/-- Multiplication by `α` on three bits. -/
def mulα (x : Nat) : Nat := ((x <<< 1) ^^^ (if x &&& 4 = 0 then 0 else 11)) &&& 7

/-- Its bit-pairing adjoint: bit `i` of `mulαT v` is the parity of `v ∧ mulα 2ⁱ`. -/
def mulαT (v : Nat) : Nat :=
  par3 (v &&& mulα 1) ||| (par3 (v &&& mulα 2) <<< 1) ||| (par3 (v &&& mulα 4) <<< 2)

/-- The term of the trail sum for the middle mask `c = c₀ + 8 c₁`. -/
def term (u₀ u₁ b₀ b₁ c : Nat) : Nat :=
  sq u₀ ((c &&& 7) ^^^ (c >>> 3)) * sq u₁ ((c &&& 7) ^^^ mulαT (c >>> 3))
    * sq (c &&& 7) b₀ * sq (c >>> 3) b₁

/-- The trail sum over the middle masks `c < n`. -/
def elpSum (u₀ u₁ b₀ b₁ : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => elpSum u₀ u₁ b₀ b₁ n + term u₀ u₁ b₀ b₁ n

/-- The two-round count at `u → v`. -/
def elp (u v : Nat) : Nat :=
  elpSum (u &&& 7) (u >>> 3) ((v &&& 7) ^^^ (v >>> 3)) ((v &&& 7) ^^^ mulαT (v >>> 3)) 64

/-- `elp u v ≤ B` for every `v < n`. -/
def okV (B u : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => okV B u n && decide (elp u n ≤ B)

/-- `elp u v ≤ B` for every `v < 64` and every `u` with `lo ≤ u < lo + n`. -/
def okU (B lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => okU B lo n && okV B (lo + n) 64

/-- What `okV` checks. -/
theorem okV_spec (B u n : Nat) (h : okV B u n = true) : ∀ v, v < n → elp u v ≤ B := by
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv
    simp only [okV, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hvn : v = n
    · subst hvn
      exact h.2
    · exact ih h.1 v (by omega)

/-- What `okU` checks. -/
theorem okU_spec (B lo n : Nat) (h : okU B lo n = true) :
    ∀ u, lo ≤ u → u < lo + n → ∀ v, v < 64 → elp u v ≤ B := by
  induction n with
  | zero => intro u h1 h2; omega
  | succ n ih =>
    intro u h1 h2
    simp only [okU, Bool.and_eq_true] at h
    by_cases hun : u = lo + n
    · subst hun
      exact okV_spec B _ 64 h.2
    · exact ih h.1 u h1 (by omega)

/-! ### The eight chunks -/

/-! Each chunk checks eight input masks (seven in the last) against all `64` output masks. -/

theorem chunk₀ : okU 1048576 1 8 = true := by decide +kernel
theorem chunk₁ : okU 1048576 9 8 = true := by decide +kernel
theorem chunk₂ : okU 1048576 17 8 = true := by decide +kernel
theorem chunk₃ : okU 1048576 25 8 = true := by decide +kernel
theorem chunk₄ : okU 1048576 33 8 = true := by decide +kernel
theorem chunk₅ : okU 1048576 41 8 = true := by decide +kernel
theorem chunk₆ : okU 1048576 49 8 = true := by decide +kernel
theorem chunk₇ : okU 1048576 57 7 = true := by decide +kernel

/-- **The bound at every pair.** For every nonzero input mask `u < 64` and every output mask
`v < 64`, `elp u v ≤ 2 ^ 20`. -/
theorem all_le : ∀ u, 1 ≤ u → u < 64 → ∀ v, v < 64 → elp u v ≤ 1048576 := by
  intro u h1 h2
  by_cases h₀ : u < 9
  · exact okU_spec _ 1 8 chunk₀ u h1 (by omega)
  by_cases h₁ : u < 17
  · exact okU_spec _ 9 8 chunk₁ u (by omega) (by omega)
  by_cases h₂ : u < 25
  · exact okU_spec _ 17 8 chunk₂ u (by omega) (by omega)
  by_cases h₃ : u < 33
  · exact okU_spec _ 25 8 chunk₃ u (by omega) (by omega)
  by_cases h₄ : u < 41
  · exact okU_spec _ 33 8 chunk₄ u (by omega) (by omega)
  by_cases h₅ : u < 49
  · exact okU_spec _ 41 8 chunk₅ u (by omega) (by omega)
  by_cases h₆ : u < 57
  · exact okU_spec _ 49 8 chunk₆ u (by omega) (by omega)
  exact okU_spec _ 57 7 chunk₇ u (by omega) (by omega)

/-- **The bound is attained** at `u = (7, 7)`, `v = (5, 2)`. -/
theorem elp_max : elp (7 + 8 * 7) (5 + 8 * 2) = 1048576 := by decide +kernel

/-- **Negative control.** With the bound `2 ^ 20 - 1` the last chunk fails. -/
theorem not_all_le_pred : okU 1048575 57 7 = false := by decide +kernel

end Linear.ToyNat
