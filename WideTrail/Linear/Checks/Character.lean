/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Binary

/-!
# The character identities against a map the kernel can enumerate

`Character.lean` and `Binary.lean` prove identities for every finite state space. This file
takes the smallest interesting one, three bits `Fin 3 → ZMod 2` with the bit pairing
`bitPairing (Fin 3)` and the sign character `sign₂`, and makes the kernel recompute both sides
of three of them by brute force for the 3-bit map

`chi3 x = fun i => x i + (x (i + 1) + 1) * x (i + 2)`,

the χ map of Keccak on three bits, a bijection (`chi3_bijective`) whose Walsh values at nonzero
input masks are at most `4` in absolute value (`chi3_isLinearityBound`); the bound `2` fails
(`chi3_not_isLinearityBound_two`).

* (W1) `toy_addKey`: for every key `k` and masks `u, v`, adding `k` before `chi3` multiplies the
  Walsh value by `sign₂ ⟨u, k⟩`. Both sides are evaluated for all `8³` triples.
* (W6) `toy_comp`: for all masks `u, w`,
  `8 · walsh (chi3 ∘ chi3) u w = ∑ᵥ walsh chi3 u v · walsh chi3 v w`.
* (W9) `toy_parseval_left`, `toy_parseval_right`: every column and every row of the squared Walsh
  values of `chi3` sums to `64 = 8²`.

Two negative controls show that the hypotheses of the theorems are used.

* **Injectivity is needed for rows only.** `andNext x = fun i => x i * x (i + 1)` is not
  injective. Its columns still sum to `64` (`toy_and_parseval_left`), and one of its rows does
  not (`toy_and_parseval_right_fails`).
* **Separation is needed for (W6).** The zero pairing `zeroPairing`, `⟨u, x⟩ = 0`, is not
  separating (`zeroPairing_not_separating`). With it every Walsh value is `8`, and the identity
  of (W6) fails: `8 · 8 = 64` against `8 · 8 · 8 = 512` (`toy_comp_fails_zeroPairing`).

These are numerical cross-checks of the identities on one instance, computed independently of
their proofs. They are not a proof of anything beyond the stated instances.
-/

set_option autoImplicit false

namespace Linear.Checks

/-- Three bits. -/
abbrev Bits3 := Fin 3 → ZMod 2

/-- The χ map on three bits: `yᵢ = xᵢ + (xᵢ₊₁ + 1) · xᵢ₊₂`, indices mod `3`. -/
def chi3 (x : Bits3) : Bits3 := fun i => x i + (x (i + 1) + 1) * x (i + 2)

/-- A non-injective map: `yᵢ = xᵢ · xᵢ₊₁`. -/
def andNext (x : Bits3) : Bits3 := fun i => x i * x (i + 1)

/-- The bit pairing of three bits. -/
abbrev B3 : Pairing Bits3 (ZMod 2) := bitPairing (Fin 3)

theorem chi3_bijective : Function.Bijective chi3 := by decide +kernel

/-- Every Walsh value of `chi3` at a nonzero input mask is at most `4` in absolute value (out of
a possible `8`). -/
theorem chi3_isLinearityBound : IsLinearityBound B3 chi3 4 := by decide +kernel

/-- The bound `2` fails: some Walsh value of `chi3` at a nonzero input mask exceeds `2` in
absolute value. -/
theorem chi3_not_isLinearityBound_two : ¬ IsLinearityBound B3 chi3 2 := by decide +kernel

theorem andNext_not_injective : ¬ Function.Injective andNext := by decide +kernel

/-! ### (W1), (W6), (W9) by enumeration -/

/-- (W1) for `chi3`, all keys and masks. -/
theorem toy_addKey : ∀ k u v : Bits3,
    walsh sign₂ B3 B3 (fun x => chi3 (x + k)) u v
      = sign₂ (B3.dot u k) * walsh sign₂ B3 B3 chi3 u v := by
  decide +kernel

/-- (W6) for `chi3 ∘ chi3`, all masks. -/
theorem toy_comp : ∀ u w : Bits3,
    (8 : ℤ) * walsh sign₂ B3 B3 (fun x => chi3 (chi3 x)) u w
      = ∑ v, walsh sign₂ B3 B3 chi3 u v * walsh sign₂ B3 B3 chi3 v w := by
  decide +kernel

/-- (W9), columns, for `chi3`. -/
theorem toy_parseval_left : ∀ v : Bits3, ∑ u, walsh sign₂ B3 B3 chi3 u v ^ 2 = 64 := by
  decide +kernel

/-- (W9), rows, for `chi3`, which is injective. -/
theorem toy_parseval_right : ∀ u : Bits3, ∑ v, walsh sign₂ B3 B3 chi3 u v ^ 2 = 64 := by
  decide +kernel

/-! ### Negative controls -/

/-- Columns sum to `64` for the non-injective `andNext` too. -/
theorem toy_and_parseval_left : ∀ v : Bits3, ∑ u, walsh sign₂ B3 B3 andNext u v ^ 2 = 64 := by
  decide +kernel

/-- Rows need injectivity: a row of `andNext` does not sum to `64`. -/
theorem toy_and_parseval_right_fails :
    ¬ ∀ u : Bits3, ∑ v, walsh sign₂ B3 B3 andNext u v ^ 2 = 64 := by
  decide +kernel

/-- The degenerate pairing `⟨u, x⟩ = 0`. -/
def zeroPairing : Pairing Bits3 (ZMod 2) := ⟨0⟩

theorem zeroPairing_not_separating : ¬ zeroPairing.Separating sign₂ := fun h => by
  obtain ⟨x, hx⟩ := h.left (fun _ => 1) (by decide)
  exact hx rfl

/-- (W6) fails for the degenerate pairing: `64 ≠ 512`. -/
theorem toy_comp_fails_zeroPairing :
    (8 : ℤ) * walsh sign₂ zeroPairing zeroPairing (fun x => chi3 (chi3 x)) 0 0
      ≠ ∑ v, walsh sign₂ zeroPairing zeroPairing chi3 0 v
          * walsh sign₂ zeroPairing zeroPairing chi3 v 0 := by
  decide +kernel

end Linear.Checks
