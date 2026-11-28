/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Hades
import WideTrail.Poseidon2.BN254

/-!
# Checks for the linear trails of HADES rounds

Controls for `Linear/Hades.lean` and the instance files `Linear/Poseidon2.lean` and
`Linear/Poseidon.lean`:

* `trivial_not_separating`, `walsh_masked_needs_separation`: over `ZMod 2`, the trivial character
  is not separating for the multiplication pairing, and with it the identity of `walsh_masked`
  fails: the masked layer with the empty mask has Walsh value `2` at the masks `(0, 1)`, while the
  right-hand side is `0`. So the separation hypothesis of `Hades.walsh_masked` is needed.
* `bridge_needs_separation`: with the same trivial character, a one-round trail over `ZMod 2`
  whose mask becomes `0` has trail correlation `2 ≠ 0` but is not a `Hades.IsTrail` of the mask
  schedule. So the separation hypothesis of `Hades.isTrail_of_linCorr_ne_zero` is needed.
* `linCorr_zero_trail`, `linCorr_zero_trail_ne_zero`, `scheduledWeight_zero_trail`: for every
  pairing, character and schedule, the zero trail has correlation `|Idx → K| ^ r` (nonzero when
  `|Idx → K|` is nonzero in `R`) and charges no S-box. So the hypothesis `T 0 ≠ 0` of every linear
  activity bound (`Hades.hades_linear_activity` and the instance theorems, whose counts are
  positive) is needed.
* `BN254.maskLin_external_ne`: the forward mask map of the BN254 width-three external layer is
  not the layer itself (`circ(2, 1, 1)` applied twice to `e₀` gives `(6, 5, 5)`), so masks and
  differences do not move through the same maps; the linear activity results are about the mask
  schedule `Hades.maskSchedule`, not the state schedule.

## What is not claimed

These are checks of hypotheses on small examples and of one value. They do not evaluate any
correlation of a Poseidon or Poseidon2 permutation, and they do not show that any linear activity
count is attained.
-/

set_option autoImplicit false

namespace Linear.Checks

open Hades

/-! ### Separation is needed -/

/-- The trivial character of `ZMod 2` is not separating for the multiplication pairing. -/
theorem trivial_not_separating :
    ¬ (mulPairing (ZMod 2)).Separating (1 : AddChar (ZMod 2) ℤ) := fun h => by
  obtain ⟨x, hx⟩ := h.left 1 one_ne_zero
  exact hx (AddChar.one_apply _)

/-- **`walsh_masked` fails without separation.** With the trivial character, the masked layer
with the empty mask on `Fin 1 → ZMod 2` has Walsh value `2` at the masks `(0, 1)`, while the
right-hand side of `Hades.walsh_masked` is `0`. -/
theorem walsh_masked_needs_separation :
    walsh (1 : AddChar (ZMod 2) ℤ) (mulPairing (ZMod 2)).pi (mulPairing (ZMod 2)).pi
        (maskedBricklayer (∅ : Finset (Fin 1)) (fun _ => id)) 0 (fun _ => 1) = 2 ∧
      (∏ i : Fin 1, if i ∈ (∅ : Finset (Fin 1)) then
          walsh (1 : AddChar (ZMod 2) ℤ) (mulPairing (ZMod 2)) (mulPairing (ZMod 2)) id
            ((0 : Fin 1 → ZMod 2) i) ((fun _ => (1 : ZMod 2)) i)
        else if (0 : Fin 1 → ZMod 2) i = (fun _ => (1 : ZMod 2)) i then
          (Fintype.card (ZMod 2) : ℤ) else 0) = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [walsh, AddChar.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one]
    norm_num
  · simp

/-- **The bridge fails without separation.** With the trivial character over `ZMod 2`, the
one-round trail `(1, 0)` through a round with mask `{0}`, the identity S-box and the identity
layer has trail correlation `2 ≠ 0`, but it is not a `Hades.IsTrail` of the mask schedule: the
mask `1` would have to become `0` through an equivalence. -/
theorem bridge_needs_separation :
    let rounds : ℕ → RoundSpec (Fin 1) (ZMod 2) :=
      fun _ => ⟨{0}, fun _ => Equiv.refl _, LinearEquiv.refl _ _, 0⟩
    let T : ℕ → Fin 1 → ZMod 2 := fun n => if n = 0 then fun _ => 1 else 0
    linCorr (1 : AddChar (ZMod 2) ℤ) (AddMonoidHom.id (ZMod 2)) rounds 1 T = 2 ∧
      ¬ IsTrail (maskSchedule rounds) T 1 := by
  intro rounds T
  refine ⟨?_, fun h => ?_⟩
  · simp only [linCorr, trailCorr, Finset.prod_range_one, walsh, AddChar.one_apply,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      nsmul_eq_mul, mul_one]
    norm_num
  · obtain ⟨b, hb, hl, _⟩ := h 0 (by norm_num)
    have hT1 : T 1 = 0 := by simp [T]
    have hb0 : b = 0 := (maskLin (rounds 0).lin).injective (by rw [map_zero]; exact hl.trans hT1)
    have hsupp : activePattern (T 0) = ∅ := by rw [← hb, hb0, activePattern_eq_empty]
    rw [activePattern_eq_empty] at hsupp
    have h0 := congrFun hsupp 0
    simp [T] at h0

/-! ### The nonzero input mask is needed -/

variable {Idx K G R : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [Fintype K]
  [AddCommGroup G] [CommRing R]

/-- **The zero trail has correlation `|Idx → K| ^ r`**, for every pairing `ℓ (u ⬝ᵥ x)`, every
character and every schedule: every factor is the Walsh value at the zero masks. -/
theorem linCorr_zero_trail (ψ : AddChar G R) (ℓ : K →+ G) (rounds : ℕ → RoundSpec Idx K)
    (r : ℕ) : linCorr ψ ℓ rounds r 0 = (Fintype.card (Idx → K) : R) ^ r := by
  rw [linCorr, trailCorr]
  simp only [Pi.zero_apply, map_zero]
  rw [Finset.prod_congr rfl fun n _ => walsh_zero_zero ψ _ _ _, Finset.prod_const,
    Finset.card_range]

/-- The zero trail has a nonzero correlation whenever `|Idx → K|` is nonzero in `R`. -/
theorem linCorr_zero_trail_ne_zero [IsDomain R] (ψ : AddChar G R) (ℓ : K →+ G)
    (rounds : ℕ → RoundSpec Idx K) (r : ℕ) (hcard : (Fintype.card (Idx → K) : R) ≠ 0) :
    linCorr ψ ℓ rounds r 0 ≠ 0 := by
  rw [linCorr_zero_trail]
  exact pow_ne_zero r hcard

omit [Fintype K] in
/-- The zero trail charges no S-box. -/
theorem scheduledWeight_zero_trail [DecidableEq K] (rounds : ℕ → RoundSpec Idx K) (s l : ℕ) :
    scheduledWeight rounds 0 s l = 0 := by
  simp [scheduledWeight, sboxWeight, activeSboxes, activePattern_eq_empty.mpr rfl]

end Linear.Checks

/-! ### Masks and differences move through different maps -/

namespace Poseidon2.BN254

/-- **The forward mask map of the external layer is not the layer.** `maskLin external` is
`external⁻¹` (`circ(2, 1, 1)` is symmetric); if it were `external`, then `external` applied twice
would fix `e₀`, but it sends `e₀` to `(6, 5, 5)`. -/
theorem maskLin_external_ne : Hades.maskLin external ≠ external := by
  intro h
  have hm : Hades.maskLin external = external.symm :=
    Hades.maskLin_eq_symm_of_selfAdjoint external fun x y =>
      Hades.selfAdjoint_of_mulVec external_eq_mulVec (by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl) x y
  have hsymm : external.symm = external := hm.symm.trans h
  have h2 := congrArg (fun L : State ≃ₗ[F] State => L (external (Pi.single 0 1)) 0) hsymm
  simp only [LinearEquiv.symm_apply_apply] at h2
  revert h2
  decide

end Poseidon2.BN254
