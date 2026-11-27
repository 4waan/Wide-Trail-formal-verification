/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Hades
import WideTrail.Poseidon.StarknetMiddle

/-!
# Linear activity of Starknet's Poseidon permutation

Starknet's Poseidon (HADES) permutation over the STARK field, width `3`, S-box `x³`, `4 + 83 + 4`
rounds, the same layer `M = [[3, 1, 1], [1, -1, 1], [1, 1, -2]]` in every round, the partial
rounds with the S-box on coordinate `2`, and no linear layer before round `0`
(`WideTrail.Poseidon.Starknet`). The pairing is the dot product read through any `ℓ : F →+ G`,
and the character `ψ : AddChar G R` is any character into a domain for which it is separating
(`Field.lean` supplies `ZMod.stdAddChar` with `ℓ = id`). Masks move forward through
`maskLin M = (Mᵀ)⁻¹` (`WideTrail.Linear.Hades`).

## Results

* `mds_selfAdjoint`, `maskLin_mds`: `M` is symmetric (`mdsMatrix_transpose`), so it moves masks
  by its inverse, `maskLin M = M⁻¹`. `maskLin_mds_isBranchBound`: the forward mask map has branch
  number at least `4` (`M` is MDS, `Hades.isBranchBound_maskLin_of_isMDS`);
  `mds_isLinBranchBound`: for a separating `ψ` into a domain in which `|F ^ 3|` is nonzero, `M`
  has linear branch number (through correlations) at least `4`.
* `maskLin_mds_inactive_trivial`, `maskLin_middle_bound`: the window `3` of `mds_inactive_trivial`
  and the automaton middle bound `41` of `middle_bound` hold for the forward mask map `M⁻¹`
  (`Hades.inactiveSpace_symm_eq_bot_iff`, `Hades.MiddleBound.symm`).
* `linear_activity_general`, `linear_activity_middle_general`, `linear_activity_middle`: every
  linear trail through the `91` rounds with a nonzero input mask and a nonzero correlation
  (`Hades.linCorr`), for every table of round constants, charges at least `43` S-boxes
  (`16 + 83 / 3`) and at least `57` (`16 + 41`): the same lower bounds as the differential counts
  `activity_with_partial_general` and `activity_middle_general`.
* `linear_bound_middle_general`: for an absolute value `abv` with `abv (ψ t) = 1` and an S-box
  whose Walsh values at every nonzero input mask are at most `C` under `abv` (**a hypothesis**),
  every such trail has `abv (linCorr) · p ^ 57 ≤ C ^ 57 · |F ^ 3| ^ 91`.
* `walsh_permutation_eq_sum_linCorr`: since there is no linear layer before round `0`, the Walsh
  value of the permutation with its pinned constants is the sum of the trail correlations:
  `|F ^ 3| ^ 90 · walsh permutation u v = ∑_d linCorr T_d` over the trails `T_d` from `u` to `v`
  (`Hades.walsh_execute_eq_sum_linCorr`).

## What is not claimed

The counts are lower bounds on charged S-boxes in the `IsTrail` model; they are not claimed to be
attained, and no statement is made about trails with a zero correlation. A trail bound bounds one
trail, one summand of `walsh_permutation_eq_sum_linCorr`; it is not a bound on the correlation of
the permutation, which is the sum of those summands, and they can reinforce or cancel. The S-box
correlation bound `C` is a hypothesis: the Weil bound `2 √p` for `x ↦ x³` is not proved in this
library. No instance file is changed.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

open Linear
open scoped Matrix

namespace Poseidon.Starknet

/-- `M` is self-adjoint: `mds x ⬝ᵥ y = x ⬝ᵥ mds y` (`mdsMatrix_transpose`). -/
theorem mds_selfAdjoint (x y : State) : mds x ⬝ᵥ y = x ⬝ᵥ mds y :=
  Hades.selfAdjoint_of_mulVec mds_eq_mulVec mdsMatrix_transpose x y

/-- **`M` moves masks by its inverse**: `maskLin M = M⁻¹`. -/
theorem maskLin_mds : Hades.maskLin mds = mds.symm :=
  Hades.maskLin_eq_symm_of_selfAdjoint mds mds_selfAdjoint

/-- **Branch number `4` for the forward mask map** (`M` is MDS). -/
theorem maskLin_mds_isBranchBound : isBranchBound id (Hades.maskLin mds) 4 :=
  Hades.isBranchBound_maskLin_of_isMDS mds_isMDS mds mds_eq_mulVec

/-- **No nonzero mask stays off the S-box coordinate through three partial rounds of the forward
mask map**: `mds_inactive_trivial` for `M⁻¹` (`Hades.inactiveSpace_symm_eq_bot_iff`). -/
theorem maskLin_mds_inactive_trivial :
    Hades.inactiveSpace (Hades.maskLin mds).toLinearMap ({2} : Finset (Fin 3)) 3 = ⊥ := by
  rw [maskLin_mds, Hades.inactiveSpace_symm_eq_bot_iff]
  exact mds_inactive_trivial

/-- **The middle bound `41` for the forward mask map**: `middle_bound`, transferred to `M⁻¹`
(`Hades.MiddleBound.maskLin_of_selfAdjoint`). -/
theorem maskLin_middle_bound :
    Hades.MiddleBound (Hades.maskLin mds).toLinearMap ({2} : Finset (Fin 3)) 83 41 :=
  Hades.MiddleBound.maskLin_of_selfAdjoint mds_selfAdjoint middle_bound

variable {G R S : Type*} [AddCommGroup G] [CommRing R] [IsDomain R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : F →+ G}

/-- **Linear branch number `4`** for `M`: for a pairing `ℓ (u ⬝ᵥ x)` separating for `ψ`, into a
domain in which `|F ^ 3|` is nonzero, every pair of masks `(u, v) ≠ (0, 0)` at which `M` has a
nonzero Walsh value has at least `4` nonzero coordinates in total. -/
theorem mds_isLinBranchBound (hP : (Pairing.traceForm ℓ).Separating ψ)
    (hcard : (Fintype.card (Fin 3 → F) : R) ≠ 0) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) mds 4 :=
  (Hades.isLinBranchBound_iff_maskLin hP hcard mds 4).mpr maskLin_mds_isBranchBound

/-- **Forty-three active S-boxes for masks, for every round-constant table.** Every linear trail
through the `91` rounds with a nonzero input mask and a nonzero correlation charges at least
`43` S-boxes: `16` in the full rounds and `83 / 3 = 27` in the partial rounds, one per window of
three (`maskLin_mds_inactive_trivial`). The count of `activity_with_partial_general`, for masks.
A lower bound. -/
theorem linear_activity_general (hP : (Pairing.traceForm ℓ).Separating ψ) (table : ℕ → State)
    {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ
      (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) 91 T ≠ 0) :
    43 ≤ Hades.scheduledWeight
      (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) T 0 91 :=
  Hades.hades_linear_activity hP 4 83 4 4 (83 / 3) {2} (fun _ _ => sbox) (fun _ => mds) table
    (fun _ _ => maskLin_mds_isBranchBound) (fun _ _ => maskLin_mds_isBranchBound)
    (Hades.maskLin mds).toLinearMap (fun _ _ => rfl)
    (Hades.MiddleBound.of_inactiveSpace maskLin_mds_inactive_trivial 83) h0 h

/-- **Fifty-seven active S-boxes for masks, for every round-constant table**: `16` in the full
rounds and `41` in the partial rounds, from the automaton certificate `middle_bound` transferred
to the forward mask map (`maskLin_middle_bound`). The count of `activity_middle_general`, for
masks. A lower bound. -/
theorem linear_activity_middle_general (hP : (Pairing.traceForm ℓ).Separating ψ)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0)
    (h : Hades.linCorr ψ ℓ
      (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) 91 T ≠ 0) :
    57 ≤ Hades.scheduledWeight
      (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) T 0 91 :=
  Hades.hades_linear_activity hP 4 83 4 4 41 {2} (fun _ _ => sbox) (fun _ => mds) table
    (fun _ _ => maskLin_mds_isBranchBound) (fun _ _ => maskLin_mds_isBranchBound)
    (Hades.maskLin mds).toLinearMap (fun _ _ => rfl) maskLin_middle_bound h0 h

/-- **Fifty-seven active S-boxes for masks** for the pinned rounds. -/
theorem linear_activity_middle (hP : (Pairing.traceForm ℓ).Separating ψ) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (h : Hades.linCorr ψ ℓ rounds 91 T ≠ 0) :
    57 ≤ Hades.scheduledWeight rounds T 0 91 :=
  linear_activity_middle_general hP values h0 h

/-- **The linear trail bound, for every round-constant table**: under an S-box correlation
bound `C ≥ 0` for `x ↦ x³` (a hypothesis), every linear trail through the `91` rounds with a
nonzero input mask has `abv (linCorr) · p ^ 57 ≤ C ^ 57 · |F ^ 3| ^ 91`. One trail: one summand
of `walsh_permutation_eq_sum_linCorr`, not the correlation of the permutation. -/
theorem linear_bound_middle_general (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) {C : S} (hC0 : 0 ≤ C)
    (hC : ∀ a : F, a ≠ 0 → ∀ b : F,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) sbox a b) ≤ C)
    (table : ℕ → State) {T : ℕ → State} (h0 : T 0 ≠ 0) :
    abv (Hades.linCorr ψ ℓ
        (Hades.hadesSchedule 4 83 4 {2} (fun _ _ => sbox) (fun _ => mds) table) 91 T) *
        (modulus : S) ^ 57 ≤ C ^ 57 * (Fintype.card (Fin 3 → F) : S) ^ 91 := by
  have h := Hades.hades_linear_bound abv hψ hP 4 83 4 4 41 {2} (fun _ _ => sbox) (fun _ => mds)
    table hC0 (fun _ _ _ => hC) (fun _ _ => maskLin_mds_isBranchBound)
    (fun _ _ => maskLin_mds_isBranchBound) (Hades.maskLin mds).toLinearMap (fun _ _ => rfl)
    maskLin_middle_bound h0
  rwa [field_card] at h

/-- **The permutation's Walsh value is the sum of its trail correlations.** With no linear layer
before round `0`, for the pinned round constants and with no key,
`|F ^ 3| ^ 90 · walsh permutation u v = ∑_d linCorr rounds 91 T_d` over the trails
`T_d = Scheduled.throughTrail u d v` from `u` to `v`, one for each choice of the `90` intermediate
masks. The summands can reinforce or cancel. -/
theorem walsh_permutation_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (u v : State) :
    (Fintype.card (Fin 3 → F) : R) ^ 90 *
        walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi permutation u v =
      ∑ d : Fin 90 → State, Hades.linCorr ψ ℓ rounds 91 (Scheduled.throughTrail u d v) :=
  Hades.walsh_execute_eq_sum_linCorr hP rounds 90 u v

end Poseidon.Starknet
