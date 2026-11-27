/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Hades
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Prime fields: the standard character and the norm forms

The generic layer (`Character.lean`, `Hades.lean`) works with any character `ψ : AddChar G R`
into a domain and any absolute value on `R`. For a state over the prime field `ZMod p`, the
intended choices are the multiplication pairing `⟨u, x⟩ = u * x` (`Linear.mulPairing`, the trace
form of the identity; on states its bundle sum is the dot product), the standard character
`ZMod.stdAddChar : AddChar (ZMod p) ℂ`, `j ↦ exp (2πi j / p)`, and the norm of `ℂ`. This file
discharges the hypotheses of the generic results for these choices and states the HADES results
in norm form.

This is the only module of this library that imports `Mathlib.Analysis` (for `ZMod.stdAddChar`
and the norm of `ℂ`; about 3.4 GB of memory to elaborate, almost all of it that import). No module
with results imports it: only the aggregator `WideTrail.Linear` does, so that the library root
reaches it, and the aggregator and the root then load `Mathlib.Analysis` as well (about 3.5 GB
each). `Linear/Hades.lean`, `Linear/Poseidon2.lean` and `Linear/Poseidon.lean` state their
results for every separating character and absolute value; with the facts below they apply to
`ZMod.stdAddChar` and the norm.

## What is proved

* `normAbv`, `normAbv_apply`: the norm of `ℂ` as an `AbsoluteValue ℂ ℝ`.
* `norm_stdAddChar`, `normAbv_stdAddChar`: every value of `ZMod.stdAddChar` has norm `1`.
* `mulPairing_separating`: for a prime `p`, the multiplication pairing of `ZMod p` is separating
  for `ZMod.stdAddChar` (the character is injective, so `stdAddChar 1 ≠ 1`); hence so is the dot
  product of states (`Pairing.Separating.pi`).
* `natCast_card_ne_zero`: the size of a nonempty finite type is nonzero in `ℂ`, the hypothesis of
  `isLinBranchBound_iff` and `Hades.isLinBranchBound_iff_maskLin`.
* `norm_walsh_le_card`: `‖walsh‖ ≤ |X|`.
* For HADES rounds over `ZMod p`, with `ψ = ZMod.stdAddChar` and the dot product:
  `Hades.isTrail_of_linCorr_ne_zero_std` (the bridge), `Hades.walsh_execute_eq_sum_linCorr_std`
  (the permutation's Walsh value as the sum of its trail correlations),
  `Hades.isLinBranchBound_iff_maskLin_std` (the linear branch number of a layer is the branch
  number of its forward mask map), `Hades.norm_linCorr_le`,
  `Hades.norm_linCorr_mul_pow_le_of_le` and `Hades.hades_linear_bound_norm` (the trail bounds in
  norm form, with the S-box correlation bound `c` a hypothesis).

## What is not claimed

No bound on any Walsh value of a power map `x ↦ x ^ d` over `ZMod p` is proved: the Weil bound
`(d - 1) √p` is the Riemann hypothesis for curves over finite fields and is out of reach here,
and the S-box bound `c` of the trail bounds stays a hypothesis. A trail bound bounds one trail,
one summand of `Hades.walsh_execute_eq_sum_linCorr_std`; it is not a bound on the correlation of
the permutation, which is the sum of those summands. Linear hulls over `ZMod p` (key-averaged
squared correlations in `ℂ`) are not treated.
-/

set_option autoImplicit false

namespace Linear

/-- **The norm of `ℂ` as an absolute value.** -/
noncomputable def normAbv : AbsoluteValue ℂ ℝ :=
  IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)

@[simp] theorem normAbv_apply (z : ℂ) : normAbv z = ‖z‖ :=
  rfl

/-- The size of a nonempty finite type is nonzero in `ℂ`. -/
theorem natCast_card_ne_zero (X : Type*) [Fintype X] [Nonempty X] :
    (Fintype.card X : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

variable (p : ℕ) [Fact p.Prime]

/-- **Every value of the standard character has norm `1`.** -/
theorem norm_stdAddChar (t : ZMod p) : ‖ZMod.stdAddChar t‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The same through `normAbv`. -/
theorem normAbv_stdAddChar (t : ZMod p) : normAbv (ZMod.stdAddChar t) = 1 :=
  norm_stdAddChar p t

/-- **The multiplication pairing of `ZMod p` is separating for the standard character.** The
character is injective (`ZMod.injective_stdAddChar`), so `stdAddChar 1 ≠ stdAddChar 0 = 1`, and
a trace-form pairing on a field is separating as soon as one value of `ψ ∘ ℓ` differs from `1`
(`Pairing.traceForm_separating`). -/
theorem mulPairing_separating :
    (mulPairing (ZMod p)).Separating (ZMod.stdAddChar (N := p)) := by
  refine Pairing.traceForm_separating (AddMonoidHom.id (ZMod p)) (t := 1) ?_
  intro h
  have h1 : ZMod.stdAddChar (N := p) 1 = ZMod.stdAddChar (N := p) 0 := by
    rw [AddChar.map_zero_eq_one]
    exact h
  exact one_ne_zero (ZMod.injective_stdAddChar h1)

/-- **A Walsh value has norm at most `|X|`**, for the standard character. -/
theorem norm_walsh_le_card {X Y : Type*} [AddCommGroup X] [Fintype X] [AddCommGroup Y]
    (P : Pairing X (ZMod p)) (Q : Pairing Y (ZMod p)) (F : X → Y) (u : X) (v : Y) :
    ‖walsh ZMod.stdAddChar P Q F u v‖ ≤ Fintype.card X :=
  abv_walsh_le_card normAbv (normAbv_stdAddChar p) P Q F u v

end Linear

namespace Hades

open Linear
open scoped Matrix

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {p : ℕ} [Fact p.Prime]

/-- **The bridge over `ZMod p`.** For the standard character and the dot product, a linear trail
of HADES rounds with a nonzero correlation is a `Hades.IsTrail` of the mask schedule. -/
theorem isTrail_of_linCorr_ne_zero_std (rounds : ℕ → RoundSpec Idx (ZMod p)) {r : ℕ}
    {T : ℕ → Idx → ZMod p}
    (h : linCorr ZMod.stdAddChar (AddMonoidHom.id (ZMod p)) rounds r T ≠ 0) :
    IsTrail (maskSchedule rounds) T r :=
  isTrail_of_linCorr_ne_zero (mulPairing_separating p) rounds h

/-- **The permutation's Walsh value over `ZMod p`.** For the standard character and the dot
product, `p ^ (|Idx| r) · walsh (r + 1 rounds) u v = ∑_d linCorr T_d` over the trails
`T_d = throughTrail u d v` from `u` to `v`, with the fixed constants of `rounds` and no key
(`walsh_execute_eq_sum_linCorr`). -/
theorem walsh_execute_eq_sum_linCorr_std (rounds : ℕ → RoundSpec Idx (ZMod p)) (r : ℕ)
    (u v : Idx → ZMod p) :
    (Fintype.card (Idx → ZMod p) : ℂ) ^ r *
        walsh ZMod.stdAddChar (mulPairing (ZMod p)).pi (mulPairing (ZMod p)).pi
          (fun x => execute rounds x (r + 1)) u v
      = ∑ d : Fin r → Idx → ZMod p, linCorr ZMod.stdAddChar (AddMonoidHom.id (ZMod p)) rounds
          (r + 1) (Scheduled.throughTrail u d v) :=
  walsh_execute_eq_sum_linCorr (mulPairing_separating p) rounds r u v

/-- **The linear branch number over `ZMod p`.** For the standard character and the dot product,
`B` is a linear branch-number lower bound for `L` (through correlations) exactly when it is a
branch-number lower bound for the forward mask map `maskLin L`. -/
theorem isLinBranchBound_iff_maskLin_std (L : (Idx → ZMod p) ≃ₗ[ZMod p] (Idx → ZMod p))
    (B : ℕ) :
    IsLinBranchBound ZMod.stdAddChar (mulPairing (ZMod p)) L B ↔
      isBranchBound id (maskLin L) B :=
  isLinBranchBound_iff_maskLin (mulPairing_separating p) (natCast_card_ne_zero _) L B

/-- **The trail bound in norm form.** For the standard character and the dot product, if every
S-box that the masks of the first `r` rounds charge has Walsh values of norm at most `c` at every
nonzero input mask (a hypothesis), then
`‖linCorr‖ ≤ c ^ W · p ^ (r · |Idx| - W)` with `W = scheduledWeight rounds T 0 r`. -/
theorem norm_linCorr_le (rounds : ℕ → RoundSpec Idx (ZMod p)) (r : ℕ) {c : ℝ}
    (hc : ∀ n < r, ∀ i ∈ (rounds n).mask, ∀ a : ZMod p, a ≠ 0 → ∀ b : ZMod p,
      ‖walsh ZMod.stdAddChar (mulPairing (ZMod p)) (mulPairing (ZMod p)) ((rounds n).sbox i) a b‖
        ≤ c)
    (T : ℕ → Idx → ZMod p) :
    ‖linCorr ZMod.stdAddChar (AddMonoidHom.id (ZMod p)) rounds r T‖ ≤
      c ^ scheduledWeight rounds T 0 r *
        (p : ℝ) ^ (r * Fintype.card Idx - scheduledWeight rounds T 0 r) := by
  have h := abv_linCorr_le normAbv (normAbv_stdAddChar p) rounds r hc T
  rwa [ZMod.card] at h

/-- **The exact ratio in norm form.** Under the hypotheses of `norm_linCorr_le`, with `c ≥ 0`,
for every `A ≤ scheduledWeight rounds T 0 r`:
`‖linCorr‖ · p ^ A ≤ c ^ A · (p ^ |Idx|) ^ r`. Divided by `(p ^ |Idx|) ^ r`, the trail's
correlation has norm at most `(c / p) ^ A`. No relation between `c` and `p` is assumed. -/
theorem norm_linCorr_mul_pow_le_of_le (rounds : ℕ → RoundSpec Idx (ZMod p)) (r : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c)
    (hc : ∀ n < r, ∀ i ∈ (rounds n).mask, ∀ a : ZMod p, a ≠ 0 → ∀ b : ZMod p,
      ‖walsh ZMod.stdAddChar (mulPairing (ZMod p)) (mulPairing (ZMod p)) ((rounds n).sbox i) a b‖
        ≤ c)
    (T : ℕ → Idx → ZMod p) {A : ℕ} (hA : A ≤ scheduledWeight rounds T 0 r) :
    ‖linCorr ZMod.stdAddChar (AddMonoidHom.id (ZMod p)) rounds r T‖ * (p : ℝ) ^ A ≤
      c ^ A * ((p : ℝ) ^ Fintype.card Idx) ^ r := by
  have h := abv_linCorr_mul_card_pow_le_of_le normAbv (normAbv_stdAddChar p) hc0 rounds r hc T hA
  rwa [Fintype.card_fun, ZMod.card, Nat.cast_pow] at h

/-- **The linear trail bound of a HADES schedule in norm form.** For the standard character and
the dot product over `ZMod p`, under the branch and middle-bound hypotheses of
`hades_linear_activity` for the forward mask maps, and an S-box correlation bound `c ≥ 0` in
norm (a hypothesis), every linear trail through the `r + m + s` rounds with a nonzero input mask
satisfies `‖linCorr‖ · p ^ N ≤ c ^ N · (p ^ |Idx|) ^ (r + m + s)` with
`N = (r / 2 + s / 2) · B + r % 2 + s % 2 + μ`. One trail: not the correlation of the
permutation. -/
theorem hades_linear_bound_norm (r m s B μ : ℕ) (mask : Finset Idx)
    (boxes : ℕ → Idx → ZMod p ≃ ZMod p)
    (linear : ℕ → (Idx → ZMod p) ≃ₗ[ZMod p] (Idx → ZMod p)) (values : ℕ → Idx → ZMod p)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ n < r + m + s, ∀ i, ∀ a : ZMod p, a ≠ 0 → ∀ b : ZMod p,
      ‖walsh ZMod.stdAddChar (mulPairing (ZMod p)) (mulPairing (ZMod p)) (boxes n i) a b‖ ≤ c)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (maskLin (linear j)) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (maskLin (linear (r + m + j))) B)
    (A : Module.End (ZMod p) (Idx → ZMod p))
    (hmid : ∀ j < m,
      ((maskLin (linear (r + j))).toLinearMap : Module.End (ZMod p) (Idx → ZMod p)) = A)
    (hμ : MiddleBound A mask m μ) {T : ℕ → Idx → ZMod p} (h0 : T 0 ≠ 0) :
    ‖linCorr ZMod.stdAddChar (AddMonoidHom.id (ZMod p))
        (hadesSchedule r m s mask boxes linear values) (r + m + s) T‖ *
        (p : ℝ) ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + μ) ≤
      c ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + μ) *
        ((p : ℝ) ^ Fintype.card Idx) ^ (r + m + s) := by
  have h := hades_linear_bound normAbv (normAbv_stdAddChar p) (mulPairing_separating p) r m s B μ
    mask boxes linear values hc0 hc hbp hbs A hmid hμ h0
  rwa [Fintype.card_fun, ZMod.card, Nat.cast_pow] at h

end Hades
