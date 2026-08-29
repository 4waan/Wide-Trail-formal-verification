/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer3.TrailProb
import Mathlib.Data.ZMod.Basic

/-!
# Layer 3 against a cipher the kernel can enumerate

Everything in Layer 3 is a count, so everything in Layer 3 is decidable on a small enough
cipher. This file takes a two-bundle state over `ZMod 4`, sixteen states in all, and makes
the kernel recompute by brute force what the theorems derive.

The cipher: `sb` swaps `2` and `3` and fixes `0` and `1`, giving differential uniformity
`2` out of `4`, so `d = 1` and every active S-box costs a factor `2⁻¹`. The linear layer is
`(x₀, x₁) ↦ (x₀ + x₁, x₀)`, invertible over `ZMod 4`. Rounds are `z ↦ λ(γ(z + k))`.

Four things are checked, and two of them are checks on the *hypotheses* rather than on the
conclusions.

* `toy_diffUniform` / `toy_not_diffUniform_one`: the uniformity constant is exactly `2`, so
  the bound is not being fed a value it could not attain.
* `toy_bricklayer_factors`: the product formula over bundles, recomputed on both sides.
* `toy_markov_matches`: `trailKeyCount` by exhaustive search over all `256` round-key
  vectors, against the product of per-round differential counts. Two independent routes to
  the same number, so `trailKeyCount_eq_prod` is not quietly about something else.
* `toy_fixed_key_fails_markov`: **the Markov hypothesis is load-bearing.** There is a
  trail whose key-averaged count is positive and whose count under one particular fixed
  round-key vector is zero. The product formula is therefore false at a fixed key, and the
  theorem in `Markov.lean` cannot be strengthened to drop the averaging.
* `toy_hull`: **the hull effect is real, not hypothetical.** A concrete two-round
  differential is realised by `8` of the `16` inputs, split evenly between two intermediate
  differences that each account for only `4`. The best single trail is off by a factor of
  two, and no wide-trail bound sees the difference.
-/

set_option autoImplicit false
-- The kernel enumerates `256` round-key vectors and unfolds two rounds on each.
set_option maxRecDepth 40000

/-! ### The cipher -/

/-- The toy S-box: the transposition of `2` and `3` in `ZMod 4`. -/
def sb (x : ZMod 4) : ZMod 4 := if x = 2 then 3 else if x = 3 then 2 else x

theorem sb_injective : Function.Injective sb := by decide

/-- The differential uniformity of `sb` is `2` out of `4`, so one active S-box costs a
factor `2⁻¹`. -/
theorem toy_diffUniform : IsDiffUniform sb 2 := by decide

/-- And it is exactly `2`: the bound cannot be improved to `1`. -/
theorem toy_not_diffUniform_one : ¬ IsDiffUniform sb 1 := by decide

/-- `2 · 2¹ ≤ 4`: the toy cipher clears a factor `2⁻¹` per active S-box. -/
theorem toy_uniformity_clears : 2 * 2 ^ 1 ≤ Fintype.card (ZMod 4) := by decide

/-- The S-box layer of the toy cipher. -/
def toyGamma : (Fin 2 → ZMod 4) → (Fin 2 → ZMod 4) := bricklayer (fun _ => sb)

/-- The linear layer `(x₀, x₁) ↦ (x₀ + x₁, x₀)`, as an additive bijection. -/
def toyLin : (Fin 2 → ZMod 4) ≃+ (Fin 2 → ZMod 4) where
  toFun x := ![x 0 + x 1, x 0]
  invFun y := ![y 1, y 0 - y 1]
  left_inv := by decide
  right_inv := by decide
  map_add' := by decide

/-- A two-round difference trail: one active bundle, then two, then one. -/
def toyTrail : Nat → (Fin 2 → ZMod 4)
  | 0 => ![1, 0]
  | 1 => ![1, 1]
  | _ => ![0, 1]

/-! ### The bundle product -/

/-- `diffCount_bricklayer`, recomputed on both sides: the left is a scan of all `16` states,
the right two scans of `4`. -/
theorem toy_bricklayer_factors :
    diffCount toyGamma ![1, 1] ![1, 3] = diffCount sb 1 1 * diffCount sb 1 3 := by decide

/-! ### The Markov product

The two numbers below are computed by different means: the first enumerates all `16² = 256`
round-key vectors, the second multiplies two differential counts. `trailKeyCount_eq_prod`
says they must agree, and here they are made to agree by computation rather than by proof. -/

theorem toy_trailKeyCount : trailKeyCount toyLin toyGamma 2 toyTrail 0 = 4 := by decide

theorem toy_trail_prod :
    ∏ n ∈ Finset.range 2, diffCount toyGamma (toyTrail n) (toyLin.symm (toyTrail (n + 1)))
      = 4 := by decide

theorem toy_markov_matches :
    trailKeyCount toyLin toyGamma 2 toyTrail 0
      = ∏ n ∈ Finset.range 2, diffCount toyGamma (toyTrail n) (toyLin.symm (toyTrail (n + 1))) :=
  toy_trailKeyCount.trans toy_trail_prod.symm

/-- The key-averaged count really does not depend on the input it starts from. -/
theorem toy_trailKeyCount_other : trailKeyCount toyLin toyGamma 2 toyTrail ![3, 1] = 4 := by
  decide

/-! ### The averaging is load-bearing

Under the all-zero round keys **no** pair follows this trail, while averaged over round keys
the count is `4` out of `256`. If the product formula held at a fixed key it would force
`0 · 16² = 16 · 4`, which is false. Every use of the Markov model is a use of this gap. -/

theorem toy_fixedKeyCount_zero : fixedKeyCount toyLin toyGamma 2 toyTrail ![0, 0] = 0 := by
  decide

theorem toy_fixed_key_fails_markov :
    fixedKeyCount toyLin toyGamma 2 toyTrail ![0, 0] * Fintype.card (Fin 2 → ZMod 4) ^ 2
      ≠ Fintype.card (Fin 2 → ZMod 4)
        * ∏ n ∈ Finset.range 2,
            diffCount toyGamma (toyTrail n) (toyLin.symm (toyTrail (n + 1))) := by
  rw [toy_fixedKeyCount_zero, toy_trail_prod]
  decide

/-! ### The bound, checked

`patternWeight toyTrail 2 = 1 + 2 = 3` active S-boxes at `2⁻¹` each, so the theorem promises
`4 · 2³ ≤ 16²`. The true probability is `4/256 = 2⁻⁶`, comfortably inside the promised
`2⁻³`: the toy S-box's actual differential counts are `1`, not the `2` its uniformity
allows, and the bound is only as sharp as its worst case. -/

theorem toy_patternWeight : patternWeight toyTrail 2 = 3 := by decide

theorem toy_bound_holds :
    trailKeyCount toyLin toyGamma 2 toyTrail 0 * 2 ^ (1 * patternWeight toyTrail 2)
      ≤ Fintype.card (Fin 2 → ZMod 4) ^ 2 := by
  rw [toy_trailKeyCount, toy_patternWeight]
  decide

/-! ### The hull

`toyRound k` is one keyed round. Over two rounds the differential `(0,2) → (2,2)` is
realised by `8` of the `16` inputs, and `diffCount_comp` splits that `8` into `4 + 4` across
two intermediate differences. A trail bound controls one of those summands. Nothing in
Layers 1 to 3 controls their sum. -/

/-- One keyed round of the toy cipher. -/
def toyRound (k x : Fin 2 → ZMod 4) : Fin 2 → ZMod 4 := toyLin (toyGamma (x + k))

theorem toy_hull_total :
    diffCount (fun x => toyRound ![1, 2] (toyRound 0 x)) ![0, 2] ![2, 2] = 8 := by decide

theorem toy_hull_split :
    jointCount (toyRound ![1, 2]) (toyRound 0) ![0, 2] ![1, 0] ![2, 2] = 4
      ∧ jointCount (toyRound ![1, 2]) (toyRound 0) ![0, 2] ![3, 0] ![2, 2] = 4 := by
  refine ⟨by decide, by decide⟩

/-- The differential is twice its best trail. A bound of `2⁻ᵏ` on every trail of a cipher is
not a bound of `2⁻ᵏ` on its differentials, and this is the smallest example that shows it. -/
theorem toy_hull_gap :
    jointCount (toyRound ![1, 2]) (toyRound 0) ![0, 2] ![1, 0] ![2, 2]
      < diffCount (fun x => toyRound ![1, 2] (toyRound 0 x)) ![0, 2] ![2, 2] := by
  rw [toy_hull_total, toy_hull_split.1]
  decide
