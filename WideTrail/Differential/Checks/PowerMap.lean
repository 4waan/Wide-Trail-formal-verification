/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Differential.PowerMap
import Mathlib.Algebra.Field.ZMod

/-!
# Checks for the power-map bound

`PowerMap.lean` proves that `x ↦ x ^ d` has differential uniformity at most `d - 1`
whenever `2 ≤ d` and `(d : K) ≠ 0`. This file tests that statement on prime fields small
enough for the kernel to enumerate.

* **Attained for cubes.** Over `ZMod 7` the cube map has a differential with count `2`,
  so `pow_three_uniform` is sharp there, and the kernel's own enumeration of the whole
  table agrees with the bound.
* **The characteristic hypothesis is necessary.** Over `ZMod 3` cubing is additive, and
  the differential `(1, 1)` is realised by all three inputs. Every hypothesis of
  `pow_uniform` except `(d : K) ≠ 0` holds, and the conclusion fails.
* **The hypothesis `2 ≤ d` is necessary.** For `d = 1`, the identity map realises the
  differential `(1, 1)` on every input, although `(1 : K) ≠ 0` in every field.
* **Attained for seventh powers.** Over `ZMod 29` the differential `(1, 0)` of
  `x ↦ x ^ 7` has count `6`, so `pow_seven_uniform` is sharp there. The six inputs are
  `1 / (ζ - 1)` for the six seventh roots of unity `ζ ≠ 1`, which exist because `7`
  divides `29 - 1`. `29` is the smallest prime for which this happens. Over smaller
  prime fields the bound is not attained: over `ZMod 11`, where `x ↦ x ^ 7` is a
  permutation, the kernel finds uniformity `2`.

The witnesses were found by an exhaustive search outside Lean; only the witnesses
themselves are used here, and every finite check is kernel `decide`.
-/

set_option autoImplicit false

namespace Sbox.PowerMapChecks

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

instance : Fact (Nat.Prime 29) := ⟨by decide⟩

/-! ### Cubes over `ZMod 7`: the bound two is attained -/

/-- The general bound, instantiated. -/
theorem cube_seven_uniform : IsDiffUniform (fun x : ZMod 7 => x ^ 3) 2 :=
  pow_three_uniform (by decide)

/-- The kernel enumerates the whole difference table and finds the same bound. -/
theorem cube_seven_uniform_decide : IsDiffUniform (fun x : ZMod 7 => x ^ 3) 2 := by
  decide

/-- `(x + 1) ^ 3 - x ^ 3 = 1` has the two solutions `0` and `6`. -/
theorem cube_seven_attained : diffCount (fun x : ZMod 7 => x ^ 3) 1 1 = 2 := by decide

/-- So the bound of `pow_three_uniform` cannot be lowered over `ZMod 7`. -/
theorem cube_seven_not_uniform_one : ¬ IsDiffUniform (fun x : ZMod 7 => x ^ 3) 1 := by
  intro h
  have h1 := h 1 (by decide) 1
  rw [cube_seven_attained] at h1
  omega

/-! ### Cubes over `ZMod 3`: the characteristic hypothesis is necessary -/

/-- Cubing is additive over `ZMod 3`, so the differential `(1, 1)` is realised by every
input. -/
theorem cube_three_additive : diffCount (fun x : ZMod 3 => x ^ 3) 1 1 = 3 := by decide

/-- Over `ZMod 3`, with `d = 3`, the hypothesis `2 ≤ d` holds, the hypothesis
`(d : K) ≠ 0` fails, and the conclusion of `pow_uniform` fails. -/
theorem cube_three_counterexample :
    2 ≤ 3 ∧ ((3 : Nat) : ZMod 3) = 0 ∧
      ¬ IsDiffUniform (fun x : ZMod 3 => x ^ 3) (3 - 1) := by
  refine ⟨by norm_num, by decide, fun h => ?_⟩
  have h1 := h 1 (by decide) 1
  rw [cube_three_additive] at h1
  omega

/-- **`(d : K) ≠ 0` cannot be dropped from `pow_uniform`.** -/
theorem pow_uniform_needs_char :
    ¬ ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : Nat), 2 ≤ d →
      IsDiffUniform (fun x : K => x ^ d) (d - 1) :=
  fun h => cube_three_counterexample.2.2 (h (ZMod 3) 3 (by norm_num))

/-- **`2 ≤ d` cannot be dropped from `pow_uniform`.** For `d = 1` the map is the identity
and `(1 : K) ≠ 0` in every field, but the differential `(1, 1)` is realised by every
input. -/
theorem pow_uniform_needs_two_le :
    ¬ ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : Nat), (d : K) ≠ 0 →
      IsDiffUniform (fun x : K => x ^ d) (d - 1) := by
  intro h
  have h1 := h (ZMod 3) 1 (by decide) 1 (by decide) 1
  have hcount : diffCount (fun x : ZMod 3 => x ^ 1) 1 1 = 3 := by decide
  rw [hcount] at h1
  omega

/-! ### Seventh powers: attained over `ZMod 29`, not over `ZMod 11` -/

/-- The general bound, instantiated over `ZMod 29`. -/
theorem seventh_twentynine_uniform : IsDiffUniform (fun x : ZMod 29 => x ^ 7) 6 :=
  pow_seven_uniform (by decide)

/-- `(x + 1) ^ 7 = x ^ 7` has six solutions in `ZMod 29`, namely `x = 1 / (ζ - 1)` for
the six nontrivial seventh roots of unity `ζ`. -/
theorem seventh_twentynine_attained : diffCount (fun x : ZMod 29 => x ^ 7) 1 0 = 6 := by
  decide

/-- So the bound of `pow_seven_uniform` cannot be lowered over `ZMod 29`. -/
theorem seventh_twentynine_not_uniform_five :
    ¬ IsDiffUniform (fun x : ZMod 29 => x ^ 7) 5 := by
  intro h
  have h1 := h 1 (by decide) 0
  rw [seventh_twentynine_attained] at h1
  omega

/-- Over `ZMod 11` the seventh-power map is a permutation (`gcd 7 10 = 1`) and its
uniformity is `2`, well below the general bound `6`. The bound of `pow_seven_uniform` is
therefore not attained over every field where it applies. -/
theorem seventh_eleven_uniform : IsDiffUniform (fun x : ZMod 11 => x ^ 7) 2 := by
  decide

/-! ### Axiom footprints -/

/-- info: 'Sbox.pow_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sbox.pow_uniform

/-- info: 'Sbox.pow_uniform_of_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sbox.pow_uniform_of_choose

/-- info: 'Sbox.pow_three_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sbox.pow_three_uniform

/-- info: 'Sbox.pow_seven_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sbox.pow_seven_uniform

/-- info: 'Sbox.powDiff_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sbox.powDiff_coeff

/-- info: 'Sbox.powDiff_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sbox.powDiff_natDegree_le

end Sbox.PowerMapChecks
