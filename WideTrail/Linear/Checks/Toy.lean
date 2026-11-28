/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Checks.ToyOne

/-!
# Linear trails and hulls on a two-bundle toy

The trail and hull bounds of `Trail.lean` and `Hull.lean`, instantiated on a cipher the kernel
can evaluate, with checks that their hypotheses are needed and that the hull bound is a
statement about the key-averaged model only.

The cipher: the state is two bundles of three bits, `State = Fin 2 → Bits3`, sixty-four states,
with the bundle-sum bit pairing `B3.pi`. The S-box is `chi3` on both bundles: bijective, with
linearity bound `4` of `8` (`Checks/Character.lean`). The linear layer is
`toyLin (x₀, x₁) = (x₀ + x₁, x₀ + α x₁)`, with `α` multiplication by `x` in
`GF(8) = F₂[x] / (x³ + x + 1)` on bit vectors (`mulAlpha`). Its bit-pairing adjoint is
`toyLinT (v₀, v₁) = (v₀ + v₁, v₀ + αᵀ v₁)` (`toyLin_isAdjoint`), whose branch number is at least
`3` (`toyLinT_isBranchBound`) and not `4`. Round `n` is `x ↦ toyLin (chi3 (x + k n))` on both
bundles.

* **The two-round hull bound, instantiated.** `toy_two_round_bound` is
  `elpCount_two_round_bound` with `c = 4`, `B = 3`: for every `u ≠ 0` and `v`,
  `elpCount 2 u v · 8 ^ 4 ≤ 4 ^ 4 · 64 ^ 4`, that is at most `2 ^ 20` of a possible `2 ^ 24`.
* **The bound is attained.** At `u77 = (7, 7)`, `v52 = (5, 2)` the count is exactly `2 ^ 20`
  (`toy_elp_attained`, from `elpCount_two` and a kernel evaluation of the trail sum).
* **The branch hypothesis is needed.** With `B = 4` the inequality fails at `u77 → v52`
  (`toy_bound_fails_branch_four`).
* **Bijectivity is needed.** With the non-injective `andNext` in place of `chi3`, all other
  hypotheses hold (linearity bound `4`, the pairing, the adjoint, the branch number), and the
  count at `u70 = (7, 0)`, `u70 → u70`, is `1114112 > 2 ^ 20` (`toy_nonbijective_exceeds`).
  With `andNext` a one-round trail from the zero mask has a nonzero correlation and a support
  change (`toy_bridge_fails_nonbijective`). `Checks/ToySpec.lean` turns this into the typed
  statement that the trail is not an `IsTrail` of any specification whose `lin` is undone by
  `toyLinT` (`toy_not_isTrail_nonbijective`): the conclusion of the bridge
  `isTrail_of_trailCorr_ne_zero` fails.
* **The model is load-bearing.** Under the fixed key `kfix` the squared Walsh value at
  `u13 = (1, 3)`, `v31 = (3, 1)` is `1024`, four times the average `2 ^ 20 / 64 ^ 2 = 256` that
  the bound allows per key vector (`toy_fixed_exceeds`). At `u12 = (1, 2)`, `v74 = (7, 4)` the
  Walsh value is `16`, `-16` or `0` depending on the second round key (`toy_sign`): the key
  changes the sign, and trails can cancel.
* **The trail bound, instantiated.** `toy_trail_bound` is `natAbs_trailCorr_mul_pow_le` with
  `c = 4`, `d = 1`: every two-round trail has `|trailCorr| · 2 ^ W ≤ 64 ^ 2`. It is attained by
  the trail `trailA` from `u77` through `(1, 0)` to `v52`, with correlation `512` and three
  active S-boxes (`toy_trail_attained`), and it fails for `d = 2`, where `4 · 2 ^ 2 > 8`
  (`toy_trail_bound_fails_two`).

Masks are written as pairs of 3-bit numbers, bit `i` first. Every exhaustive check is over
`Bits3` or over sixty-four terms; the values were computed outside Lean first, and the kernel
rechecks every value used. `Checks/ToyNat.lean` recomputes the bound at all `63 · 64` mask pairs
as a numerical cross-check on natural numbers. `Checks/ToySpec.lean` builds a wide-trail
specification for this toy, instantiates the specification-level trail bounds and the schedule
bound, and checks further hypotheses.

## What is not claimed

These checks concern this toy only. The attained maximum `2 ^ 20` says nothing about how close
the bound is for any other cipher. The fixed-key check uses one key vector: it shows that the
key-averaged bound can fail for a fixed key, and says nothing about other keys.
-/

set_option autoImplicit false

namespace Linear.Checks

/-! ### Two bundles -/

/-- Multiplication by `α` in `GF(8) = F₂[x] / (x³ + x + 1)` on bit vectors, bit `i` the
coefficient of `xⁱ`: `(x₀, x₁, x₂) ↦ (x₂, x₀ + x₂, x₁)`. -/
def mulAlpha (x : Bits3) : Bits3 := ![x 2, x 0 + x 2, x 1]

/-- The bit-pairing adjoint of `mulAlpha`: `(v₀, v₁, v₂) ↦ (v₁, v₂, v₀ + v₁)`. -/
def mulAlphaT (v : Bits3) : Bits3 := ![v 1, v 2, v 0 + v 1]

/-- The state of the two-bundle toy: two bundles of three bits, sixty-four states. -/
abbrev State := Fin 2 → Bits3

/-- Two bundles of three bits make sixty-four states. -/
theorem card_State : Fintype.card (Fin 2 → Bits3) = 64 := by
  rw [Fintype.card_fun, card_Bits3, Fintype.card_fin]
  rfl

/-- `mulAlpha` is additive (a check over the `64` pairs of bundles). -/
theorem mulAlpha_add : ∀ a b : Bits3, mulAlpha (a + b) = mulAlpha a + mulAlpha b := by
  decide +kernel

/-- `mulAlphaT` is the bit-pairing adjoint of `mulAlpha`. -/
theorem mulAlpha_isAdjoint : ∀ v y : Bits3, B3.dot v (mulAlpha y) = B3.dot (mulAlphaT v) y := by
  decide +kernel

/-- The inverse of `toyLin` undoes it, first bundle (a check over the `64` pairs of bundles). -/
theorem toyLin_inv_zero : ∀ a b : Bits3,
    a + b + (mulAlpha (mulAlpha (a + b + (a + mulAlpha b))) + mulAlpha (a + b + (a + mulAlpha b)))
      = a := by
  decide +kernel

/-- The inverse of `toyLin` undoes it, second bundle. -/
theorem toyLin_inv_one : ∀ a b : Bits3,
    mulAlpha (mulAlpha (a + b + (a + mulAlpha b))) + mulAlpha (a + b + (a + mulAlpha b)) = b := by
  decide +kernel

/-- `toyLin` undoes its inverse, first bundle. -/
theorem toyLin_symm_zero : ∀ a b : Bits3,
    a + (mulAlpha (mulAlpha (a + b)) + mulAlpha (a + b))
      + (mulAlpha (mulAlpha (a + b)) + mulAlpha (a + b)) = a := by
  decide +kernel

/-- `toyLin` undoes its inverse, second bundle. -/
theorem toyLin_symm_one : ∀ a b : Bits3,
    a + (mulAlpha (mulAlpha (a + b)) + mulAlpha (a + b))
      + mulAlpha (mulAlpha (mulAlpha (a + b)) + mulAlpha (a + b)) = b := by
  decide +kernel

/-- The linear layer `(x₀, x₁) ↦ (x₀ + x₁, x₀ + α x₁)`, with inverse
`(y₀, y₁) ↦ (y₀ + t, t)`, `t = (α² + α)(y₀ + y₁)`. -/
def toyLin : State ≃+ State where
  toFun x := ![x 0 + x 1, x 0 + mulAlpha (x 1)]
  invFun y := ![y 0 + (mulAlpha (mulAlpha (y 0 + y 1)) + mulAlpha (y 0 + y 1)),
    mulAlpha (mulAlpha (y 0 + y 1)) + mulAlpha (y 0 + y 1)]
  left_inv x := by
    funext i
    fin_cases i
    · exact toyLin_inv_zero (x 0) (x 1)
    · exact toyLin_inv_one (x 0) (x 1)
  right_inv y := by
    funext i
    fin_cases i
    · exact toyLin_symm_zero (y 0) (y 1)
    · exact toyLin_symm_one (y 0) (y 1)
  map_add' x y := by
    funext i
    fin_cases i
    · change x 0 + y 0 + (x 1 + y 1) = x 0 + x 1 + (y 0 + y 1)
      abel
    · change x 0 + y 0 + mulAlpha (x 1 + y 1) = x 0 + mulAlpha (x 1) + (y 0 + mulAlpha (y 1))
      rw [mulAlpha_add]
      abel

/-- The adjoint of `toyLin` for the bit pairing: `(v₀, v₁) ↦ (v₀ + v₁, v₀ + αᵀ v₁)`. -/
def toyLinT (v : State) : State := ![v 0 + v 1, v 0 + mulAlphaT (v 1)]

/-- `toyLinT` is an adjoint of `toyLin` for the bundle-sum bit pairing. -/
theorem toyLin_isAdjoint : IsAdjoint B3.pi B3.pi toyLin toyLinT := fun v y => by
  have e1 : (B3.pi (Idx := Fin 2)).dot v (toyLin y)
      = B3.dot (v 0) (y 0 + y 1) + B3.dot (v 1) (y 0 + mulAlpha (y 1)) :=
    Fin.sum_univ_two (fun i => B3.dot (v i) (toyLin y i))
  have e2 : (B3.pi (Idx := Fin 2)).dot (toyLinT v) y
      = B3.dot (v 0 + v 1) (y 0) + B3.dot (v 0 + mulAlphaT (v 1)) (y 1) :=
    Fin.sum_univ_two (fun i => B3.dot (toyLinT v i) (y i))
  rw [e1, e2]
  simp only [map_add, AddMonoidHom.add_apply, mulAlpha_isAdjoint]
  abel

/-- The backward map `toyLinT` has branch number at least `3`. -/
theorem toyLinT_isBranchBound : isBranchBound id toyLinT 3 := by
  unfold isBranchBound
  decide +kernel

/-- And not `4`. -/
theorem toyLinT_not_isBranchBound_four : ¬ isBranchBound id toyLinT 4 := by
  unfold isBranchBound
  decide +kernel

/-- The rounds: `toyLin` after `chi3` on both bundles. -/
abbrev toyLam : ℕ → State ≃+ State := fun _ => toyLin

/-- The adjoints of the rounds' linear layers. -/
abbrev toyLamT : ℕ → State → State := fun _ => toyLinT

/-- The S-boxes: `chi3` on both bundles in every round. -/
abbrev toySbox : ℕ → Fin 2 → Bits3 → Bits3 := fun _ _ => chi3

/-! ### The two-round hull bound, instantiated -/

/-- **The two-round hull bound on the toy** (`elpCount_two_round_bound` with `c = 4`, `B = 3`):
for `u ≠ 0`, the key-averaged count is at most `2 ^ 20` of a possible
`64 ^ 2 · 64 ^ 2 = 2 ^ 24`. -/
theorem toy_two_round_bound {u : State} (hu : u ≠ 0) (v : State) :
    elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 2 u v * 8 ^ 4 ≤ 4 ^ 4 * 64 ^ 4 := by
  have h := elpCount_two_round_bound B3_separating toyLam toyLamT
    (fun _ => toyLin_isAdjoint) toySbox (fun _ _ _ => chi3_bijective)
    (fun _ _ _ => chi3_isLinearityBound) toyLinT_isBranchBound hu v
  simp only [card_Bits3, card_State, Nat.reduceSub, Nat.reduceMul] at h
  exact h

/-- The masks `u77 = (7, 7)` and `v52 = (5, 2)`, bundles as bit vectors. -/
def u77 : State := ![![1, 1, 1], ![1, 1, 1]]

/-- See `u77`. -/
def v52 : State := ![![1, 0, 1], ![0, 1, 0]]

/-- **The bound is attained.** At `u77 → v52` the count is `2 ^ 20`, computed from
`elpCount_two` and the trail sum over the sixty-four middle masks. -/
theorem toy_elp_attained :
    elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 2 u77 v52 = 2 ^ 20 := by
  rw [elpCount_two B3_separating.pi toyLam toyLamT (fun _ => toyLin_isAdjoint)]
  simp only [walsh_bricklayer, Fin.prod_univ_two]
  decide +kernel

/-- The bound of `toy_two_round_bound` holds with equality at `u77 → v52`. -/
theorem toy_bound_attained :
    elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 2 u77 v52 * 8 ^ 4 = 4 ^ 4 * 64 ^ 4 := by
  rw [toy_elp_attained]
  decide

/-- **The branch hypothesis is needed.** With `B = 4`, which `toyLinT` does not satisfy
(`toyLinT_not_isBranchBound_four`), the bound would read `elpCount · 8 ^ 6 ≤ 4 ^ 6 · 64 ^ 4`;
it fails at `u77 → v52`. -/
theorem toy_bound_fails_branch_four :
    4 ^ 6 * 64 ^ 4 < elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 2 u77 v52 * 8 ^ 6 := by
  rw [toy_elp_attained]
  decide

/-! ### The model is load-bearing -/

/-- A fixed key vector: zero in round `0`, `(0, (0, 1, 0))` in round `1`. -/
def kfix : Fin 2 → State := ![0, ![0, ![0, 1, 0]]]

/-- The masks `u13 = (1, 3)` and `v31 = (3, 1)`. -/
def u13 : State := ![![1, 0, 0], ![1, 1, 0]]

/-- See `u13`. -/
def v31 : State := ![![1, 1, 0], ![1, 0, 0]]

/-- Under the fixed key `kfix`, the Walsh value at `u13 → v31` is `-32`. -/
theorem toy_fixed_walsh :
    walsh sign₂ B3.pi B3.pi (Scheduled.run toyLam (fun n => bricklayer (toySbox n)) 2 kfix) u13 v31
      = -32 := by
  decide +kernel

/-- **A fixed key exceeds the key-averaged bound four times.** The bound allows an average squared
Walsh value of `2 ^ 20 / 64 ^ 2 = 256` per key vector; under `kfix` the squared Walsh value at
`u13 → v31` is `1024`. So `toy_two_round_bound` is not a bound for one fixed key. -/
theorem toy_fixed_exceeds :
    4 ^ 4 * 64 ^ 4 < (walsh sign₂ B3.pi B3.pi
      (Scheduled.run toyLam (fun n => bricklayer (toySbox n)) 2 kfix) u13 v31).natAbs ^ 2
        * 64 ^ 2 * 8 ^ 4 := by
  rw [toy_fixed_walsh]
  decide

/-- The masks `u12 = (1, 2)` and `v74 = (7, 4)`. -/
def u12 : State := ![![1, 0, 0], ![0, 1, 0]]

/-- See `u12`. -/
def v74 : State := ![![1, 1, 1], ![0, 0, 1]]

/-- **The key changes the sign, and can cancel trails.** At `u12 → v74`, with the round-`0` key
zero, the Walsh value is `16`, `-16` and `0` for the round-`1` keys `(0, 0)`, `(0, 1)` and
`(0, 2)`. -/
theorem toy_sign :
    walsh sign₂ B3.pi B3.pi (Scheduled.run toyLam (fun n => bricklayer (toySbox n)) 2
        ![0, 0]) u12 v74 = 16 ∧
    walsh sign₂ B3.pi B3.pi (Scheduled.run toyLam (fun n => bricklayer (toySbox n)) 2
        ![0, ![0, ![1, 0, 0]]]) u12 v74 = -16 ∧
    walsh sign₂ B3.pi B3.pi (Scheduled.run toyLam (fun n => bricklayer (toySbox n)) 2
        ![0, ![0, ![0, 1, 0]]]) u12 v74 = 0 := by
  decide +kernel

/-! ### Bijective S-boxes are needed -/

/-- The non-injective `andNext` has linearity bound `4`, as `chi3` does. -/
theorem andNext_isLinearityBound : IsLinearityBound B3 andNext 4 := by decide +kernel

/-- The mask `u70 = (7, 0)`. -/
def u70 : State := ![![1, 1, 1], 0]

/-- **Bijectivity is needed for the two-round bound.** With the non-injective `andNext` in place
of `chi3`, every other hypothesis of `elpCount_two_round_bound` holds (the pairing, the
adjoint, the branch number `3`, the linearity bound `4`), and the bound `2 ^ 20` fails at
`u70 → u70`: the count is `1114112`. -/
theorem toy_nonbijective_exceeds :
    4 ^ 4 * 64 ^ 4
      < elpCount B3.pi toyLam (fun _ => bricklayer fun _ => andNext) 2 u70 u70 * 8 ^ 4 := by
  rw [elpCount_two B3_separating.pi toyLam toyLamT (fun _ => toyLin_isAdjoint)]
  simp only [walsh_bricklayer, Fin.prod_univ_two]
  decide +kernel

/-- **Bijectivity is needed for the bridge.** With `andNext`, the one-round trail from the zero
mask to `(1, 0)` has a nonzero correlation, yet the mask `toyLinT (1, 0) = (1, 1)` at the output
of the S-box layer is not supported where the input mask is. `toy_not_isTrail_nonbijective`
(`Checks/ToySpec.lean`) derives from this, through `isTrail_iff_backward`, that the trail is not
an `IsTrail`: the conclusion of `isTrail_of_trailCorr_ne_zero` fails. -/
theorem toy_bridge_fails_nonbijective :
    trailCorr sign₂ B3.pi toyLamT (fun _ => bricklayer fun _ => andNext) 1
        (fun n => if n = 0 then 0 else ![![1, 0, 0], 0]) ≠ 0 ∧
      activePattern (toyLinT ![![1, 0, 0], 0]) ≠ activePattern (0 : State) := by
  decide +kernel

/-! ### The trail bound, instantiated -/

/-- **The trail bound on the toy** (`natAbs_trailCorr_mul_pow_le` with `c = 4`, `d = 1`): every
two-round trail has `|trailCorr| · 2 ^ W ≤ 64 ^ 2`, with `W` its number of active S-boxes. -/
theorem toy_trail_bound (T : ℕ → State) :
    (trailCorr sign₂ B3.pi toyLamT (fun n => bricklayer (toySbox n)) 2 T).natAbs
        * 2 ^ (1 * patternWeight T 2) ≤ 64 ^ 2 := by
  have h := natAbs_trailCorr_mul_pow_le (r := 2) (d := 1) (s := toySbox)
    (fun _ _ _ => chi3_isLinearityBound) (by rw [card_Bits3]; decide) toyLamT T
  simp only [card_State] at h
  exact h

/-- The trail `u77 → (1, 0) → v52`. -/
def trailA : ℕ → State := Scheduled.throughTrail u77 ![![![1, 0, 0], 0]] v52

/-- **The trail bound is attained**: `trailA` has correlation `512` and three active S-boxes,
and `512 · 2 ^ 3 = 64 ^ 2`. -/
theorem toy_trail_attained :
    trailCorr sign₂ B3.pi toyLamT (fun n => bricklayer (toySbox n)) 2 trailA = 512 ∧
      patternWeight trailA 2 = 3 := by
  decide +kernel

/-- **The hypothesis `c · 2 ^ d ≤ |K|` is needed.** With `d = 2` (and `4 · 2 ^ 2 > 8`) the
inequality of `toy_trail_bound` fails for `trailA`. -/
theorem toy_trail_bound_fails_two :
    64 ^ 2 < (trailCorr sign₂ B3.pi toyLamT (fun n => bricklayer (toySbox n)) 2 trailA).natAbs
      * 2 ^ (2 * patternWeight trailA 2) := by
  rw [toy_trail_attained.1, toy_trail_attained.2]
  decide

end Linear.Checks
