/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Checks.Toy

/-!
# The two-bundle toy as a wide-trail specification, and further hypothesis checks

The toys of `Checks/ToyOne.lean` and `Checks/Toy.lean`, used to instantiate further headline
theorems of `Trail.lean` and `Hull.lean` with every hypothesis met, and to show that some further
hypotheses are needed.

* **A wide-trail specification for the toy.** `toyMaskSpec` has two columns of one bundle each,
  the identity as dispersion, the forward mask map `toyLinV` (the inverse of `toyLinT`,
  `toyLinT_toyLinV`) as mixing layer, and branch number `1`; its `lin` is undone by `toyLinT`
  (`toyMaskSpec_lin`). With columns of one bundle, the branch number `1` holds for every map,
  so the activity bound of the specification is weak: these instances show that the hypotheses
  of the specification-level theorems can be met together, not that the bounds are strong.
* **The bridge and the specification bounds, instantiated.** `toy_isTrail_of_trailCorr_ne_zero`
  is `isTrail_of_trailCorr_ne_zero` on the toy; `toy_trailCorr_le_of_spec` and
  `toy_trailCorr_ratio_le_of_spec` are `trailCorr_le_of_spec` (with `c = 4`, `d = 1`) and
  `trailCorr_ratio_le_of_spec` (with `c = 4`) for `toyMaskSpec`, for every number of rounds.
* **The schedule bound, instantiated.** `toy_three_round_bound` is
  `elpCount_bound_of_two_rounds` on three rounds of the toy, with the two-round window starting
  at round `1`: for `u ≠ 0`, `elpCount 3 u v · 8 ^ 4 ≤ 4 ^ 4 · 64 ^ 5`.
* **Bijectivity is needed for the bridge, typed.** `toy_not_isTrail_nonbijective`: for every
  specification on the toy's state whose `lin` is undone by `toyLinT`, the one-round trail of
  `toy_bridge_fails_nonbijective`, which has a nonzero correlation through the non-injective
  `andNext`, is not an `IsTrail`. `toyMaskSpec` is such a specification
  (`toy_bridge_fails_nonbijective_spec`), so every hypothesis of `isTrail_of_trailCorr_ne_zero`
  other than bijectivity holds there.
* **The nonzero input mask is needed for the two-round bound.** At `u = v = 0` the count is
  `64 ^ 4 = 2 ^ 24` (`toy_elpCount_zero_zero`, from the column sums and the zero output mask),
  and the bound of `toy_two_round_bound` fails (`toy_bound_fails_zero_mask`).
* **The linearity bound is needed for the two-round bound.** `chi3` does not have linearity
  bound `2` (`chi3_not_isLinearityBound_two`); with `c = 2` the inequality fails at
  `u77 → v52` (`toy_bound_fails_linearity_two`).
* **Separation is needed for the fixed-key expansion.** On the one-bundle toy under the zero
  pairing, for which the identity is still an adjoint of the linear layer, the identity of
  `walsh_run_eq_sum_trails` at `r = 1` fails at the zero key and the masks `(0, 0)`:
  `8 · 8 ≠ 512` (`one_expansion_fails_zeroPairing`).

## Which hypotheses the toy checks cover

Shown to be needed on the toys: separation, for Nyberg's identity and the fixed-key expansion;
bijectivity, for the two-round bound and the bridge; the branch number, the linearity bound and
the nonzero input mask, for the two-round bound; `c · 2 ^ d ≤ |K|`, for the weight-based trail
bound. Not shown, among others: the adjoint hypotheses; the nonzero input mask of the
specification bounds; separation for the two-round bound, the schedule bound and the
specification bounds. On the toy, a nonzero mask that pairs to zero with every state has Walsh
value `8` at the output mask `0` for every S-box, so such a pairing breaks the linearity bound `4`
as well, and the role of separation alone is not isolated there.

## What is not claimed

These checks concern the toys only. The specification `toyMaskSpec` has branch number `1`, so
its activity bound `r / 4 + [2 ≤ r % 4]` is weak; these instances say nothing about the bounds of
a specification with larger columns. An instance of the specification-level linear trail bounds
with a meaningful activity bound is left to the AES stage.
-/

set_option autoImplicit false

namespace Linear.Checks

/-! ### The forward mask map -/

/-- The bit-pairing adjoint `mulAlphaT` of `mulAlpha`, applied twice and once and summed: on the
mask side this is the inverse of `1 + αᵀ`. -/
def toyLinVt (w : Bits3) : Bits3 := mulAlphaT (mulAlphaT w) + mulAlphaT w

/-- The forward mask map of the toy, the inverse of `toyLinT`:
`(w₀, w₁) ↦ (w₀ + t, t)`, `t = (αᵀ² + αᵀ)(w₀ + w₁)`. -/
def toyLinV (w : State) : State := ![w 0 + toyLinVt (w 0 + w 1), toyLinVt (w 0 + w 1)]

/-- `toyLinT` undoes `toyLinV`, first bundle (a check over the `64` pairs of bundles). -/
theorem toyLinT_toyLinV_zero : ∀ a b : Bits3,
    a + toyLinVt (a + b) + toyLinVt (a + b) = a := by
  decide +kernel

/-- `toyLinT` undoes `toyLinV`, second bundle. -/
theorem toyLinT_toyLinV_one : ∀ a b : Bits3,
    a + toyLinVt (a + b) + mulAlphaT (toyLinVt (a + b)) = b := by
  decide +kernel

/-- `toyLinT` undoes the forward mask map `toyLinV`. -/
theorem toyLinT_toyLinV (w : State) : toyLinT (toyLinV w) = w := by
  funext i
  fin_cases i
  · exact toyLinT_toyLinV_zero (w 0) (w 1)
  · exact toyLinT_toyLinV_one (w 0) (w 1)

/-- `toyLinT` sends the zero mask to the zero mask. -/
theorem toyLinT_zero : toyLinT 0 = 0 := by decide +kernel

/-- The forward mask map sends only the zero mask to the zero mask. -/
theorem toyLinV_nondeg : NonDegenerate toyLinV := fun a h => by
  rw [← toyLinT_toyLinV a, h, toyLinT_zero]

/-! ### A wide-trail specification for the toy -/

/-- With columns of one bundle each, every map has column branch number at least `1`. -/
theorem toyLinV_isColBranchBound : IsColBranchBound (id : Fin 2 → Fin 2) toyLinV 1 :=
  fun _ _ h => h

/-- With columns of one bundle each, the identity dispersion is diffusion-optimal: no two
distinct bundles share a column. -/
theorem toy_diffusionOptimal : DiffusionOptimal (id : Fin 2 → Fin 2) (Equiv.refl (Fin 2)) :=
  fun _ _ hij hcol => absurd hcol hij

/-- **A wide-trail specification for the toy's masks.** Two columns of one bundle each, the
identity as dispersion, the forward mask map `toyLinV` as mixing layer, branch number `1`. The
S-box field is the identity; `IsTrail` and its activity bounds do not refer to it. -/
def toyMaskSpec : WideTrailSpec (Fin 2) (Fin 2) Bits3 where
  col := id
  sbox := id
  disp := Equiv.refl (Fin 2)
  mix := toyLinV
  branch := 1
  sbox_preserves := fun _ => rfl
  disp_optimal := toy_diffusionOptimal
  mix_branch := toyLinV_isColBranchBound
  mix_nondeg := toyLinV_nondeg

/-- `toyLinT` undoes the specification's forward mask map. -/
theorem toyMaskSpec_lin : ∀ b, toyLinT (toyMaskSpec.lin b) = b :=
  fun b => toyLinT_toyLinV b

/-! ### The bridge and the specification bounds, instantiated -/

/-- **The bridge on the toy** (`isTrail_of_trailCorr_ne_zero`): a trail of the toy with a nonzero
correlation over the first `r` rounds is a trail of `toyMaskSpec`. -/
theorem toy_isTrail_of_trailCorr_ne_zero {r : ℕ} {T : ℕ → State}
    (h : trailCorr sign₂ B3.pi toyLamT (fun n => bricklayer (toySbox n)) r T ≠ 0) :
    toyMaskSpec.IsTrail T r :=
  isTrail_of_trailCorr_ne_zero B3_separating toyMaskSpec (fun _ _ _ => chi3_bijective)
    (fun _ _ => toyMaskSpec_lin) h

/-- **The specification trail bound on the toy** (`trailCorr_le_of_spec` with `c = 4`, `d = 1`,
for `toyMaskSpec`): every `r`-round trail with a nonzero input mask has
`|trailCorr| · 2 ^ (r / 4 + [2 ≤ r % 4]) ≤ 64 ^ r`. -/
theorem toy_trailCorr_le_of_spec {r : ℕ} {T : ℕ → State} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ B3.pi toyLamT (fun n => bricklayer (toySbox n)) r T).natAbs
        * 2 ^ (1 * (r / 4 * 1 + (if 2 ≤ r % 4 then 1 else 0))) ≤ 64 ^ r := by
  have h := trailCorr_le_of_spec B3_separating toyMaskSpec (s := fun _ => chi3)
    (fun _ => chi3_bijective) (c := 4) (d := 1) (fun _ => chi3_isLinearityBound)
    (by rw [card_Bits3]; decide) toyMaskSpec_lin (r := r) h0
  rw [card_State] at h
  exact h

/-- **The specification ratio bound on the toy** (`trailCorr_ratio_le_of_spec` with `c = 4`, for
`toyMaskSpec`): every `r`-round trail with a nonzero input mask has
`|trailCorr| · 8 ^ A ≤ 4 ^ A · 64 ^ r`, `A = r / 4 + [2 ≤ r % 4]`. -/
theorem toy_trailCorr_ratio_le_of_spec {r : ℕ} {T : ℕ → State} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ B3.pi toyLamT (fun n => bricklayer (toySbox n)) r T).natAbs
        * 8 ^ (r / 4 * 1 + (if 2 ≤ r % 4 then 1 else 0))
      ≤ 4 ^ (r / 4 * 1 + (if 2 ≤ r % 4 then 1 else 0)) * 64 ^ r := by
  have h := trailCorr_ratio_le_of_spec B3_separating toyMaskSpec (s := fun _ => chi3)
    (fun _ => chi3_bijective) (c := 4) (fun _ => chi3_isLinearityBound) toyMaskSpec_lin (r := r) h0
  rw [card_Bits3, card_State] at h
  exact h

/-! ### The schedule bound, instantiated -/

/-- **The schedule bound on the toy** (`elpCount_bound_of_two_rounds` with `R = 3`, `j = 1`,
`c = 4`, `B = 3`): over three rounds, for `u ≠ 0`, `elpCount 3 u v · 8 ^ 4 ≤ 4 ^ 4 · 64 ^ 5`. -/
theorem toy_three_round_bound {u : State} (hu : u ≠ 0) (v : State) :
    elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 3 u v * 8 ^ 4
      ≤ 4 ^ 4 * 64 ^ 5 := by
  have h := elpCount_bound_of_two_rounds B3_separating toyLam toyLamT
    (fun _ => toyLin_isAdjoint) (fun n => bricklayer (toySbox n)) toySbox 3 1 (by norm_num)
    (fun _ _ x y hxy => funext fun i => chi3_bijective.injective (congrFun hxy i))
    (fun _ _ _ => rfl) (fun _ _ _ _ => chi3_bijective) (fun _ _ _ _ => chi3_isLinearityBound)
    toyLinT_isBranchBound hu v
  simp only [card_Bits3, card_State, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at h
  exact h

/-! ### Bijectivity is needed for the bridge, typed -/

/-- **Bijectivity is needed for the bridge.** For every specification on the toy's state whose
forward mask map is undone by `toyLinT`, the one-round trail from the zero mask to `(1, 0)`
through the non-injective `andNext` has a nonzero correlation and is not a trail of the
specification: the conclusion of `isTrail_of_trailCorr_ne_zero` fails. -/
theorem toy_not_isTrail_nonbijective {Col : Type} [DecidableEq Col] [Fintype Col]
    (S : WideTrailSpec (Fin 2) Col Bits3) (hlam : ∀ b, toyLinT (S.lin b) = b) :
    trailCorr sign₂ B3.pi toyLamT (fun _ => bricklayer fun _ => andNext) 1
        (fun n => if n = 0 then 0 else ![![1, 0, 0], 0]) ≠ 0 ∧
      ¬ S.IsTrail (fun n => if n = 0 then 0 else ![![1, 0, 0], 0]) 1 := by
  refine ⟨toy_bridge_fails_nonbijective.1, fun hT => ?_⟩
  have hinj : Function.Injective toyLinT :=
    Finite.injective_iff_surjective.mpr fun b => ⟨S.lin b, hlam b⟩
  rw [isTrail_iff_backward S hinj hlam] at hT
  exact toy_bridge_fails_nonbijective.2 (by simpa using hT 0 (by norm_num))

/-- The same for `toyMaskSpec`, which meets every other hypothesis of
`isTrail_of_trailCorr_ne_zero`: a separating pairing and `toyLinT` undoing its `lin`. -/
theorem toy_bridge_fails_nonbijective_spec :
    trailCorr sign₂ B3.pi toyLamT (fun _ => bricklayer fun _ => andNext) 1
        (fun n => if n = 0 then 0 else ![![1, 0, 0], 0]) ≠ 0 ∧
      ¬ toyMaskSpec.IsTrail (fun n => if n = 0 then 0 else ![![1, 0, 0], 0]) 1 :=
  toy_not_isTrail_nonbijective toyMaskSpec toyMaskSpec_lin

/-! ### Further hypotheses of the two-round bound -/

/-- At the zero masks the two-round count is `64 ^ 4`: the column at the output mask `0` sums
to `64 ^ 4` (`sum_elpCount_left`), and every nonzero input mask contributes `0`
(`elpCount_zero_right`). -/
theorem toy_elpCount_zero_zero :
    elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 2 0 0 = 64 ^ 4 := by
  have h := sum_elpCount_left B3_separating.pi toyLam (fun n => bricklayer (toySbox n)) 2
    (0 : State)
  rw [Finset.sum_eq_single (0 : State)
    (fun u _ hu => elpCount_zero_right B3_separating.pi _ _ 2 hu)
    (fun h => absurd (Finset.mem_univ _) h), card_State] at h
  exact h

/-- **The nonzero input mask is needed.** At `u = v = 0` the inequality of
`toy_two_round_bound` fails: `2 ^ 24 · 8 ^ 4 > 4 ^ 4 · 64 ^ 4`. -/
theorem toy_bound_fails_zero_mask :
    4 ^ 4 * 64 ^ 4 < elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 2 0 0 * 8 ^ 4 := by
  rw [toy_elpCount_zero_zero]
  decide

/-- **The linearity bound is needed.** With `c = 2`, which `chi3` does not satisfy
(`chi3_not_isLinearityBound_two`), the bound would read `elpCount · 8 ^ 4 ≤ 2 ^ 4 · 64 ^ 4`; it
fails at `u77 → v52`. -/
theorem toy_bound_fails_linearity_two :
    2 ^ 4 * 64 ^ 4 < elpCount B3.pi toyLam (fun n => bricklayer (toySbox n)) 2 u77 v52 * 8 ^ 4 := by
  rw [toy_elp_attained]
  decide

/-! ### Separation is needed for the fixed-key expansion -/

/-- **Separation is needed for the fixed-key expansion.** Under the zero pairing, which is not
separating (`zeroPairing_not_separating`), the identity is an adjoint of the linear layer, and
the identity of `walsh_run_eq_sum_trails` at `r = 1` on the one-bundle toy fails at the zero
key and the masks `(0, 0)`: `8 · 8 ≠ 512`. -/
theorem one_expansion_fails_zeroPairing :
    IsAdjoint zeroPairing zeroPairing idBits id ∧
    (8 : ℤ) * walsh sign₂ zeroPairing zeroPairing
        (Scheduled.run (fun _ => idBits) (fun _ => chi3) (1 + 1) 0) 0 0
      ≠ ∑ d : Fin 1 → Bits3, trailPhase sign₂ zeroPairing (1 + 1) 0
          (Scheduled.throughTrail 0 d 0)
          * trailCorr sign₂ zeroPairing (fun _ => id) (fun _ => chi3) (1 + 1)
              (Scheduled.throughTrail 0 d 0) :=
  ⟨fun _ _ => rfl, by decide +kernel⟩

end Linear.Checks
