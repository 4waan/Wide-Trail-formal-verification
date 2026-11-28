/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.WindowRelation
import WideTrail.Hades.Checks.MiddleBound

/-!
# Checks for window-relation certificates on the `ZMod 5` toy

`WideTrail.Hades.WindowRelation` proves that a window-relation certificate that passes
`Hades.RelationCheck.checkAll` gives the middle bound `3` (`MiddleBound.of_relationCheck`). This
file runs that path away from the width-sixteen instances, on the toy layer `Hades.Toy.mix`,
`x ↦ (x 0 + x 1, x 0 + 2 x 1)` over `ZMod 5`, with the S-box on coordinate `0`, the layer of the
checks in `WideTrail.Hades.Checks.MiddleBound`.

* `mix_eq_diagPlusOnes`: `mix` is `diag d + J` with `d = (0, 1)`.
* `toy_relations_check`, `toy_middleBound_six`: a chain of length `2` (`toyPsi`, `toyGamma`)
  gives four relations over six rounds, and `toySingles`, `toyPairs` refute the `6 + 15`
  patterns of one or two active rounds; `RelationCheck.checkAll` accepts them by
  `decide +kernel`, so every trail through `6` consecutive rounds with `mix` and mask `{0}`, from
  a nonzero difference, charges at least `3` S-boxes. `toy_window_six` gets the same `6 / 2 = 3`
  from the window argument: on the toy, the certificate recomputes the window bound.
* `toy_trail_check`, `toy_not_middleBound_six_four`: an explicit trail through `6` rounds with
  `mix` and mask `{0}`, from a nonzero difference, with active rounds exactly `1`, `2` and `4`
  (`toy_trail_active`), so `MiddleBound mix {0} 6 4` fails and `3` is the largest middle bound for
  six rounds.
* `toy_trail5_check`, `toy_not_middleBound_five_three`, `toy_no_certificate_five`: an explicit
  trail through `5` rounds with active rounds exactly `1` and `3`, so
  `MiddleBound mix {0} 5 3` fails; by `MiddleBound.of_relationCheck`, `checkAll` returns `false`
  for five rounds on every chain length and on all data with this diagonal.
* Negative controls: `toy_singles_rejected` (the multiplier `λ_0` of the certificate of the
  pattern `{1}` increased by one) and `toy_psi_rejected` (one entry of the chain increased by
  one); `checkAll` returns `false` on each, by `decide +kernel`.

The certificate data were computed outside Lean from the literals of `WideTrail.Hades.Checks.Toy`
(the matrix `!![1, 1; 1, 2]` and `mix`); nothing depends on how they were found, since the checks
are complete. The axiom footprints of the results are pinned at the end of the file.

## What is not claimed

The bounds are lower bounds on charged S-boxes in the `IsTrail` model for the toy layer; the
witness trails are trails in that model, not claimed to be realised by an input pair with the
toy's constants. Nothing here concerns the width-sixteen instances, whose certificates are checked
in `WideTrail.Poseidon2.Certificates`.
-/

set_option autoImplicit false

namespace Hades.WindowRelationChecks

open Hades.Toy
open Hades.MiddleBoundChecks (toy_inactive_two)

/-! ### The toy layer is `diag d + J` -/

/-- `mix` is `diag d + J` with `d = (0, 1)`: `(x 0 + x 1, x 1 + (x 0 + x 1))`. -/
theorem mix_eq_diagPlusOnes :
    mix.toLinearMap = Poseidon2.diagPlusOnes (1 : ZMod 5) ![0, 1] := by
  refine LinearMap.ext fun x => funext fun i => ?_
  fin_cases i
  · simp [mix, Poseidon2.diagPlusOnes_apply, Fin.sum_univ_two]
  · simp [mix, Poseidon2.diagPlusOnes_apply, Fin.sum_univ_two]
    ring

/-- No nonzero difference stays inactive through `m ≥ 2` consecutive rounds with `diag d + J`
(from `toy_inactive_two`). -/
theorem toy_inactive {m : ℕ} (hm : 2 ≤ m) :
    inactiveSpace (Poseidon2.diagPlusOnes (1 : ZMod 5) ![0, 1]) ({0} : Finset (Fin 2)) m = ⊥ := by
  rw [← mix_eq_diagPlusOnes]
  exact eq_bot_iff.mpr ((inactiveSpace_anti _ _ hm).trans toy_inactive_two.le)

/-! ### The certificate data -/

/-- The diagonal `d = (0, 1)`. -/
def toyDiagonal : List ℕ := [0, 1]

/-- A chain of length `2` for `diag d + J` at coordinate `0`. -/
def toyPsi : List (List ℕ) := [[0, 0], [2, 4], [4, 0]]

/-- The scalars `γ_0`, `γ_1` of the chain. -/
def toyGamma : List ℕ := [1, 4]

/-- Refutations `[pos, out, λ_0, λ_1, λ_2, λ_3]` of the patterns `{x}`, `x < 6`. -/
def toySingles : List (List ℕ) :=
  [[0, 1, 4, 0, 0, 0], [1, 0, 3, 3, 0, 0], [2, 0, 4, 0, 0, 0], [3, 0, 0, 4, 0, 0],
    [4, 0, 0, 0, 4, 0], [5, 0, 0, 0, 0, 4]]

/-- Refutations of the patterns `{x, x + 1 + j}`, row `x`, entry `j`. -/
def toyPairs : List (List (List ℕ)) :=
  [[[1, 1, 0, 4, 0, 0], [0, 1, 4, 2, 2, 0], [0, 1, 4, 0, 0, 0], [0, 1, 4, 0, 0, 0],
      [0, 1, 4, 0, 0, 0]],
    [[2, 1, 0, 0, 4, 0], [1, 0, 3, 3, 4, 4], [1, 0, 3, 3, 0, 0], [1, 0, 3, 3, 0, 0]],
    [[2, 0, 4, 0, 0, 0], [2, 0, 4, 0, 0, 0], [2, 0, 4, 0, 0, 0]],
    [[3, 0, 0, 4, 0, 0], [3, 0, 0, 4, 0, 0]],
    [[4, 0, 0, 0, 4, 0]],
    []]

/-- The states of a trail through `6` rounds with active rounds `1`, `2` and `4`. -/
def toyTrailStates : List (List ℕ) :=
  [[0, 1], [1, 2], [1, 3], [0, 3], [3, 1], [0, 1], [1, 2]]

/-- The S-box output differences of that trail. -/
def toyTrailOutputs : List ℕ := [0, 4, 2, 0, 4, 0]

/-- The states of a trail through `5` rounds with active rounds `1` and `3`. -/
def toyTrail5States : List (List ℕ) := [[0, 1], [1, 2], [0, 2], [2, 4], [0, 4], [4, 3]]

/-- The S-box output differences of that trail. -/
def toyTrail5Outputs : List ℕ := [0, 3, 0, 1, 0]

/-- The diagonal is the list `toyDiagonal`, entry by entry. -/
theorem toy_diag_eq :
    ∀ k : Fin 2, (![0, 1] : Fin 2 → ZMod 5) k = RelationCheck.ent 5 toyDiagonal k := by
  decide

/-! ### Six rounds: the certificate gives `3`, and `3` is the largest -/

/-- **The checker accepts the toy certificate** for six rounds. -/
theorem toy_relations_check :
    RelationCheck.checkAll 5 2 0 6 2 toyDiagonal toyPsi toyGamma toySingles toyPairs = true := by
  decide +kernel

/-- **Six rounds charge at least three S-boxes**, from the relation certificate: every trail
through `6` consecutive rounds with `mix` and mask `{0}`, from a nonzero difference, charges at
least `3` S-boxes. -/
theorem toy_middleBound_six : MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 6 3 := by
  rw [mix_eq_diagPlusOnes]
  exact MiddleBound.of_relationCheck _ 0 6 2 toyDiagonal toyPsi toyGamma toySingles toyPairs
    toy_diag_eq toy_relations_check (toy_inactive (by norm_num))

/-- The window argument gives the same `6 / 2 = 3`. -/
theorem toy_window_six : MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 6 (6 / 2) :=
  MiddleBound.of_inactiveSpace toy_inactive_two 6

/-- The checker accepts the trail through six rounds. -/
theorem toy_trail_check :
    RelationCheck.checkTrail 5 2 0 6 toyDiagonal toyTrailStates toyTrailOutputs = true := by
  decide +kernel

/-- The active rounds of the six-round trail are exactly `1`, `2` and `4`. -/
theorem toy_trail_active : ∀ n < 6,
    (RelationCheck.ent 5 (RelationCheck.row toyTrailStates n) 0 ≠ 0 ↔
      n = 1 ∨ n = 2 ∨ n = 4) := by
  decide +kernel

/-- **`toy_middleBound_six` is the largest bound for six rounds**: the trail of
`toyTrailStates` and `toyTrailOutputs` starts from a nonzero difference and charges `3`
S-boxes. -/
theorem toy_not_middleBound_six_four :
    ¬ MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 6 4 := by
  rw [mix_eq_diagPlusOnes]
  exact MiddleBound.not_of_checkTrail _ 0 6 4 toyDiagonal toyTrailStates toyTrailOutputs mix
    mix_eq_diagPlusOnes toy_diag_eq toy_trail_check (by decide +kernel) (by decide +kernel)

/-! ### Five rounds: no certificate passes -/

/-- The checker accepts the trail through five rounds. -/
theorem toy_trail5_check :
    RelationCheck.checkTrail 5 2 0 5 toyDiagonal toyTrail5States toyTrail5Outputs = true := by
  decide +kernel

/-- The active rounds of the five-round trail are exactly `1` and `3`. -/
theorem toy_trail5_active : ∀ n < 5,
    (RelationCheck.ent 5 (RelationCheck.row toyTrail5States n) 0 ≠ 0 ↔ n = 1 ∨ n = 3) := by
  decide +kernel

/-- **Five rounds need not charge three S-boxes**: the trail of `toyTrail5States` and
`toyTrail5Outputs` starts from a nonzero difference and charges `2`. -/
theorem toy_not_middleBound_five_three :
    ¬ MiddleBound mix.toLinearMap ({0} : Finset (Fin 2)) 5 3 := by
  rw [mix_eq_diagPlusOnes]
  exact MiddleBound.not_of_checkTrail _ 0 5 3 toyDiagonal toyTrail5States toyTrail5Outputs mix
    mix_eq_diagPlusOnes toy_diag_eq toy_trail5_check (by decide +kernel) (by decide +kernel)

/-- **No relation certificate passes for five rounds**: for every chain length `D` and all data
`psi`, `gamma`, `singles`, `pairs`, `RelationCheck.checkAll` with the toy diagonal returns
`false` for five rounds, since a passing check would give `toy_not_middleBound_five_three`'s
bound by `MiddleBound.of_relationCheck`. -/
theorem toy_no_certificate_five (D : ℕ) (psi : List (List ℕ)) (gamma : List ℕ)
    (singles : List (List ℕ)) (pairs : List (List (List ℕ))) :
    RelationCheck.checkAll 5 2 0 5 D toyDiagonal psi gamma singles pairs = false := by
  rw [← Bool.not_eq_true]
  intro h
  apply toy_not_middleBound_five_three
  rw [mix_eq_diagPlusOnes]
  exact MiddleBound.of_relationCheck _ 0 5 D toyDiagonal psi gamma singles pairs toy_diag_eq h
    (toy_inactive (by norm_num))

/-! ### Changed certificates are rejected -/

/-- `toySingles` with the multiplier `λ_0` of the certificate of the pattern `{1}` increased by
one (`3` becomes `4`); every other entry is unchanged. -/
def toySinglesCorrupted : List (List ℕ) :=
  toySingles.set 1 ((toySingles.getD 1 []).set 2 ((toySingles.getD 1 []).getD 2 0 + 1))

/-- The corrupted table differs from `toySingles`. -/
theorem toySinglesCorrupted_ne : toySinglesCorrupted ≠ toySingles := by
  decide +kernel

/-- **The checker rejects the changed multiplier.** -/
theorem toy_singles_rejected :
    RelationCheck.checkAll 5 2 0 6 2 toyDiagonal toyPsi toyGamma toySinglesCorrupted toyPairs =
      false := by
  decide +kernel

/-- `toyPsi` with entry `0` of row `1` of the chain increased by one (`2` becomes `3`); every
other entry is unchanged. -/
def toyPsiCorrupted : List (List ℕ) :=
  toyPsi.set 1 ((toyPsi.getD 1 []).set 0 ((toyPsi.getD 1 []).getD 0 0 + 1))

/-- The corrupted chain differs from `toyPsi`. -/
theorem toyPsiCorrupted_ne : toyPsiCorrupted ≠ toyPsi := by
  decide +kernel

/-- **The checker rejects the changed chain.** -/
theorem toy_psi_rejected :
    RelationCheck.checkAll 5 2 0 6 2 toyDiagonal toyPsiCorrupted toyGamma toySingles toyPairs =
      false := by
  decide +kernel

end Hades.WindowRelationChecks

/-- info: 'Hades.WindowRelationChecks.mix_eq_diagPlusOnes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.mix_eq_diagPlusOnes

/-- info: 'Hades.WindowRelationChecks.toy_relations_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_relations_check

/-- info: 'Hades.WindowRelationChecks.toy_middleBound_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_middleBound_six

/-- info: 'Hades.WindowRelationChecks.toy_trail_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_trail_check

/-- info: 'Hades.WindowRelationChecks.toy_not_middleBound_six_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_not_middleBound_six_four

/-- info: 'Hades.WindowRelationChecks.toy_trail5_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_trail5_check

/-- info: 'Hades.WindowRelationChecks.toy_not_middleBound_five_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_not_middleBound_five_three

/-- info: 'Hades.WindowRelationChecks.toy_no_certificate_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_no_certificate_five

/-- info: 'Hades.WindowRelationChecks.toy_singles_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_singles_rejected

/-- info: 'Hades.WindowRelationChecks.toy_psi_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hades.WindowRelationChecks.toy_psi_rejected
