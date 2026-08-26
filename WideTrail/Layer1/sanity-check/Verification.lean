/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.AES
import Mathlib.Data.Fintype.Pi

/-!
# Adversarial checks on the formalisation

A proved theorem can still be worthless: its hypotheses may be jointly unsatisfiable
(making it vacuous), or one of them may be inert (making the statement weaker than it
looks). This file attacks both possibilities with concrete, kernel-evaluated ciphers.

* `toySpec` is a complete `WideTrailSpec`. It exists, so the hypothesis bundle is
  satisfiable and every theorem about `WideTrailSpec` has at least one model.
* `four_round_fails_without_dispersion` lists every hypothesis of
  `four_round_identical` *except* diffusion optimality, all satisfied, together with the
  negated conclusion. So that hypothesis cannot be dropped, and the proof cannot be
  secretly ignoring it.
* `thetaTheta_bound_matches` derives the `B²` constant a second time along the other
  route, through Theorem 2 and the paper's form of Lemma 2, confirming that the two
  four-round theorems agree rather than one being an artefact of how it was set up.
-/

set_option autoImplicit false
-- `Fintype Col` below is used inside proofs (to sum over all columns) but not in the
-- statements, which this linter flags; `Finite Col` plus `Fintype.ofFinite` would obscure
-- the counting arguments for no gain.
set_option linter.unusedFintypeInType false

/-! ### The hypotheses are satisfiable

A `2 × 2` state over `GF(2)` whose column map is `(x, y) ↦ (x + y, x)`. Its bundle branch
number is exactly `2`: `decide` confirms the bound at `2` and, by direct computation, it
fails at `3`. -/

/-- The column map of the toy cipher. -/
def toyMix : (SquareIdx 2 → Fin 2) → (SquareIdx 2 → Fin 2) :=
  fun a i => if i.1 = 0 then a (0, i.2) + a (1, i.2) else a (0, i.2)

theorem toyMix_branch : IsColBranchBound (sqCol 2) toyMix 2 := by
  change ∀ (a : SquareIdx 2 → Fin 2) (x : Fin 2),
    0 < localWeight (sqCol 2) x a + localWeight (sqCol 2) x (toyMix a) →
    2 ≤ localWeight (sqCol 2) x a + localWeight (sqCol 2) x (toyMix a)
  decide

/-- The branch number really is `2` and not more, so `toySpec` is not accidentally
stronger than it claims. -/
theorem toyMix_branch_not_three : ¬ IsColBranchBound (sqCol 2) toyMix 3 := by
  intro h
  revert h
  change ¬ ∀ (a : SquareIdx 2 → Fin 2) (x : Fin 2),
    0 < localWeight (sqCol 2) x a + localWeight (sqCol 2) x (toyMix a) →
    3 ≤ localWeight (sqCol 2) x a + localWeight (sqCol 2) x (toyMix a)
  decide

theorem toyMix_nondeg : NonDegenerate toyMix := by
  change ∀ a : SquareIdx 2 → Fin 2, toyMix a = 0 → a = 0
  decide

/-- A complete wide-trail specification. Its existence rules out vacuity. -/
def toySpec : WideTrailSpec (SquareIdx 2) (Fin 2) (Fin 2) :=
  squareSpec 2 id toyMix 2 (fun _ => rfl) toyMix_branch toyMix_nondeg

example : toySpec.fourRoundBound = 4 := rfl

/-! ### Diffusion optimality is load-bearing

Give the state a single column of four bundles. No transposition can then be
diffusion-optimal, since two bundles of that column have nowhere else to go. The column
map `M = I + J` over `GF(2)` still has bundle branch number `4`: if `w(x)` is even then
`Mx = x` and the total is `2w(x) ≥ 4`; if `w(x)` is odd then `Mx` is the complement of
`x` and the total is exactly `4`.

`M` is an involution, so `e₀ ↦ Me₀ ↦ e₀ ↦ Me₀` is a genuine four-round trail, and it
activates `1 + 3 + 1 + 3 = 8` S-boxes, well under the `B² = 16` that Theorem 3 would
otherwise promise. -/

/-- The trivial column partition: one column holding every bundle. -/
abbrev trivCol : Fin 4 → Unit := fun _ => ()

/-- `M = I + J` over `GF(2)`. -/
def hadamardMix : (Fin 4 → Fin 2) → (Fin 4 → Fin 2) :=
  fun a i => a i + (a 0 + a 1 + a 2 + a 3)

theorem hadamardMix_branch : IsColBranchBound trivCol hadamardMix 4 := by
  change ∀ (a : Fin 4 → Fin 2) (x : Unit),
    0 < localWeight trivCol x a + localWeight trivCol x (hadamardMix a) →
    4 ≤ localWeight trivCol x a + localWeight trivCol x (hadamardMix a)
  decide

theorem hadamardMix_nondeg : NonDegenerate hadamardMix := by
  change ∀ a : Fin 4 → Fin 2, hadamardMix a = 0 → a = 0
  decide

/-- With one column there is no diffusion-optimal transposition at all. -/
theorem no_diffusionOptimal (p : Equiv.Perm (Fin 4)) : ¬ DiffusionOptimal trivCol p :=
  fun h => h 0 1 (by decide) rfl rfl

/-- The round transformation of the sabotaged cipher: `θ ∘ π ∘ γ` with `γ = id` and
`π = id`. -/
def noPiRound (a : Fin 4 → Fin 2) : Fin 4 → Fin 2 :=
  hadamardMix (transpose (Equiv.refl (Fin 4)) (id a))

/-- The difference pattern with a single active bundle. -/
def e₀ : Fin 4 → Fin 2 := fun i => if i = 0 then 1 else 0

/-- Every hypothesis of `four_round_identical` except `DiffusionOptimal`, satisfied at
once, together with the negation of its conclusion. Diffusion optimality therefore
cannot be removed, and the proof of Theorem 3 genuinely uses it. -/
theorem four_round_fails_without_dispersion :
    PreserveSupport (id : (Fin 4 → Fin 2) → (Fin 4 → Fin 2))
      ∧ SupportPerm (Equiv.refl (Fin 4))
          (fun a : Fin 4 → Fin 2 => transpose (Equiv.refl (Fin 4)) (id a))
      ∧ IsColBranchBound trivCol hadamardMix 4
      ∧ NonDegenerate hadamardMix
      ∧ e₀ ≠ 0
      ∧ ¬ (4 * 4 ≤ weight e₀ + weight (noPiRound e₀)
            + weight (noPiRound (noPiRound e₀))
            + weight (noPiRound (noPiRound (noPiRound e₀)))) :=
  ⟨fun _ => rfl,
   (supportPerm_transpose (Equiv.refl (Fin 4))).comp_preserveSupport (fun _ => rfl),
   hadamardMix_branch, hadamardMix_nondeg, by decide, by decide⟩

/-- The trail above activates exactly 8 S-boxes over four rounds, against a promised 16. -/
theorem noPi_trail_weight :
    weight e₀ + weight (noPiRound e₀) + weight (noPiRound (noPiRound e₀))
      + weight (noPiRound (noPiRound (noPiRound e₀))) = 8 := by decide

/-! ### The two four-round theorems agree

Section 6 of the paper claims the single-round-transformation structure "achieves the same
bound" as the two-round-transformation structure. Feeding the paper's form of Lemma 2 into
Theorem 2 reproduces exactly the constant `B²` that Theorem 3 produces, which is that
claim, checked. -/

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Idx]
  [DecidableEq Col] [Fintype Col] {col : Idx → Col}

/-- Theorem 2, applied to the `Θ = π ∘ θ ∘ π` construction, yields the same `B(θ)²` that
Theorem 3 yields directly. -/
theorem thetaTheta_bound_matches {γ θ π : (Idx → K) → (Idx → K)} {p : Equiv.Perm Idx}
    {B : Nat} (hγ : PreserveSupport γ) (hπ : SupportPerm p π)
    (hp : DiffusionOptimal col p) (hθ : IsColBranchBound col θ B)
    (hnd : NonDegenerate θ) {a₁ a₂ a₃ a₄ : Idx → K} (h₁ : a₁ ≠ 0)
    (h₂ : a₂ = θ (γ a₁)) (h₃ : a₃ = π (θ (π (γ a₂)))) (h₄ : a₄ = θ (γ a₃)) :
    B * B ≤ weight a₁ + weight a₂ + weight a₃ + weight a₄ :=
  four_round_thetaTheta hγ hθ (isBranchBound_transpose_comp hp hπ hπ hθ) hnd h₁ h₂ h₃ h₄
