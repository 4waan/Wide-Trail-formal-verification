/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Dispersion

/-!
# The four-round propagation theorems

Theorem 2 (the `θΘ` construction, two alternating round transformations) and Theorem 3
(the `γπθ` construction, one round transformation, the AES shape) of Daemen and Rijmen.

Both are the same three-line count once Lemma 1 and Lemma 2 are available:

* rounds 1 and 3 each convert *active columns* into `B(θ)` times as many *active bundles*
  (Lemma 1, used output-indexed for round 1 and input-indexed for round 3);
* round 2 forces `B(Θ, Ξ)` active columns across the boundary between them;
* multiply.

Theorem 3 is proved directly rather than by rewriting four `γπθ` rounds as
`ρᵃ ∘ ρᵇ ∘ ρᵃ ∘ ρᵇ` and appealing to Theorem 2. The paper's regrouping is correct as an
identity of functions, but it produces the round order `ρᵇ, ρᵃ, ρᵇ, ρᵃ` reading from the
input, whereas Theorem 2 is stated for a trail that *starts* with `ρᵃ`; patching that gap
costs more than redoing the count, and the direct version also shows precisely where
`Θ = π ∘ θ ∘ π` enters (only through `lemma_two`, applied across rounds 2 and 3).
-/

set_option autoImplicit false
-- `Fintype Col` below is used inside proofs (to sum over all columns) but not in the
-- statements, which this linter flags; `Finite Col` plus `Fintype.ofFinite` would obscure
-- the counting arguments for no gain.
set_option linter.unusedFintypeInType false

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Idx]
  [DecidableEq Col] [Fintype Col]
variable {col : Idx → Col}

/-- Only the zero pattern maps to the zero pattern. Every linear layer in the paper is
invertible, so this always holds; it is isolated as a named hypothesis because it is the
one and only place the four-round proofs need invertibility. -/
def NonDegenerate (ψ : (Idx → K) → (Idx → K)) : Prop := ∀ a, ψ a = 0 → a = 0

omit [DecidableEq Idx] in
/-- **Theorem 2 (Four-round Propagation Theorem for the `θΘ` construction).**

For a key-alternating cipher alternating `ρᵃ = θ ∘ γ` and `ρᵇ = Θ ∘ γ`, the bundle weight
of any trail over `ρᵇ ∘ ρᵃ ∘ ρᵇ ∘ ρᵃ` is at least `B(θ) · B(Θ, Ξ)`.

`a₁ … a₄` are the patterns at the input of each round; the linear layer of the fourth
round never appears, exactly as in the paper. Key additions never appear either: they
satisfy `PreserveSupport` and so are absorbed into `γ`. -/
theorem four_round_thetaTheta {γ θ Θ : (Idx → K) → (Idx → K)} {Bθ BΘ : Nat}
    (hγ : PreserveSupport γ) (hθ : IsColBranchBound col θ Bθ)
    (hΘ : isBranchBound col Θ BΘ) (hnd : NonDegenerate θ)
    {a₁ a₂ a₃ a₄ : Idx → K} (h₁ : a₁ ≠ 0)
    (h₂ : a₂ = θ (γ a₁)) (h₃ : a₃ = Θ (γ a₂)) (h₄ : a₄ = θ (γ a₃)) :
    Bθ * BΘ ≤ weight a₁ + weight a₂ + weight a₃ + weight a₄ := by
  have hγ₁ : γ a₁ ≠ 0 := ne_zero_of_preservesSupport hγ h₁
  have ha₂ : a₂ ≠ 0 := by rw [h₂]; exact fun h => hγ₁ (hnd _ h)
  have hγ₂ : γ a₂ ≠ 0 := ne_zero_of_preservesSupport hγ ha₂
  -- Round 2 spreads activity across columns.
  have hcol : BΘ ≤ colWeight col a₂ + colWeight col a₃ := by
    have h := hΘ (γ a₂) hγ₂
    rwa [colWeight_eq_of_preservesSupport hγ, ← h₃] at h
  -- Round 1: each column active at its output costs `Bθ` bundles.
  have hR1 : colWeight col a₂ * Bθ ≤ weight a₁ + weight a₂ := by
    have h := lemma_one_out hθ (γ a₁)
    rwa [← h₂, weight_eq_of_preservesSupport hγ] at h
  -- Round 3: each column active at its input costs `Bθ` bundles.
  have hR3 : colWeight col a₃ * Bθ ≤ weight a₃ + weight a₄ := by
    have h := lemma_one_in hθ (γ a₃)
    rwa [← h₄, weight_eq_of_preservesSupport hγ,
      colWeight_eq_of_preservesSupport hγ] at h
  calc Bθ * BΘ
      = BΘ * Bθ := Nat.mul_comm _ _
    _ ≤ (colWeight col a₂ + colWeight col a₃) * Bθ := Nat.mul_le_mul_right Bθ hcol
    _ = colWeight col a₂ * Bθ + colWeight col a₃ * Bθ := Nat.add_mul _ _ _
    _ ≤ weight a₁ + weight a₂ + (weight a₃ + weight a₄) := Nat.add_le_add hR1 hR3
    _ = weight a₁ + weight a₂ + weight a₃ + weight a₄ := by omega

/-- **Theorem 3 (Four-Round Propagation Theorem).**

For a key-iterated cipher with the single round transformation `ρᶜ = θ ∘ π ∘ γ` and a
diffusion-optimal `π`, the number of active S-boxes in any four-round trail is at least
`B(θ)²`. This is the AES round shape: `γ` = SubBytes, `π` = ShiftRows, `θ` = MixColumns. -/
theorem four_round_identical {γ θ π : (Idx → K) → (Idx → K)} {p : Equiv.Perm Idx} {B : Nat}
    (hγ : PreserveSupport γ) (hπ : SupportPerm p π) (hp : DiffusionOptimal col p)
    (hθ : IsColBranchBound col θ B) (hnd : NonDegenerate θ)
    {a₁ a₂ a₃ a₄ : Idx → K} (h₁ : a₁ ≠ 0)
    (h₂ : a₂ = θ (π (γ a₁))) (h₃ : a₃ = θ (π (γ a₂))) (h₄ : a₄ = θ (π (γ a₃))) :
    B * B ≤ weight a₁ + weight a₂ + weight a₃ + weight a₄ := by
  -- `π ∘ γ` relabels supports along `p`, because `γ` moves no activity at all.
  have hfp : SupportPerm p (fun a : Idx → K => π (γ a)) := hπ.comp_preserveSupport hγ
  have hw : ∀ a : Idx → K, weight (π (γ a)) = weight a := fun a => hfp.weight_eq a
  have hne : ∀ a : Idx → K, a ≠ 0 → π (γ a) ≠ 0 := fun a ha => hfp.ne_zero ha
  have ha₂ : a₂ ≠ 0 := by rw [h₂]; exact fun h => hne a₁ h₁ (hnd _ h)
  -- Round 1, output-indexed.
  have hR1 : colWeight col a₂ * B ≤ weight a₁ + weight a₂ := by
    have h := lemma_one_out hθ (π (γ a₁))
    rwa [← h₂, hw a₁] at h
  -- Round 3, input-indexed.
  have hR3 : colWeight col (π (γ a₃)) * B ≤ weight a₃ + weight a₄ := by
    have h := lemma_one_in hθ (π (γ a₃))
    rwa [← h₄, hw a₃] at h
  -- Rounds 2 and 3 together *are* `Θ = π ∘ θ ∘ π`, so Lemma 2 applies verbatim.
  have hcol : B ≤ colWeight col a₂ + colWeight col (π (γ a₃)) := by
    rw [h₃]
    exact lemma_two hp hfp hfp hθ (a := a₂) (hne a₂ ha₂)
  calc B * B
      ≤ (colWeight col a₂ + colWeight col (π (γ a₃))) * B := Nat.mul_le_mul_right B hcol
    _ = colWeight col a₂ * B + colWeight col (π (γ a₃)) * B := Nat.add_mul _ _ _
    _ ≤ weight a₁ + weight a₂ + (weight a₃ + weight a₄) := Nat.add_le_add hR1 hR3
    _ = weight a₁ + weight a₂ + weight a₃ + weight a₄ := by omega

/-- Two rounds of the `γπθ` structure already cost `B(θ)` active bundles. This is
Theorem 1 specialised to the AES round shape, and it is what makes the four-round bound
`B²` rather than merely `2B`. -/
theorem two_round_identical {γ θ π : (Idx → K) → (Idx → K)} {p : Equiv.Perm Idx} {B : Nat}
    (hγ : PreserveSupport γ) (hπ : SupportPerm p π) (hθ : IsColBranchBound col θ B)
    {a₁ a₂ : Idx → K} (h₁ : a₁ ≠ 0) (h₂ : a₂ = θ (π (γ a₁))) :
    B ≤ weight a₁ + weight a₂ := by
  have hfp : SupportPerm p (fun a : Idx → K => π (γ a)) := hπ.comp_preserveSupport hγ
  have h := branch_le_weight_add (col := col) hθ (hfp.ne_zero h₁ : π (γ a₁) ≠ 0)
  rwa [← h₂, hfp.weight_eq a₁] at h
