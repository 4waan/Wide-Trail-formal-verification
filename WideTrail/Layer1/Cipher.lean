/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.FourRound

/-!
# Bundled wide-trail specifications and multi-round bounds

`WideTrailSpec` packages everything a `γπθ` cipher must supply for the four-round bound
the column partition, an S-box layer, a dispersion permutation, a mixing layer, and the
four structural facts about them. Instantiating the structure and reading off
`fourRoundBound` is the "kernel-checked active-S-box bound" the project is aiming at:
the number is `B²`, and the proof obligation is discharged once, here.

`trailWeight_bound` then extends the paper, which only remarks that "any `2n`-round trail
can be decomposed in `n` 2-round trails". The same decomposition at width four gives
`n · B²` active S-boxes over `4n` rounds, which is the form an implementer actually wants
(AES-128 has 10 rounds, so two disjoint four-round blocks, hence `2 · 25 = 50`).
-/

set_option autoImplicit false

/-- A cipher in the `γπθ` shape, together with the structural facts the wide-trail
theorems consume. -/
structure WideTrailSpec (Idx Col K : Type*) [Zero K] [DecidableEq K] [Fintype Idx]
    [DecidableEq Idx] [DecidableEq Col] [Fintype Col] where
  /-- The column partition, given by its quotient map. -/
  col : Idx → Col
  /-- The non-linear bricklayer layer `γ`. -/
  sbox : (Idx → K) → (Idx → K)
  /-- The bundle transposition underlying the dispersion layer `π`. -/
  disp : Equiv.Perm Idx
  /-- The intra-column mixing layer `θ`. -/
  mix : (Idx → K) → (Idx → K)
  /-- The bundle branch number of `θ`. -/
  branch : Nat
  /-- `γ` is a bricklayer of invertible S-boxes, so it moves no activity. -/
  sbox_preserves : PreserveSupport sbox
  /-- `π` scatters each column across pairwise distinct columns. -/
  disp_optimal : DiffusionOptimal col disp
  /-- Every column active on either side of `θ` carries `branch` active bundles. -/
  mix_branch : IsColBranchBound col mix branch
  /-- `θ` is invertible. -/
  mix_nondeg : NonDegenerate mix

namespace WideTrailSpec

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Idx]
  [DecidableEq Col] [Fintype Col]

/-- The round transformation `ρᶜ = θ ∘ π ∘ γ`. -/
def round (S : WideTrailSpec Idx Col K) (a : Idx → K) : Idx → K :=
  S.mix (transpose S.disp (S.sbox a))

/-- The sequence of difference (or selection) patterns at the input of each round. -/
def trail (S : WideTrailSpec Idx Col K) (a : Idx → K) : Nat → (Idx → K)
  | 0 => a
  | n + 1 => S.round (trail S a n)

/-- The bundle weight of the first `r` rounds of a trail: the number of active S-boxes. -/
def trailWeight (S : WideTrailSpec Idx Col K) (a : Idx → K) (r : Nat) : Nat :=
  ∑ i ∈ Finset.range r, weight (S.trail a i)

/-- The four-round active-S-box bound of this specification. -/
def fourRoundBound (S : WideTrailSpec Idx Col K) : Nat := S.branch * S.branch

variable (S : WideTrailSpec Idx Col K)

theorem round_apply (a : Idx → K) :
    S.round a = S.mix (transpose S.disp (S.sbox a)) := rfl

@[simp] theorem trail_zero (a : Idx → K) : S.trail a 0 = a := rfl

@[simp] theorem trail_succ (a : Idx → K) (n : Nat) :
    S.trail a (n + 1) = S.round (S.trail a n) := rfl

theorem round_ne_zero {a : Idx → K} (ha : a ≠ 0) : S.round a ≠ 0 := by
  intro h
  exact (supportPerm_transpose S.disp).ne_zero
    (ne_zero_of_preservesSupport S.sbox_preserves ha) (S.mix_nondeg _ h)

theorem trail_ne_zero {a : Idx → K} (ha : a ≠ 0) (n : Nat) : S.trail a n ≠ 0 := by
  induction n with
  | zero => exact ha
  | succ n ih => exact S.round_ne_zero ih

/-- Two consecutive rounds of a wide-trail cipher already cost `branch` active S-boxes. -/
theorem two_round {a : Idx → K} (ha : a ≠ 0) (n : Nat) :
    S.branch ≤ weight (S.trail a n) + weight (S.trail a (n + 1)) :=
  two_round_identical S.sbox_preserves (supportPerm_transpose S.disp) S.mix_branch
    (S.trail_ne_zero ha n) rfl

/-- **The four-round bound.** Any four consecutive rounds of a wide-trail cipher contain
at least `branch²` active S-boxes. -/
theorem four_round {a : Idx → K} (ha : a ≠ 0) (n : Nat) :
    S.fourRoundBound ≤ weight (S.trail a n) + weight (S.trail a (n + 1))
      + weight (S.trail a (n + 2)) + weight (S.trail a (n + 3)) :=
  four_round_identical S.sbox_preserves (supportPerm_transpose S.disp) S.disp_optimal
    S.mix_branch S.mix_nondeg (S.trail_ne_zero ha n) rfl rfl rfl

theorem trailWeight_add_four (a : Idx → K) (n : Nat) :
    S.trailWeight a (n + 4) = S.trailWeight a n
      + (weight (S.trail a n) + weight (S.trail a (n + 1))
        + weight (S.trail a (n + 2)) + weight (S.trail a (n + 3))) := by
  have e3 : S.trailWeight a (n + 4)
      = S.trailWeight a (n + 3) + weight (S.trail a (n + 3)) := Finset.sum_range_succ _ _
  have e2 : S.trailWeight a (n + 3)
      = S.trailWeight a (n + 2) + weight (S.trail a (n + 2)) := Finset.sum_range_succ _ _
  have e1 : S.trailWeight a (n + 2)
      = S.trailWeight a (n + 1) + weight (S.trail a (n + 1)) := Finset.sum_range_succ _ _
  have e0 : S.trailWeight a (n + 1)
      = S.trailWeight a n + weight (S.trail a n) := Finset.sum_range_succ _ _
  omega

theorem trailWeight_mono (a : Idx → K) {r r' : Nat} (h : r ≤ r') :
    S.trailWeight a r ≤ S.trailWeight a r' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- Over `4n` rounds the active-S-box count is at least `n` times the four-round bound.
The paper states the analogous decomposition only for two-round blocks. -/
theorem trailWeight_bound {a : Idx → K} (ha : a ≠ 0) (n : Nat) :
    n * S.fourRoundBound ≤ S.trailWeight a (4 * n) := by
  induction n with
  | zero => simp [trailWeight]
  | succ n ih =>
    have hstep := S.four_round ha (4 * n)
    have hsplit : 4 * (n + 1) = 4 * n + 4 := by omega
    rw [hsplit, S.trailWeight_add_four]
    have hmul : (n + 1) * S.fourRoundBound
        = n * S.fourRoundBound + S.fourRoundBound := Nat.succ_mul n S.fourRoundBound
    omega

end WideTrailSpec
