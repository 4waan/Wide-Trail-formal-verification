/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.Columns

/-!
# Bundle transpositions, diffusion optimality and Lemma 2

Section 5.4 of Daemen and Rijmen builds the inter-column mixing `Θ` out of the cheap
intra-column mixing `θ` and a pure bundle transposition `π`, as `Θ = π ∘ θ ∘ π`. The
transposition costs nothing to implement and moves no activity, yet if it is
*diffusion-optimal* it converts `θ`'s bundle branch number into `Θ`'s column branch
number. Lemma 2 is that conversion.

The formalisation makes one deliberate generalisation over the paper. A transposition is
only ever used through what it does to supports, so instead of demanding the literal
`π a i = a (p i)` we assume `SupportPerm p π`: `π` relabels the support along `p`. This
is closed under composition with the S-box layer, which is what lets Theorem 3 avoid the
paper's step of commuting `γ` past `π` and regrouping four `γπθ` rounds into
`ρᵃ ∘ ρᵇ ∘ ρᵃ ∘ ρᵇ`, a regrouping that leaves the round order shifted relative to the
`ρᵇ ∘ ρᵃ ∘ ρᵇ ∘ ρᵃ` that Theorem 2 is stated for.
-/

set_option autoImplicit false
-- `Fintype Col` below is used inside proofs (to sum over all columns) but not in the
-- statements, which this linter flags; `Finite Col` plus `Fintype.ofFinite` would obscure
-- the counting arguments for no gain.
set_option linter.unusedFintypeInType false

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Idx]
  [DecidableEq Col]
variable {col : Idx → Col} {p : Equiv.Perm Idx} {B : Nat}

/-- The bundle transposition of the paper: `b = π a ⇔ bᵢ = a_{p(i)}`. -/
def transpose (p : Equiv.Perm Idx) (a : Idx → K) : Idx → K := fun i => a (p i)

/-- `f` relabels supports the way the bundle transposition for `p` does. Weaker than
being that transposition, and closed under composing with support-preserving maps, which
is the only reason it is stated this way. -/
def SupportPerm (p : Equiv.Perm Idx) (f : (Idx → K) → (Idx → K)) : Prop :=
  ∀ a, activePattern (f a) = (activePattern a).image p.symm

theorem supportPerm_transpose (p : Equiv.Perm Idx) :
    SupportPerm p (transpose p : (Idx → K) → (Idx → K)) := by
  intro a
  ext i
  simp only [mem_activePattern, transpose, Finset.mem_image]
  constructor
  · intro h
    exact ⟨p i, h, p.symm_apply_apply i⟩
  · rintro ⟨j, hj, rfl⟩
    rwa [p.apply_symm_apply]

theorem SupportPerm.comp_preserveSupport {f g : (Idx → K) → (Idx → K)}
    (hf : SupportPerm p f) (hg : PreserveSupport g) : SupportPerm p (fun a => f (g a)) :=
  fun a => by rw [hf (g a), hg a]

theorem SupportPerm.weight_eq {f : (Idx → K) → (Idx → K)} (h : SupportPerm p f)
    (a : Idx → K) : weight (f a) = weight a := by
  rw [weight, weight, h a, Finset.card_image_of_injective _ p.symm.injective]

theorem SupportPerm.ne_zero {f : (Idx → K) → (Idx → K)} (h : SupportPerm p f)
    {a : Idx → K} (ha : a ≠ 0) : f a ≠ 0 := by
  intro hf
  have himg : (activePattern a).image p.symm = ∅ := by rw [← h a, hf]; simp
  exact ha (activePattern_eq_empty.mp (Finset.image_eq_empty.mp himg))

/-- `π` is diffusion-optimal when it sends the bundles of any one column to bundles in
pairwise distinct columns (Definition 5). -/
def DiffusionOptimal (col : Idx → Col) (p : Equiv.Perm Idx) : Prop :=
  ∀ i j, i ≠ j → col i = col j → col (p i) ≠ col (p j)

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq Col] in
/-- The paper's "it is easy to see that this implies the same condition for `π⁻¹`". -/
theorem DiffusionOptimal.symm (h : DiffusionOptimal col p) :
    DiffusionOptimal col p.symm := by
  intro i j hij hcol hcontra
  have hne : p.symm i ≠ p.symm j := fun e => hij (p.symm.injective e)
  have hkey := h _ _ hne hcontra
  rw [p.apply_symm_apply, p.apply_symm_apply] at hkey
  exact hkey hcol

omit [Fintype Idx] [DecidableEq Idx] in
/-- The counting heart of Lemma 2: a diffusion-optimal `p` maps the active bundles of a
single column injectively onto *columns* of the image, so one column's local weight is a
lower bound for the image's column weight. -/
theorem card_filter_le_colWeight_image (hp : DiffusionOptimal col p)
    {s t : Finset Idx} (hst : ∀ i ∈ s, p i ∈ t) (ξ : Col) :
    (s.filter (fun i => col i = ξ)).card ≤ (t.image col).card := by
  refine Finset.card_le_card_of_injOn (fun i => col (p i)) ?_ ?_
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem col (hst i hi.1))
  · intro i hi j hj hEq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
    by_contra hne
    exact hp i j hne (hi.2.trans hj.2.symm) hEq

/-- **Lemma 2.** If `π` is a diffusion-optimal bundle transposition then the *column*
branch number of `π ∘ φ ∘ π` is at least the *bundle* branch number of `φ`.

Stated for two possibly different support-transpositions `π₁`, `π₂` along the same
permutation, so that an S-box layer may be folded into either of them. -/
theorem lemma_two [Fintype Col] (hp : DiffusionOptimal col p)
    {π₁ π₂ φ : (Idx → K) → (Idx → K)}
    (h₁ : SupportPerm p π₁) (h₂ : SupportPerm p π₂)
    (hφ : IsColBranchBound col φ B)
    {a : Idx → K} (ha : π₁ a ≠ 0) :
    B ≤ colWeight col a + colWeight col (π₂ (φ (π₁ a))) := by
  -- `b` is the state just after the first transposition, `c` after `φ`, `d` after the
  -- second transposition.  Pick any column `ξ` that is active in `b`.
  obtain ⟨ξ, hξ⟩ : (activeCols col (π₁ a)).Nonempty := by
    rw [activeCols, Finset.image_nonempty, Finset.nonempty_iff_ne_empty]
    exact fun h => ha (activePattern_eq_empty.mp h)
  have hpos : 0 < localWeight col ξ (π₁ a) := mem_activeCols.mp hξ
  -- Within that column, `φ` alone already forces `B` active bundles.
  have hlocal : B ≤ localWeight col ξ (π₁ a) + localWeight col ξ (φ (π₁ a)) :=
    hφ (π₁ a) ξ (by omega)
  -- `π₁⁻¹` spreads the active bundles of column `ξ` of `b` over distinct columns of `a`.
  have hA : localWeight col ξ (π₁ a) ≤ colWeight col a := by
    refine card_filter_le_colWeight_image hp (fun i hi => ?_) ξ
    rw [h₁ a, Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rwa [p.apply_symm_apply]
  -- `π₂` spreads the active bundles of column `ξ` of `c` over distinct columns of `d`.
  have hB : localWeight col ξ (φ (π₁ a)) ≤ colWeight col (π₂ (φ (π₁ a))) := by
    refine card_filter_le_colWeight_image hp.symm (fun i hi => ?_) ξ
    rw [h₂ (φ (π₁ a))]
    exact Finset.mem_image_of_mem _ hi
  omega

/-- **Lemma 2, in the paper's own words.** The *column* branch number of `Θ = π ∘ φ ∘ π`
is at least the *bundle* branch number of `φ`, as a statement about `isBranchBound`
(Definition 4) rather than about one particular trail. -/
theorem isBranchBound_transpose_comp [Fintype Col] (hp : DiffusionOptimal col p)
    {π₁ π₂ φ : (Idx → K) → (Idx → K)}
    (h₁ : SupportPerm p π₁) (h₂ : SupportPerm p π₂)
    (hφ : IsColBranchBound col φ B) :
    isBranchBound col (fun a => π₂ (φ (π₁ a))) B :=
  fun _ ha => lemma_two hp h₁ h₂ hφ (h₁.ne_zero ha)
