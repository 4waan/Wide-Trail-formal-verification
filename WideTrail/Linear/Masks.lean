/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Character
import WideTrail.Propagation.Cipher
import WideTrail.Propagation.Grid
import Mathlib.Data.Matrix.Mul

/-!
# Masks through linear layers

A linear layer `L` acts on masks through an adjoint `Lt`, `⟨v, L y⟩ = ⟨Lt v, y⟩` (`IsAdjoint`):
by (W3) the output mask `v` of `L` is the mask `Lt v` at the input of `L`. This file collects
the adjoint calculus, identifies the linear branch number of a map with the differential branch
number of its adjoint, and fixes the direction in which masks are propagated.

## The mask convention

A linear trail is indexed from the input: `T 0` is the input mask of round `0`. With `lamT` an
adjoint of the round's linear layer, the mask at the output of round `n`'s S-box layer is
`b = lamT (T (n + 1))`, and a nonzero trail has `supp b = supp (T n)`. Masks are propagated
**forward through the inverse of the adjoint**, `T (n + 1) = lamT⁻¹ b`, so that a mask sequence
is a `WideTrailSpec.IsTrail` of the specification whose linear layer `lin` is the forward mask
map `lamT⁻¹`. Forward propagation keeps the pairing invariant: `⟨Lt⁻¹ w, L y⟩ = ⟨w, y⟩`
(`IsAdjoint.dot_symm_apply`), so masks move contragrediently to states.

The backward reading, through `lamT` itself, is equivalent: `isTrail_iff_backward` restates
`S.IsTrail T r` as `supp (lamT (T (n + 1))) = supp (T n)` for every `n < r`, given that `lamT` is
injective and undoes `S.lin`. Branch numbers do not see the difference between a bijection and
its inverse (`isBranchBound_symm_iff`).

## What is proved

* `IsAdjoint.comp`, `IsAdjoint.symm`: adjoints compose, and if `Lt` is an adjoint of a bijection
  `L`, then `Lt⁻¹` is an adjoint of `L⁻¹`.
* `IsAdjoint.unique`, `IsAdjoint.map_zero`, `IsAdjoint.map_add`: for a pairing separating on the
  source, an adjoint is unique and additive.
* `IsAdjoint.comap`, `IsAdjoint.maskRelabel`: pulling pairings back along additive bijections
  conjugates an adjoint; relabelling masks, `⟨u, y⟩' = ⟨φ u, y⟩`, turns an adjoint `Lt` of `L`
  into the adjoint `φ⁻¹ ∘ Lt ∘ φ'` of the same `L` for the relabelled pairings. (Applied to the
  bit and trace pairings of `GF(2⁸)`, this would relate the bit adjoint of a field matrix to its
  field transpose; that instance is not constructed here.)
* `isAdjoint_transpose`: a bundle transposition `transpose p` has `transpose p⁻¹` as an adjoint,
  for the bundle-sum pairing of any bundle pairing.
* `isAdjoint_mul_left`, `isAdjoint_mulVec`, `isAdjoint_colMatrix`: for every trace-form pairing
  `⟨u, x⟩ = ℓ (u * x)`, multiplication by a constant is an adjoint of itself, and the transpose
  of a matrix over the ring is an adjoint of the matrix (applied to a vector, or column by
  column to a grid). These are the only adjoints when the pairing is separating
  (`IsAdjoint.unique`). Without separation they need not be: under the zero trace form every
  map is an adjoint of every map (`isAdjoint_traceForm_zero`).
* `isBranchBound_symm_iff`: an additive bijection and its inverse have the same branch-number
  lower bounds.
* `IsLinBranchBound` (Daemen and Rijmen's linear branch number, through correlations) and
  `isLinBranchBound_iff`: for a separating pairing into a domain in which `|X|` is nonzero, `B`
  is a linear branch-number lower bound for a map with an adjoint `Lt` exactly when it is a
  differential branch-number lower bound for `Lt`. With `isAdjoint_mulVec` this covers
  `x ↦ A x` under the dot product (the trace form of the identity), the setting in which
  `Algebra/Transpose.lean` takes this identification as a definition, once a separating character
  is supplied. That file is not changed.
* `isTrail_iff_backward`: the forward and backward readings of a mask trail agree.

## What is not claimed

Branch numbers are lower bounds here, as everywhere in this library; nothing says they are
attained. No correlation bound for any S-box, trail or cipher is stated in this file.
-/

set_option autoImplicit false

namespace Linear

variable {W X Y Z G R : Type*} [AddCommGroup W] [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup Z] [AddCommGroup G] [CommRing R]

/-! ### Adjoint calculus -/

section Calculus

/-- **Adjoints compose**, in the reverse order: `(M ∘ L)ᵀ = Lᵀ ∘ Mᵀ`. -/
theorem IsAdjoint.comp {P₁ : Pairing X G} {P₂ : Pairing Y G} {P₃ : Pairing Z G}
    {L : X → Y} {Lt : Y → X} {M : Y → Z} {Mt : Z → Y}
    (hL : IsAdjoint P₁ P₂ L Lt) (hM : IsAdjoint P₂ P₃ M Mt) :
    IsAdjoint P₁ P₃ (fun x => M (L x)) (fun w => Lt (Mt w)) := fun w x => by rw [hM, hL]

/-- **The inverse of an adjoint is an adjoint of the inverse**: if `Lt` is an adjoint of the
bijection `L`, then `Lt⁻¹` is an adjoint of `L⁻¹`. -/
theorem IsAdjoint.symm {P : Pairing Y G} {Q : Pairing Z G} {L : Y ≃ Z} {Lt : Z ≃ Y}
    (h : IsAdjoint P Q L Lt) : IsAdjoint Q P L.symm Lt.symm := fun v y => by
  have := h (Lt.symm v) (L.symm y)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact this.symm

/-- **Masks move forward through the inverse of an adjoint**, contragrediently to states:
`⟨Lt⁻¹ w, L y⟩ = ⟨w, y⟩`. -/
theorem IsAdjoint.dot_symm_apply {P : Pairing Y G} {Q : Pairing Z G} {L : Y → Z} {Lt : Z ≃ Y}
    (h : IsAdjoint P Q L Lt) (w y : Y) : Q.dot (Lt.symm w) (L y) = P.dot w y := by
  rw [h, Equiv.apply_symm_apply]

variable {ψ : AddChar G R}

/-- **An adjoint is unique** when the pairing on the source of `L` is separating. -/
theorem IsAdjoint.unique {P : Pairing Y G} {Q : Pairing Z G} (hP : P.Separating ψ)
    {L : Y → Z} {Lt Lt' : Z → Y} (h : IsAdjoint P Q L Lt) (h' : IsAdjoint P Q L Lt') :
    Lt = Lt' :=
  funext fun v => hP.ext_left fun y => by rw [← h, ← h']

/-- An adjoint sends the zero mask to the zero mask, when the source pairing is separating. -/
theorem IsAdjoint.map_zero {P : Pairing Y G} {Q : Pairing Z G} (hP : P.Separating ψ)
    {L : Y → Z} {Lt : Z → Y} (h : IsAdjoint P Q L Lt) : Lt 0 = 0 :=
  hP.eq_zero_of_dot_left fun y => by
    rw [← h, _root_.map_zero, AddMonoidHom.zero_apply]

/-- An adjoint is additive, when the source pairing is separating. -/
theorem IsAdjoint.map_add {P : Pairing Y G} {Q : Pairing Z G} (hP : P.Separating ψ)
    {L : Y → Z} {Lt : Z → Y} (h : IsAdjoint P Q L Lt) (v w : Z) :
    Lt (v + w) = Lt v + Lt w :=
  hP.ext_left fun y => by
    rw [← h, _root_.map_add, AddMonoidHom.add_apply, h, h, _root_.map_add,
      AddMonoidHom.add_apply]

/-- **Pulling pairings back conjugates an adjoint.** If `Lt` is an adjoint of `L` for `P` and
`Q`, then `e⁻¹ ∘ Lt ∘ f` is an adjoint of `f⁻¹ ∘ L ∘ e` for the pairings pulled back along `e`
and `f`. -/
theorem IsAdjoint.comap {P : Pairing Y G} {Q : Pairing Z G} (e : X ≃+ Y) (f : W ≃+ Z)
    {L : Y → Z} {Lt : Z → Y} (h : IsAdjoint P Q L Lt) :
    IsAdjoint (P.comap e.toAddMonoidHom) (Q.comap f.toAddMonoidHom)
      (fun x => f.symm (L (e x))) (fun w => e.symm (Lt (f w))) := fun w x => by
  simp only [Pairing.comap_dot, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  exact h (f w) (e x)

/-- **Relabelling masks moves an adjoint.** If `⟨u, y⟩' = ⟨φ u, y⟩` on the source of `L` and
`⟨v, z⟩' = ⟨φ' v, z⟩` on its target, an adjoint `Lt` for the unprimed pairings gives the adjoint
`φ⁻¹ ∘ Lt ∘ φ'` of `L` for the primed ones. States, and so `L`, are not moved. -/
theorem IsAdjoint.maskRelabel {P P' : Pairing Y G} {Q Q' : Pairing Z G} (φ : Y ≃ Y)
    {φ' : Z → Z} (hP : ∀ u y, P'.dot u y = P.dot (φ u) y)
    (hQ : ∀ v z, Q'.dot v z = Q.dot (φ' v) z) {L : Y → Z} {Lt : Z → Y}
    (h : IsAdjoint P Q L Lt) : IsAdjoint P' Q' L (fun v => φ.symm (Lt (φ' v))) := fun v y => by
  rw [hQ, hP, Equiv.apply_symm_apply, h]

end Calculus

/-! ### Concrete adjoints -/

section Concrete

/-- **A bundle transposition has its inverse as an adjoint**, for the bundle-sum pairing of any
bundle pairing. -/
theorem isAdjoint_transpose {Idx K : Type*} [Fintype Idx] [AddCommGroup K] (P : Pairing K G)
    (p : Equiv.Perm Idx) :
    IsAdjoint P.pi P.pi (transpose p : (Idx → K) → (Idx → K)) (transpose p.symm) :=
  fun v y => by
    simp only [Pairing.pi_dot, transpose]
    exact Fintype.sum_equiv p _ _ (fun i => by rw [Equiv.symm_apply_apply])

/-- **Under every trace-form pairing, multiplication by a constant is an adjoint of itself**:
`ℓ (v * (c * y)) = ℓ ((c * v) * y)`. -/
theorem isAdjoint_mul_left {K : Type*} [CommRing K] (ℓ : K →+ G) (c : K) :
    IsAdjoint (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) (fun y => c * y) (fun v => c * v) :=
  fun v y => by
    simp only [Pairing.traceForm_dot]
    rw [mul_left_comm, ← mul_assoc]

/-- **Without separation an adjoint need not be unique**: under the zero trace form, `ℓ = 0`,
every map `Lt` is an adjoint of every map `L`. -/
theorem isAdjoint_traceForm_zero {K : Type*} [CommRing K] (L Lt : K → K) :
    IsAdjoint (Pairing.traceForm (0 : K →+ G)) (Pairing.traceForm (0 : K →+ G)) L Lt :=
  fun v y => by simp only [Pairing.traceForm_dot, AddMonoidHom.zero_apply]

/-- **Under every trace-form pairing, the transpose of a matrix over the ring is an adjoint of
the matrix**, for the bundle-sum pairing: `⟨v, N y⟩ = ⟨Nᵀ v, y⟩`. It is the only adjoint when the
pairing is separating (`IsAdjoint.unique`). -/
theorem isAdjoint_mulVec {m n K : Type*} [Fintype m] [Fintype n] [CommRing K] (ℓ : K →+ G)
    (N : Matrix m n K) :
    IsAdjoint (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi N.mulVec N.transpose.mulVec :=
  fun v y => by
    simp only [Pairing.pi_dot, Pairing.traceForm_dot]
    rw [← map_sum, ← map_sum]
    congr 1
    change v ⬝ᵥ N.mulVec y = N.transpose.mulVec v ⬝ᵥ y
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **A matrix applied column by column has its transpose, applied column by column, as an
adjoint**, for every trace-form pairing. The column-wise action is written inline, so it is
definitionally the shape of a `MixColumns` layer on a `rows × cols` grid. -/
theorem isAdjoint_colMatrix {Row Col K : Type*} [Fintype Row] [Fintype Col] [CommRing K]
    (ℓ : K →+ G) (N : Matrix Row Row K) :
    IsAdjoint (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi
      (fun (a : Row × Col → K) i => N.mulVec (fun r => a (r, i.2)) i.1)
      (fun (a : Row × Col → K) i => N.transpose.mulVec (fun r => a (r, i.2)) i.1) :=
  fun v y => by
    simp only [Pairing.pi_dot]
    rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h := isAdjoint_mulVec ℓ N (fun r => v (r, c)) (fun r => y (r, c))
    simpa only [Pairing.pi_dot] using h

end Concrete

/-! ### Branch numbers -/

section Branch

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [AddCommGroup K] [DecidableEq K]

/-- **An additive bijection and its inverse have the same branch-number lower bounds.** The
code `{(x, e x)}` is the code `{(e⁻¹ y, y)}` with the halves exchanged. -/
theorem isBranchBound_symm_iff (e : (Idx → K) ≃+ (Idx → K)) (B : ℕ) :
    isBranchBound id e.symm B ↔ isBranchBound id e B := by
  constructor
  · intro h a ha
    have := h (e a) ((map_ne_zero_iff e e.injective).mpr ha)
    rw [AddEquiv.symm_apply_apply] at this
    omega
  · intro h a ha
    have := h (e.symm a) ((map_ne_zero_iff e.symm e.symm.injective).mpr ha)
    rw [AddEquiv.apply_symm_apply] at this
    omega

variable [Fintype K]

/-- `B` is a **linear branch-number lower bound** for `L` (Daemen and Rijmen's linear branch
number, defined through correlations): every pair of masks `(u, v) ≠ (0, 0)` at which `L` has a
nonzero Walsh value has at least `B` active bundles across input and output together. -/
def IsLinBranchBound (ψ : AddChar G R) (P : Pairing K G) (L : (Idx → K) → (Idx → K))
    (B : ℕ) : Prop :=
  ∀ u v : Idx → K, (u ≠ 0 ∨ v ≠ 0) → walsh ψ P.pi P.pi L u v ≠ 0 → B ≤ weight u + weight v

/-- **The linear branch number of a map is the differential branch number of its adjoint.** For
a separating bundle pairing into a domain in which `|Idx → K|` is nonzero, and `Lt` an adjoint
of `L` for the bundle-sum pairing, `B` is a linear branch-number lower bound for `L` exactly when
it is a branch-number lower bound for `Lt`. By (W7) the nonzero Walsh values of `L` sit exactly
at the pairs `(Lt v, v)`. -/
theorem isLinBranchBound_iff [IsDomain R] {ψ : AddChar G R} {P : Pairing K G}
    (hP : P.Separating ψ) (hcard : (Fintype.card (Idx → K) : R) ≠ 0)
    {L Lt : (Idx → K) → (Idx → K)} (hadj : IsAdjoint P.pi P.pi L Lt) (B : ℕ) :
    IsLinBranchBound ψ P L B ↔ isBranchBound id Lt B := by
  have hPi : (P.pi (Idx := Idx)).Separating ψ := hP.pi
  constructor
  · intro h a ha
    have hw : walsh ψ P.pi P.pi L (Lt a) a ≠ 0 := by
      rw [walsh_of_adjoint hPi hadj, if_pos rfl]
      exact hcard
    have := h (Lt a) a (Or.inr ha) hw
    rw [colWeight_id, colWeight_id]
    omega
  · intro h u v huv hw
    rw [walsh_of_adjoint hPi hadj] at hw
    by_cases hu : u = Lt v
    · subst hu
      have hv : v ≠ 0 := by
        rintro rfl
        rcases huv with h0 | h0
        · exact h0 (hadj.map_zero hPi)
        · exact h0 rfl
      have := h v hv
      rw [colWeight_id, colWeight_id] at this
      omega
    · exact absurd (if_neg hu) hw

end Branch

/-! ### Forward and backward readings of a mask trail -/

/-- **The forward and backward readings of a mask trail agree.** If `lamT` is injective and
undoes the forward mask map `S.lin`, then `S.IsTrail T r` holds exactly when, for every
`n < r`, the S-box output mask `lamT (T (n + 1))` has the support of the S-box input mask
`T n`. -/
theorem isTrail_iff_backward {Idx Col K : Type*} [Fintype Idx] [DecidableEq Idx]
    [DecidableEq Col] [Fintype Col] [Zero K] [DecidableEq K] (S : WideTrailSpec Idx Col K)
    {lamT : (Idx → K) → (Idx → K)} (hinj : Function.Injective lamT)
    (hlam : ∀ b, lamT (S.lin b) = b) (T : ℕ → Idx → K) (r : ℕ) :
    S.IsTrail T r ↔ ∀ n < r, activePattern (lamT (T (n + 1))) = activePattern (T n) := by
  constructor
  · intro h n hn
    obtain ⟨b, hb, he⟩ := h n hn
    rw [he, hlam]
    exact hb
  · intro h n hn
    exact ⟨lamT (T (n + 1)), h n hn, hinj (hlam _).symm⟩

end Linear
