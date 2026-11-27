/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Differential.Bricklayer
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Correlations as character sums

Linear cryptanalysis measures how well a linear function of the input `x ↦ ⟨u, x⟩` predicts a
linear function of the output `x ↦ ⟨v, F x⟩`. This file sets that up for any finite additive
group of states, with three ingredients:

* a **pairing** `P : Pairing X G`, a bi-additive map `⟨·, ·⟩ : X × X → G` of masks with states
  (masks and states share the type `X`);
* an **additive character** `ψ : AddChar G R` into a commutative ring `R`: `t ↦ (-1)ᵗ` from
  `ZMod 2` to `ℤ` (`Linear.sign₂`, in `Binary.lean`) or a character of `ZMod p` into `ℂ`;
* the **Walsh value** `walsh ψ P Q F u v = ∑ₓ ψ (⟨v, F x⟩ - ⟨u, x⟩)`.

The correlation of `F` at the masks `(u, v)` is `walsh ψ P Q F u v / |X|`. As
`Differential/Counts.lean` keeps the numerator `diffCount` and never divides, everything here
keeps the numerator `walsh`, so every statement is an exact identity in `R`.

## The pairing is a choice

A Walsh value depends on the pairing, and the pairing is chosen per instance. For a cipher over
`GF(2⁸)` with field-linear layers (AES, Rijndael) the natural choice is a trace-form pairing
`⟨u, x⟩ = ℓ (u * x)` (`Pairing.traceForm`): under it the field transpose of a field matrix is an
adjoint of the matrix (`Linear.isAdjoint_mulVec` in `Masks.lean`), and the only one when the
pairing is separating (`Linear.IsAdjoint.unique`). For a byte cipher without field structure
the natural choice is the bit pairing, the dot product of bit vectors (`Linear.bitPairing` in
`Binary.lean`). Nothing here makes either pairing *the* pairing of a type. Two pairings related by
a relabelling of the masks, `⟨u, x⟩' = ⟨φ u, x⟩`, have the same Walsh values at relabelled masks
(`walsh_maskRelabel`). The multiplication pairing `mulPairing K`, `⟨u, x⟩ = u * x`, is the
trace form of the identity; it is the pairing of `ZMod 2` for bit vectors and of `ZMod p` for
prime-field states.

## What is proved

The identities, with the labels used in the design of this layer:

* (W1) `walsh_addKey`: a key added before `F` multiplies the Walsh value by `ψ ⟨u, k⟩`.
* (W2) `walsh_postAdd`: a constant added after `F` multiplies it by `ψ ⟨v, c⟩`.
* (W3) `walsh_comp_adjoint`: a map `L` after `F` moves the output mask through an adjoint of `L`
  (`IsAdjoint`): `walsh (L ∘ F) u v = walsh F u (Lt v)`.
* (W4) `walsh_bricklayer`: for the sum pairing of bundles (`Pairing.pi`), the Walsh value of a
  bricklayer map is the product of the S-boxes' Walsh values.
* (W5) `sum_char_dot`, `sum_char_dot_left`: orthogonality, `∑ᵤ ψ ⟨u, x⟩ = |X|·[x = 0]` and
  `∑ₓ ψ ⟨u, x⟩ = |X|·[u = 0]`.
* (W6) `walsh_comp`: correlation matrices multiply,
  `|Y| · walsh (H ∘ F) u w = ∑ᵥ walsh F u v · walsh H v w`.
* (W7) `walsh_of_adjoint`: a map with an adjoint has `walsh L u v = |X|·[u = Lt v]`.
* (W8) `walsh_zero_right`, `walsh_zero_left`: a nonzero input mask has Walsh value `0` with the
  zero output mask, for every map; the zero input mask has Walsh value `0` with a nonzero output
  mask, for a bijection. Hence `activePattern_eq_of_walsh_ne_zero`: through a bricklayer of
  bijections, a nonzero Walsh value forces the input and output masks to have the same support.
* (W9) `sum_walsh_mul_walsh_neg_left`, `sum_walsh_mul_walsh_neg_right`: Parseval, in the form
  `∑ W(u, v) · W(-u, -v)`. For a pairing separating on the input side, columns sum to `|X|²`
  for every map; for one separating on the output side, rows sum to `|X| · |Y|` when `F` is
  injective. `Binary.lean` turns `W(-u, -v)` into `W(u, v)` for `ZMod 2`-valued pairings.
* (W10) `walsh_inv_mul`: under a trace-form pairing on a field, inversion has one component
  function up to scaling of the input mask: `walsh (·⁻¹) a β = walsh (·⁻¹) (a * β) 1` for
  `β ≠ 0`.

**Which identities need what.** (W1)-(W4) and (W10) are exact for every pairing and every
character, with no hypothesis on either ((W10) assumes `β ≠ 0`). (W5)-(W9) need the pairing to
be *separating* for `ψ` (`Pairing.Separating`: `x ↦ ψ ⟨u, x⟩` is a nontrivial character for
`u ≠ 0`, and the same on the other side) and `R` to be a domain (`[IsDomain R]`): orthogonality
cancels a factor `1 - ψ ⟨u₀, x⟩`. (W8)'s second half also needs `F` bijective, and the row half
of (W9) needs `F` injective. `Checks/Character.lean` shows a degenerate pairing breaking (W6).

## What is not claimed

Nothing here is about a cipher, a key schedule or an attack. The identities are about a single
map at a time; no bound on any correlation is stated in this file.
-/

set_option autoImplicit false

namespace Linear

/-- A bi-additive pairing `⟨u, x⟩` of masks `u` with states `x`, valued in `G`. Masks and states
share the type `X`. -/
structure Pairing (X G : Type*) [AddCommGroup X] [AddCommGroup G] where
  /-- `dot u x` is the pairing `⟨u, x⟩`, additive in each argument. -/
  dot : X →+ X →+ G

variable {X Y Z G R : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [AddCommGroup G] [CommRing R]

/-- `P` is separating for the character `ψ`: for every nonzero mask `u` the character
`x ↦ ψ ⟨u, x⟩` is nontrivial, and for every nonzero state `x` the character `u ↦ ψ ⟨u, x⟩` is
nontrivial. -/
structure Pairing.Separating (ψ : AddChar G R) (P : Pairing X G) : Prop where
  /-- A nonzero mask is seen by some state. -/
  left : ∀ u : X, u ≠ 0 → ∃ x, ψ (P.dot u x) ≠ 1
  /-- A nonzero state is seen by some mask. -/
  right : ∀ x : X, x ≠ 0 → ∃ u, ψ (P.dot u x) ≠ 1

/-- The Walsh value of `F` at the input mask `u` and the output mask `v`:
`∑ₓ ψ (⟨v, F x⟩ - ⟨u, x⟩)`. Divided by `|X|` it is the correlation of `x ↦ ⟨v, F x⟩` with
`x ↦ ⟨u, x⟩`. -/
def walsh [Fintype X] (ψ : AddChar G R) (P : Pairing X G) (Q : Pairing Y G) (F : X → Y)
    (u : X) (v : Y) : R :=
  ∑ x, ψ (Q.dot v (F x) - P.dot u x)

/-- `Lt` is an adjoint of `L` for the pairings `Q` (on the source of `L`) and `Q'` (on its
target): `⟨v, L y⟩ = ⟨Lt v, y⟩` for every mask `v` and state `y`. -/
def IsAdjoint (Q : Pairing Y G) (Q' : Pairing Z G) (L : Y → Z) (Lt : Z → Y) : Prop :=
  ∀ v y, Q'.dot v (L y) = Q.dot (Lt v) y

/-! ### Building pairings -/

section Constructions

/-- The pairing of states made of bundles: `⟨u, x⟩ = ∑ᵢ ⟨uᵢ, xᵢ⟩`. -/
def Pairing.pi {Idx K : Type*} [Fintype Idx] [AddCommGroup K] (P : Pairing K G) :
    Pairing (Idx → K) G where
  dot :=
    { toFun := fun u =>
        { toFun := fun x => ∑ i, P.dot (u i) (x i)
          map_zero' := by simp
          map_add' := fun x y => by simp [Finset.sum_add_distrib] }
      map_zero' := by ext; simp
      map_add' := fun u u' => by ext; simp [Finset.sum_add_distrib] }

@[simp] theorem Pairing.pi_dot {Idx K : Type*} [Fintype Idx] [AddCommGroup K]
    (P : Pairing K G) (u x : Idx → K) :
    (P.pi (Idx := Idx)).dot u x = ∑ i, P.dot (u i) (x i) := rfl

/-- The trace-form pairing of a commutative ring: `⟨u, x⟩ = ℓ (u * x)`. -/
def Pairing.traceForm {K : Type*} [CommRing K] (ℓ : K →+ G) : Pairing K G where
  dot := AddMonoidHom.mul.compr₂ ℓ

@[simp] theorem Pairing.traceForm_dot {K : Type*} [CommRing K] (ℓ : K →+ G) (u x : K) :
    (Pairing.traceForm ℓ).dot u x = ℓ (u * x) := rfl

/-- The multiplication pairing of a commutative ring, `⟨u, x⟩ = u * x`: the trace form of the
identity. For `ZMod 2` this is the pairing of one bit, and `(mulPairing (ZMod 2)).pi` is the dot
product of bit vectors; for `ZMod p` it is the pairing of a prime-field state element. -/
abbrev mulPairing (K : Type*) [CommRing K] : Pairing K K :=
  Pairing.traceForm (AddMonoidHom.id K)

@[simp] theorem mulPairing_dot (K : Type*) [CommRing K] (u x : K) :
    (mulPairing K).dot u x = u * x := rfl

/-- A pairing pulled back along an additive map: `⟨u, x⟩ = ⟨f u, f x⟩`. -/
def Pairing.comap (f : X →+ Y) (Q : Pairing Y G) : Pairing X G where
  dot := (Q.dot.comp f).compl₂ f

@[simp] theorem Pairing.comap_dot (f : X →+ Y) (Q : Pairing Y G) (u x : X) :
    (Q.comap f).dot u x = Q.dot (f u) (f x) := rfl

end Constructions

/-! ### Separation -/

section Separation

variable {ψ : AddChar G R}

/-- A separating pairing is nondegenerate on the mask side. -/
theorem Pairing.Separating.eq_zero_of_dot_left {P : Pairing X G} (hP : P.Separating ψ)
    {u : X} (h : ∀ x, P.dot u x = 0) : u = 0 := by
  by_contra hu
  obtain ⟨x, hx⟩ := hP.left u hu
  exact hx (by rw [h x, AddChar.map_zero_eq_one])

/-- A separating pairing is nondegenerate on the state side. -/
theorem Pairing.Separating.eq_zero_of_dot_right {P : Pairing X G} (hP : P.Separating ψ)
    {x : X} (h : ∀ u, P.dot u x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨u, hu⟩ := hP.right x hx
  exact hu (by rw [h u, AddChar.map_zero_eq_one])

/-- Under a separating pairing a mask is determined by how it reads every state. -/
theorem Pairing.Separating.ext_left {P : Pairing X G} (hP : P.Separating ψ) {u u' : X}
    (h : ∀ x, P.dot u x = P.dot u' x) : u = u' :=
  sub_eq_zero.mp (hP.eq_zero_of_dot_left fun x => by
    rw [map_sub, AddMonoidHom.sub_apply, h x, sub_self])

/-- The sum pairing of bundles is separating when the bundle pairing is. -/
theorem Pairing.Separating.pi {Idx K : Type*} [Fintype Idx] [AddCommGroup K]
    {P : Pairing K G} (hP : P.Separating ψ) : (P.pi (Idx := Idx)).Separating ψ where
  left u hu := by
    classical
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    obtain ⟨x, hx⟩ := hP.left (u i) hi
    refine ⟨Pi.single i x, ?_⟩
    rw [Pairing.pi_dot, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp), Pi.single_eq_same]
    exact hx
  right x hx := by
    classical
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    obtain ⟨u, hu⟩ := hP.right (x i) hi
    refine ⟨Pi.single i u, ?_⟩
    rw [Pairing.pi_dot, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, AddMonoidHom.zero_apply])
      (by simp), Pi.single_eq_same]
    exact hu

/-- A pairing pulled back along an additive bijection is separating when the original is. -/
theorem Pairing.Separating.comap {Q : Pairing Y G} (hQ : Q.Separating ψ) (e : X ≃+ Y) :
    (Q.comap e.toAddMonoidHom).Separating ψ where
  left u hu := by
    obtain ⟨y, hy⟩ := hQ.left (e u) ((map_ne_zero_iff e e.injective).mpr hu)
    exact ⟨e.symm y, by simpa using hy⟩
  right x hx := by
    obtain ⟨v, hv⟩ := hQ.right (e x) ((map_ne_zero_iff e e.injective).mpr hx)
    exact ⟨e.symm v, by simpa using hv⟩

/-- A trace-form pairing on a field is separating as soon as `ψ ∘ ℓ` is a nontrivial
character. -/
theorem Pairing.traceForm_separating {K : Type*} [Field K] (ℓ : K →+ G) {t : K}
    (ht : ψ (ℓ t) ≠ 1) : (Pairing.traceForm ℓ).Separating ψ where
  left u hu := ⟨u⁻¹ * t, by rwa [Pairing.traceForm_dot, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]⟩
  right x hx := ⟨t * x⁻¹, by rwa [Pairing.traceForm_dot, mul_assoc, inv_mul_cancel₀ hx, mul_one]⟩

end Separation

/-! ### Orthogonality -/

/-- A character turns a finite sum into a product. -/
theorem addChar_map_sum {ι M : Type*} [CommMonoid M] (ψ : AddChar G M) (s : Finset ι)
    (f : ι → G) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

section Orthogonality

variable [Fintype X] [IsDomain R] (ψ : AddChar G R)

/-- A nontrivial character of `X`, given as `ψ ∘ f`, sums to `0`. -/
theorem sum_addChar_comp_eq_zero (f : X →+ G) {x₀ : X} (h : ψ (f x₀) ≠ 1) :
    ∑ x, ψ (f x) = 0 := by
  have hshift : ∑ x, ψ (f x) = ψ (f x₀) * ∑ x, ψ (f x) := by
    rw [Finset.mul_sum]
    exact (Fintype.sum_equiv (Equiv.addRight x₀) _ _
      (fun x => by rw [Equiv.coe_addRight, map_add, AddChar.map_add_eq_mul, mul_comm])).symm
  have h1 : (1 - ψ (f x₀)) * ∑ x, ψ (f x) = 0 := by
    rw [sub_mul, one_mul, ← hshift, sub_self]
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm h))

variable [DecidableEq X] {ψ}

/-- **(W5) Orthogonality over masks.** For a separating pairing,
`∑ᵤ ψ ⟨u, x⟩ = |X|` if `x = 0` and `0` otherwise. -/
theorem sum_char_dot {P : Pairing X G} (hP : P.Separating ψ) (x : X) :
    ∑ u : X, ψ (P.dot u x) = if x = 0 then (Fintype.card X : R) else 0 := by
  split_ifs with hx
  · subst hx
    simp
  · obtain ⟨u₀, hu₀⟩ := hP.right x hx
    exact sum_addChar_comp_eq_zero ψ (P.dot.flip x) hu₀

/-- **(W5) Orthogonality over states.** For a separating pairing,
`∑ₓ ψ ⟨u, x⟩ = |X|` if `u = 0` and `0` otherwise. -/
theorem sum_char_dot_left {P : Pairing X G} (hP : P.Separating ψ) (u : X) :
    ∑ x : X, ψ (P.dot u x) = if u = 0 then (Fintype.card X : R) else 0 := by
  split_ifs with hu
  · subst hu
    simp
  · obtain ⟨x₀, hx₀⟩ := hP.left u hu
    exact sum_addChar_comp_eq_zero ψ (P.dot u) hx₀

end Orthogonality

/-! ### Exact identities -/

section Identities

variable [Fintype X] (ψ : AddChar G R) (P : Pairing X G) (Q : Pairing Y G)

/-- **(W1) A key before `F`.** Adding `k` to the input multiplies the Walsh value by
`ψ ⟨u, k⟩`. -/
theorem walsh_addKey (F : X → Y) (k u : X) (v : Y) :
    walsh ψ P Q (fun x => F (x + k)) u v = ψ (P.dot u k) * walsh ψ P Q F u v := by
  unfold walsh
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight k) _ _ (fun x => ?_)
  simp only [Equiv.coe_addRight, map_add]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  abel

/-- **(W2) A constant after `F`.** Adding `c` to the output multiplies the Walsh value by
`ψ ⟨v, c⟩`. -/
theorem walsh_postAdd (F : X → Y) (c : Y) (u : X) (v : Y) :
    walsh ψ P Q (fun x => F x + c) u v = ψ (Q.dot v c) * walsh ψ P Q F u v := by
  unfold walsh
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← AddChar.map_add_eq_mul, map_add]
  congr 1
  abel

/-- **(W3) A map after `F` moves the output mask through an adjoint.** -/
theorem walsh_comp_adjoint (Q' : Pairing Z G) {L : Y → Z} {Lt : Z → Y}
    (h : IsAdjoint Q Q' L Lt) (F : X → Y) (u : X) (v : Z) :
    walsh ψ P Q' (fun x => L (F x)) u v = walsh ψ P Q F u (Lt v) := by
  unfold walsh
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [h]

/-- **(W4) A bricklayer's Walsh value factors over bundles**, for the sum pairing of the
bundles. -/
theorem walsh_bricklayer {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [AddCommGroup K]
    [Fintype K] (P : Pairing K G) (s : Idx → K → K) (u v : Idx → K) :
    walsh ψ P.pi P.pi (bricklayer s) u v = ∏ i, walsh ψ P P (s i) (u i) (v i) := by
  unfold walsh
  rw [Finset.prod_univ_sum]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ (fun x => ?_)
  simp only [Pairing.pi_dot, bricklayer, Equiv.refl_apply, ← Finset.sum_sub_distrib]
  exact addChar_map_sum ψ _ _

/-- The zero masks: `walsh F 0 0 = |X|`. -/
theorem walsh_zero_zero (F : X → Y) : walsh ψ P Q F 0 0 = Fintype.card X := by
  simp [walsh]

/-- **(W10) Inversion has one component function**, up to scaling of the input mask: under a
trace-form pairing on a field, `walsh (·⁻¹) a β = walsh (·⁻¹) (a * β) 1` for `β ≠ 0`. -/
theorem walsh_inv_mul {K : Type*} [Field K] [Fintype K] (ℓ : K →+ G) (a β : K) (hβ : β ≠ 0) :
    walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) (fun x => x⁻¹) a β
      = walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) (fun x => x⁻¹) (a * β) 1 := by
  unfold walsh
  refine (Fintype.sum_bijective (fun z => β * z) (mulLeft_bijective₀ β hβ) _ _
    (fun z => ?_)).symm
  simp only [Pairing.traceForm_dot, one_mul, mul_inv, mul_assoc]
  rw [mul_inv_cancel_left₀ hβ]

/-- **Relabelling masks.** If `⟨u, x⟩' = ⟨φ u, x⟩` on inputs and `⟨v, y⟩' = ⟨φ' v, y⟩` on
outputs, the Walsh values for the primed pairings are the Walsh values for the unprimed ones at
the relabelled masks. States are not moved, so `F` is unchanged. -/
theorem walsh_maskRelabel {P' : Pairing X G} {Q' : Pairing Y G} {φ : X → X} {φ' : Y → Y}
    (hP : ∀ u x, P'.dot u x = P.dot (φ u) x) (hQ : ∀ v y, Q'.dot v y = Q.dot (φ' v) y)
    (F : X → Y) (u : X) (v : Y) :
    walsh ψ P' Q' F u v = walsh ψ P Q F (φ u) (φ' v) := by
  unfold walsh
  simp only [hP, hQ]

/-- **Moving states and masks together.** Pulling both pairings back along additive bijections
`e` and `f` conjugates the map: the Walsh values of `f⁻¹ ∘ F ∘ e` for the pulled-back pairings
are the Walsh values of `F` at the moved masks. -/
theorem walsh_comap [Fintype Y] (e : X ≃+ Y) (f : X ≃+ Y) (F : Y → Y) (u v : X) :
    walsh ψ (Q.comap e.toAddMonoidHom) (Q.comap f.toAddMonoidHom) (fun x => f.symm (F (e x)))
      u v = walsh ψ Q Q F (e u) (f v) := by
  unfold walsh
  refine Fintype.sum_equiv e.toEquiv _ _ (fun x => ?_)
  simp

/-- The product `W(u, v) · W(-u, -v)` as a double sum over pairs of states. -/
theorem walsh_mul_walsh_neg (F : X → Y) (u : X) (v : Y) :
    walsh ψ P Q F u v * walsh ψ P Q F (-u) (-v)
      = ∑ x, ∑ y, ψ (Q.dot v (F x - F y)) * ψ (P.dot u (y - x)) := by
  unfold walsh
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [map_neg, map_sub, AddMonoidHom.neg_apply]
  abel

end Identities

/-! ### Identities that need separation -/

section Separated

variable [Fintype X] [IsDomain R] {ψ : AddChar G R} {P : Pairing X G} {Q : Pairing Y G}

/-- **(W6) Correlation matrices multiply.** For a pairing `Q` separating on the intermediate
space, `|Y| · walsh (H ∘ F) u w = ∑ᵥ walsh F u v · walsh H v w`. -/
theorem walsh_comp [Fintype Y] (Q' : Pairing Z G) (hQ : Q.Separating ψ)
    (F : X → Y) (H : Y → Z) (u : X) (w : Z) :
    (Fintype.card Y : R) * walsh ψ P Q' (fun x => H (F x)) u w
      = ∑ v, walsh ψ P Q F u v * walsh ψ Q Q' H v w := by
  classical
  unfold walsh
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  have key : ∀ y : Y, ∑ v : Y, ψ (Q.dot v (F x) - P.dot u x) * ψ (Q'.dot w (H y) - Q.dot v y)
      = ψ (Q'.dot w (H y) - P.dot u x) * ∑ v : Y, ψ (Q.dot v (F x - y)) := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_sub]
    congr 1
    abel
  simp_rw [key, sum_char_dot hQ, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (F x), if_pos (Finset.mem_univ _), mul_comm]

/-- **(W7) The Walsh value of a map with an adjoint.** If `Lt` is an adjoint of `L` and the
pairing on the source is separating, `walsh L u v = |X|` when `u = Lt v` and `0` otherwise. -/
theorem walsh_of_adjoint [DecidableEq X] (hP : P.Separating ψ) {L : X → Y} {Lt : Y → X}
    (h : IsAdjoint P Q L Lt) (u : X) (v : Y) :
    walsh ψ P Q L u v = if u = Lt v then (Fintype.card X : R) else 0 := by
  unfold walsh
  have hterm : ∀ x, Q.dot v (L x) - P.dot u x = P.dot (Lt v - u) x := fun x => by
    rw [h, map_sub, AddMonoidHom.sub_apply]
  simp_rw [hterm, sum_char_dot_left hP, sub_eq_zero, eq_comm]

/-- **(W8) The zero output mask.** A nonzero input mask has Walsh value `0` with the zero output
mask, for every map. -/
theorem walsh_zero_right (hP : P.Separating ψ) (F : X → Y) {u : X} (hu : u ≠ 0) :
    walsh ψ P Q F u 0 = 0 := by
  classical
  unfold walsh
  have hterm : ∀ x, Q.dot 0 (F x) - P.dot u x = P.dot (-u) x := fun x => by
    rw [map_zero, AddMonoidHom.zero_apply, zero_sub, map_neg, AddMonoidHom.neg_apply]
  simp_rw [hterm, sum_char_dot_left hP, neg_eq_zero, if_neg hu]

/-- **(W8) The zero input mask.** For a bijection and a pairing separating on the target, the
zero input mask has Walsh value `0` with every nonzero output mask. -/
theorem walsh_zero_left (hQ : Q.Separating ψ) {F : X → Y}
    (hF : Function.Bijective F) {v : Y} (hv : v ≠ 0) : walsh ψ P Q F 0 v = 0 := by
  classical
  have : Fintype Y := Fintype.ofBijective F hF
  unfold walsh
  simp_rw [map_zero, AddMonoidHom.zero_apply, sub_zero]
  rw [Fintype.sum_bijective F hF _ (fun y => ψ (Q.dot v y)) (fun _ => rfl),
    sum_char_dot_left hQ, if_neg hv]

/-- **Masks keep their support through a bricklayer of bijections.** For a separating bundle
pairing, a nonzero Walsh value of `bricklayer s` at `(u, v)` forces `u` and `v` to be active in
the same bundles. This is the linear twin of `activePattern_eq_of_diffCount_ne_zero`. -/
theorem activePattern_eq_of_walsh_ne_zero {Idx K : Type*} [Fintype Idx] [DecidableEq Idx]
    [AddCommGroup K] [Fintype K] [DecidableEq K] {P : Pairing K G} (hP : P.Separating ψ)
    {s : Idx → K → K} (hs : ∀ i, Function.Bijective (s i)) {u v : Idx → K}
    (h : walsh ψ P.pi P.pi (bricklayer s) u v ≠ 0) : activePattern v = activePattern u := by
  rw [walsh_bricklayer] at h
  have hi : ∀ i, walsh ψ P P (s i) (u i) (v i) ≠ 0 :=
    fun i hz => h (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  ext i
  simp only [mem_activePattern]
  constructor
  · intro hv hu
    exact hi i (by rw [hu]; exact walsh_zero_left hP (hs i) hv)
  · intro hu hv
    exact hi i (by rw [hv]; exact walsh_zero_right hP (s i) hu)

/-- **(W9) Parseval, columns.** For a pairing separating on the source and every map `F`,
`∑ᵤ W(u, v) · W(-u, -v) = |X|²`. -/
theorem sum_walsh_mul_walsh_neg_left (hP : P.Separating ψ) (F : X → Y) (v : Y) :
    ∑ u, walsh ψ P Q F u v * walsh ψ P Q F (-u) (-v)
      = (Fintype.card X : R) * Fintype.card X := by
  classical
  simp_rw [walsh_mul_walsh_neg]
  rw [Finset.sum_comm]
  have hx : ∀ x : X, ∑ u, ∑ y, ψ (Q.dot v (F x - F y)) * ψ (P.dot u (y - x))
      = Fintype.card X := fun x => by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_char_dot hP, sub_eq_zero, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ _), sub_self, map_zero,
      AddChar.map_zero_eq_one, one_mul]
  simp_rw [hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **(W9) Parseval, rows.** For an injective map and a pairing separating on the target,
`∑ᵥ W(u, v) · W(-u, -v) = |X| · |Y|`. -/
theorem sum_walsh_mul_walsh_neg_right [Fintype Y] (hQ : Q.Separating ψ)
    {F : X → Y} (hF : Function.Injective F) (u : X) :
    ∑ v, walsh ψ P Q F u v * walsh ψ P Q F (-u) (-v)
      = (Fintype.card X : R) * Fintype.card Y := by
  classical
  simp_rw [walsh_mul_walsh_neg]
  rw [Finset.sum_comm]
  have hx : ∀ x : X, ∑ v, ∑ y, ψ (Q.dot v (F x - F y)) * ψ (P.dot u (y - x))
      = Fintype.card Y := fun x => by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_char_dot hQ, sub_eq_zero, ite_mul, zero_mul, hF.eq_iff]
    rw [Finset.sum_ite_eq Finset.univ x, if_pos (Finset.mem_univ _), sub_self, map_zero,
      AddChar.map_zero_eq_one, mul_one]
  simp_rw [hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Separated

end Linear
