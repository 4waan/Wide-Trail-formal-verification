/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Trail
import WideTrail.Hades.MiddleBound
import WideTrail.Algebra.Transpose
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Linear trails of HADES rounds

The rounds of `WideTrail.Hades` are `x ↦ L (S_mask (x + c))`: a round constant, the S-boxes on
the coordinates of a mask (identity elsewhere), then a linear equivalence `L` of `Idx → K` over a
field `K`. This file carries masks through such rounds and connects linear trails to the activity
machinery of `WideTrail.Hades` (`IsTrail`, the outer-round bounds, inactive spaces and middle
bounds), for any character into a domain for which the pairing below is separating.

## The pairing and the mask convention

States are paired with masks by the dot product read through an additive map `ℓ : K →+ G`,
`⟨u, x⟩ = ℓ (u ⬝ᵥ x) = ∑ᵢ ℓ (uᵢ xᵢ)`, which is `(Pairing.traceForm ℓ).pi`. For a prime field
`ZMod p` the intended choice is `ℓ = id` (`Linear.mulPairing`). Under it the transpose
`transposeLin L`, the map of the transposed matrix, is an adjoint of `L`. As fixed in `Masks.lean`,
masks are propagated forward through the inverse of the adjoint: `maskLin L = (L⁻¹)ᵀ = (Lᵀ)⁻¹`,
so that `⟨maskLin L w, L x⟩ = ⟨w, x⟩` (`maskLin_dotProduct`). The rounds that carry masks,
`maskSchedule rounds`, keep each round's mask, S-boxes and constant and replace `L` by
`maskLin L`. A linear trail with a nonzero correlation is a `Hades.IsTrail` of the mask schedule
(`isTrail_of_linCorr_ne_zero`), so every activity bound of `WideTrail.Hades` applies to it, with
the branch numbers and middle bounds of the maps `maskLin L`. The backward reading, through
`(maskLin L)⁻¹ = Lᵀ`, is equivalent (`isTrail_maskSchedule_iff_backward`).

## What is proved

* `transposeLin`, `maskLin`, `maskLin_dotProduct`, `maskLin_symm_dotProduct`: the transpose of a
  linear map and the forward mask map. `maskLin_symm_eq_of_dotProduct`: if `L x ⬝ᵥ y = x ⬝ᵥ T y` for
  every `x, y`, then `(maskLin L)⁻¹ = T`; `maskLin_eq_symm_of_selfAdjoint`: for a self-adjoint `L`
  (a symmetric matrix), `maskLin L = L⁻¹`. `dotProduct_of_mulVec`, `selfAdjoint_of_mulVec`: a layer
  `x ↦ M x` has `x ↦ Mᵀ x` as its transpose, and is self-adjoint when `Mᵀ = M`.
* `isAdjoint_of_dotProduct`, `isAdjoint_maskLin`: for every `ℓ`, `(maskLin L)⁻¹` is an adjoint of
  `L` for the pairing `ℓ (u ⬝ᵥ x)`.
* `isBranchBound_maskLin_iff`, `isBranchBound_maskLin_iff_of_selfAdjoint`: the branch-number lower
  bounds of `maskLin L` are those of the transpose of `L`, and for a self-adjoint `L` those of `L`.
  `isBranchBound_maskLin_of_isMDS`: for `L x = M x` with `M` an MDS matrix of size `t`, `maskLin L`
  has branch number at least `t + 1` (`isMDS_transpose_iff`). `isLinBranchBound_iff_maskLin`: for a
  separating `ψ` into a domain with `|Idx → K| ≠ 0` in `R`, `B` is a linear branch-number lower
  bound for `L` (`IsLinBranchBound`) exactly when it is a branch-number lower bound for `maskLin L`.
* `walsh_masked`: for a pairing `P` of `K` separating for `ψ`, into a domain, the Walsh value of a
  masked S-box layer is the product of the S-boxes' Walsh values on the mask and of
  `|K| · [aᵢ = bᵢ]` off it. `walsh_roundGamma`: the round constant contributes a phase.
* `linCorr`: the correlation of a linear trail through HADES rounds, the `trailCorr` of `Trail.lean`
  for the maps `roundGamma` (constant, then masked S-boxes) and the adjoints `(maskLin L)⁻¹`.
  `walsh_run_eq_sum_linCorr`: the fixed-key expansion of `Trail.lean` for these rounds, for every
  key vector; `walsh_execute_eq_sum_linCorr`: with the zero key, the Walsh value of the permutation
  `Hades.execute` with its fixed constants is the sum of the trail correlations `linCorr` over the
  trails from `u` to `v` (`run_zero_eq_execute`). `walsh_comp_linearEquiv`,
  `walsh_comp_execute_eq_sum_linCorr`: a linear layer `L₀` before the rounds (the initial external
  layer of Poseidon2) moves the input mask to `maskLin L₀ u`.
* `isTrail_of_trailCorr_ne_zero`, `isTrail_of_linCorr_ne_zero`: **the bridge.** For a separating
  pairing into a domain, a trail with a nonzero correlation is a `Hades.IsTrail` of
  `maskSchedule rounds`. The charged weight of the mask schedule is that of the rounds
  (`scheduledWeight_maskSchedule`). `isTrail_maskSchedule_iff_backward`: a `Hades.IsTrail` of the
  mask schedule is the same as a sequence of masks in which, at every round, the backward image
  `(maskLin L)⁻¹ (T (n + 1))` has the support of `T n` and agrees with `T n` off the round's mask.
* `inactiveSpace_symm_eq_bot_iff`: no nonzero difference stays inactive through `r` rounds of `L⁻¹`
  exactly when none does through `r` rounds of `L`. `MiddleBound.symm`, `middleBound_symm_iff`: **a
  middle bound for `L` is a middle bound for `L⁻¹`**, for the same number of rounds and the same
  count: a trail through `m` rounds of `L⁻¹` read backwards and shifted by `L` is a trail through
  `m` rounds of `L` with the same charged weight. `MiddleBound.maskLin_of_selfAdjoint`: so a middle
  bound for a self-adjoint `L` is one for `maskLin L = L⁻¹`.
* `hades_linear_outer_activity`, `hades_linear_activity`: for a HADES schedule
  (`Hades.hadesSchedule r m s`), every linear trail with a nonzero input mask and a nonzero
  correlation charges at least `(r / 2 + s / 2) · B + r % 2 + s % 2` S-boxes, and `μ` more under a
  middle bound `μ` for the forward mask map of the partial rounds, when the forward mask maps of the
  full rounds have branch number at least `B`.
* Bounds, for any absolute value `abv : AbsoluteValue R S` into a linearly ordered commutative ring
  with `abv (ψ t) = 1` for every `t` (for `ℂ`, the norm, in `Field.lean`), and S-boxes with
  `abv (walsh) ≤ c` at every nonzero input mask (the S-box correlation bound, a hypothesis):
  `abv_walsh_le_card`, `abv_walsh_roundGamma_le`, `abv_linCorr_le`,
  `abv_linCorr_mul_card_pow_le_of_le`: `abv (linCorr) ≤ c ^ W · |K| ^ (r · |Idx| - W)` with `W` the
  charged weight, and, for `c ≥ 0`, `abv (linCorr) · |K| ^ A ≤ c ^ A · |Idx → K| ^ r` for every
  `A ≤ W`, with no relation between `c` and `|K|` assumed. `hades_linear_bound`: the latter with `A`
  the activity of `hades_linear_activity`, for every trail with a nonzero input mask.

## What is not claimed

* A trail bound bounds one trail: one summand of the expansion `walsh_run_eq_sum_linCorr`, whose
  absolute value (for an absolute value that is `1` on the character) is the same for every key
  and every table of round constants. It is not a bound on the
  correlation of the permutation with its fixed constants, which is a sum over all trails whose
  summands can reinforce or cancel, nor on any key-averaged quantity.
* No S-box is shown to satisfy a correlation bound here: the bound `c` is a hypothesis. Over a
  prime field the Weil bound `(d - 1) √p` for `x ↦ x ^ d` is not proved anywhere in this library.
* Activity counts are lower bounds on charged S-boxes in the `IsTrail` model; they are not claimed
  to be attained. Nothing is said about linear hulls over `K`, about subspace trails beyond the
  inactive spaces, or about algebraic attacks.
* This file imports no `Mathlib.Analysis` module: the character, the ring `R` and the absolute
  value are arbitrary, subject to the stated hypotheses. `Field.lean` instantiates them with
  `ZMod.stdAddChar` and the norm of `ℂ`.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Hades

open Linear
open scoped Matrix

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K]

/-! ### The transpose and the forward mask map -/

section Transpose

/-- Two vectors with the same dot product against every vector are equal. -/
theorem eq_of_forall_dotProduct {v w : Idx → K} (h : ∀ x, v ⬝ᵥ x = w ⬝ᵥ x) : v = w := by
  funext i
  have hi := h (Pi.single i 1)
  simpa only [dotProduct_single, mul_one] using hi

/-- **The transpose of a linear map** of `Idx → K` for the dot product: the map of the
transposed matrix, so that `transposeLin A w ⬝ᵥ x = w ⬝ᵥ A x` (`transposeLin_dotProduct`). -/
def transposeLin (A : (Idx → K) →ₗ[K] (Idx → K)) : (Idx → K) →ₗ[K] (Idx → K) :=
  Matrix.toLin' (LinearMap.toMatrix' A)ᵀ

theorem transposeLin_dotProduct (A : (Idx → K) →ₗ[K] (Idx → K)) (w x : Idx → K) :
    transposeLin A w ⬝ᵥ x = w ⬝ᵥ A x := by
  rw [transposeLin, Matrix.toLin'_apply, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    LinearMap.toMatrix'_mulVec]

/-- **The forward mask map** of a linear equivalence `L`: the inverse of its transpose,
`(Lᵀ)⁻¹ = (L⁻¹)ᵀ`. Masks move forward through it, contragrediently to states
(`maskLin_dotProduct`). -/
def maskLin (L : (Idx → K) ≃ₗ[K] (Idx → K)) : (Idx → K) ≃ₗ[K] (Idx → K) :=
  { transposeLin L.symm.toLinearMap with
    invFun := transposeLin L.toLinearMap
    left_inv := fun w => eq_of_forall_dotProduct fun x => by
      change transposeLin L.toLinearMap (transposeLin L.symm.toLinearMap w) ⬝ᵥ x = w ⬝ᵥ x
      rw [transposeLin_dotProduct, transposeLin_dotProduct]
      simp
    right_inv := fun w => eq_of_forall_dotProduct fun x => by
      change transposeLin L.symm.toLinearMap (transposeLin L.toLinearMap w) ⬝ᵥ x = w ⬝ᵥ x
      rw [transposeLin_dotProduct, transposeLin_dotProduct]
      simp }

theorem maskLin_apply (L : (Idx → K) ≃ₗ[K] (Idx → K)) (w : Idx → K) :
    maskLin L w = transposeLin L.symm.toLinearMap w :=
  rfl

theorem maskLin_symm_apply (L : (Idx → K) ≃ₗ[K] (Idx → K)) (w : Idx → K) :
    (maskLin L).symm w = transposeLin L.toLinearMap w :=
  rfl

/-- **Masks move contragrediently to states**: `maskLin L w ⬝ᵥ L x = w ⬝ᵥ x`. -/
theorem maskLin_dotProduct (L : (Idx → K) ≃ₗ[K] (Idx → K)) (w x : Idx → K) :
    maskLin L w ⬝ᵥ L x = w ⬝ᵥ x := by
  rw [maskLin_apply, transposeLin_dotProduct]
  simp

/-- The inverse of the forward mask map is the transpose: `(maskLin L)⁻¹ w ⬝ᵥ x = w ⬝ᵥ L x`. -/
theorem maskLin_symm_dotProduct (L : (Idx → K) ≃ₗ[K] (Idx → K)) (w x : Idx → K) :
    (maskLin L).symm w ⬝ᵥ x = w ⬝ᵥ L x := by
  rw [maskLin_symm_apply, transposeLin_dotProduct]
  rfl

/-- **A known transpose.** If `L x ⬝ᵥ y = x ⬝ᵥ T y` for all `x, y`, then `(maskLin L)⁻¹ = T`. -/
theorem maskLin_symm_eq_of_dotProduct (L : (Idx → K) ≃ₗ[K] (Idx → K))
    {T : (Idx → K) → (Idx → K)} (h : ∀ x y, L x ⬝ᵥ y = x ⬝ᵥ T y) (w : Idx → K) :
    (maskLin L).symm w = T w :=
  eq_of_forall_dotProduct fun x => by
    rw [maskLin_symm_dotProduct, dotProduct_comm, h, dotProduct_comm]

/-- **A self-adjoint layer moves masks by its inverse.** If `L x ⬝ᵥ y = x ⬝ᵥ L y` for all
`x, y` (a symmetric matrix), then `maskLin L = L⁻¹`. -/
theorem maskLin_eq_symm_of_selfAdjoint (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (h : ∀ x y, L x ⬝ᵥ y = x ⬝ᵥ L y) : maskLin L = L.symm := by
  ext w : 1
  apply (maskLin L).symm.injective
  rw [LinearEquiv.symm_apply_apply, maskLin_symm_eq_of_dotProduct L h, LinearEquiv.apply_symm_apply]

omit [DecidableEq Idx] in
/-- **A matrix layer.** If `L x = M *ᵥ x` for every `x`, then `L x ⬝ᵥ y = x ⬝ᵥ (Mᵀ *ᵥ y)`, so
`(maskLin L)⁻¹` is `Mᵀ *ᵥ ·` (`maskLin_symm_eq_of_dotProduct`). -/
theorem dotProduct_of_mulVec {M : Matrix Idx Idx K} {L : (Idx → K) → (Idx → K)}
    (hL : ∀ x, L x = M *ᵥ x) (x y : Idx → K) : L x ⬝ᵥ y = x ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [hL, Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

omit [DecidableEq Idx] in
/-- **A symmetric matrix layer is self-adjoint**: if `L x = M *ᵥ x` and `Mᵀ = M`, then
`L x ⬝ᵥ y = x ⬝ᵥ L y`. -/
theorem selfAdjoint_of_mulVec {M : Matrix Idx Idx K} {L : (Idx → K) → (Idx → K)}
    (hL : ∀ x, L x = M *ᵥ x) (hM : Mᵀ = M) (x y : Idx → K) : L x ⬝ᵥ y = x ⬝ᵥ L y := by
  rw [dotProduct_of_mulVec hL, hM, hL]

end Transpose

/-! ### Adjoints for the pairing `ℓ (u ⬝ᵥ x)` -/

section Adjoint

variable {G : Type*} [AddCommGroup G]

omit [DecidableEq Idx] in
/-- The bundle-sum pairing of a trace form is the dot product read through `ℓ`. -/
theorem traceForm_pi_dot (ℓ : K →+ G) (u x : Idx → K) :
    (Pairing.traceForm ℓ).pi.dot u x = ℓ (u ⬝ᵥ x) := by
  rw [Pairing.pi_dot, dotProduct, map_sum]
  rfl

omit [DecidableEq Idx] in
/-- **An adjoint for the dot product is an adjoint for every pairing `ℓ (u ⬝ᵥ x)`.** -/
theorem isAdjoint_of_dotProduct (ℓ : K →+ G) {L Lt : (Idx → K) → (Idx → K)}
    (h : ∀ v y, v ⬝ᵥ L y = Lt v ⬝ᵥ y) :
    IsAdjoint (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi L Lt := fun v y => by
  rw [traceForm_pi_dot, traceForm_pi_dot, h]

/-- **`(maskLin L)⁻¹ = Lᵀ` is an adjoint of `L`**, for every pairing `ℓ (u ⬝ᵥ x)`. -/
theorem isAdjoint_maskLin (ℓ : K →+ G) (L : (Idx → K) ≃ₗ[K] (Idx → K)) :
    IsAdjoint (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi L (maskLin L).symm :=
  isAdjoint_of_dotProduct ℓ fun v y => (maskLin_symm_dotProduct L v y).symm

end Adjoint

/-! ### Branch numbers of the forward mask map -/

section Branch

variable [DecidableEq K]

/-- **The branch-number lower bounds of the forward mask map are those of the transpose.** If
`L x ⬝ᵥ y = x ⬝ᵥ T y` for all `x, y`, then `isBranchBound id (maskLin L) B` holds exactly when
`isBranchBound id T B` does: `maskLin L` is the inverse of `T` (`maskLin_symm_eq_of_dotProduct`),
and a bijection and its inverse have the same branch-number lower bounds
(`Linear.isBranchBound_symm_iff`). -/
theorem isBranchBound_maskLin_iff (L : (Idx → K) ≃ₗ[K] (Idx → K))
    {T : (Idx → K) → (Idx → K)} (h : ∀ x y, L x ⬝ᵥ y = x ⬝ᵥ T y) (B : ℕ) :
    isBranchBound id (maskLin L) B ↔ isBranchBound id T B := by
  have hT : ((maskLin L).symm : (Idx → K) → (Idx → K)) = T :=
    funext (maskLin_symm_eq_of_dotProduct L h)
  rw [← hT]
  exact (isBranchBound_symm_iff (maskLin L).toAddEquiv B).symm

/-- **For a self-adjoint layer**, the forward mask map has the branch-number lower bounds of the
layer itself. -/
theorem isBranchBound_maskLin_iff_of_selfAdjoint (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (h : ∀ x y, L x ⬝ᵥ y = x ⬝ᵥ L y) (B : ℕ) :
    isBranchBound id (maskLin L) B ↔ isBranchBound id L B :=
  isBranchBound_maskLin_iff L h B

/-- **The forward mask map of an MDS layer.** If `L x = M *ᵥ x` for an MDS matrix `M` of size
`t`, the forward mask map `maskLin L` has branch number at least `t + 1`: the transpose `Mᵀ` is
MDS (`isMDS_transpose_iff`), so `Mᵀ *ᵥ ·` has branch number at least `t + 1`
(`isMDS_branch_bound`), and `maskLin L` is its inverse. -/
theorem isBranchBound_maskLin_of_isMDS {t : ℕ} {M : Matrix (Fin t) (Fin t) K} (hM : IsMDS M)
    (L : (Fin t → K) ≃ₗ[K] (Fin t → K)) (hL : ∀ x, L x = M *ᵥ x) :
    isBranchBound id (maskLin L) (t + 1) := by
  refine (isBranchBound_maskLin_iff L (dotProduct_of_mulVec hL) (t + 1)).mpr ?_
  intro a ha
  rw [colWeight_id, colWeight_id]
  exact isMDS_branch_bound (isMDS_transpose_iff.mpr hM) a (by have := one_le_weight ha; omega)

variable [Fintype K] {G R : Type*} [AddCommGroup G] [CommRing R] [IsDomain R]

/-- **The linear branch number of a layer is the branch number of its forward mask map.** For a
pairing `ℓ (u ⬝ᵥ x)` separating for `ψ`, into a domain in which `|Idx → K|` is nonzero, `B` is a
linear branch-number lower bound for `L` (`Linear.IsLinBranchBound`, through correlations)
exactly when it is a branch-number lower bound for `maskLin L`. -/
theorem isLinBranchBound_iff_maskLin {ψ : AddChar G R} {ℓ : K →+ G}
    (hP : (Pairing.traceForm ℓ).Separating ψ) (hcard : (Fintype.card (Idx → K) : R) ≠ 0)
    (L : (Idx → K) ≃ₗ[K] (Idx → K)) (B : ℕ) :
    IsLinBranchBound ψ (Pairing.traceForm ℓ) L B ↔ isBranchBound id (maskLin L) B :=
  (isLinBranchBound_iff hP hcard (isAdjoint_maskLin ℓ L) B).trans
    (isBranchBound_symm_iff (maskLin L).toAddEquiv B)

end Branch

/-! ### The mask schedule -/

section Schedule

/-- **The rounds that carry masks**: the same masks, S-boxes and constants, with each linear
layer `L` replaced by its forward mask map `maskLin L`. -/
def maskSchedule (rounds : ℕ → RoundSpec Idx K) : ℕ → RoundSpec Idx K :=
  fun n => { rounds n with lin := maskLin (rounds n).lin }

@[simp] theorem maskSchedule_mask (rounds : ℕ → RoundSpec Idx K) (n : ℕ) :
    (maskSchedule rounds n).mask = (rounds n).mask :=
  rfl

@[simp] theorem maskSchedule_lin (rounds : ℕ → RoundSpec Idx K) (n : ℕ) :
    (maskSchedule rounds n).lin = maskLin (rounds n).lin :=
  rfl

/-- The mask schedule of a HADES schedule is the HADES schedule of the forward mask maps. -/
theorem maskSchedule_hadesSchedule (r m s : ℕ) (mask : Finset Idx) (boxes : ℕ → Idx → K ≃ K)
    (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K)) (values : ℕ → Idx → K) :
    maskSchedule (hadesSchedule r m s mask boxes linear values) =
      hadesSchedule r m s mask boxes (fun n => maskLin (linear n)) values :=
  rfl

/-- The charged weight depends only on the masks, so the mask schedule charges what the rounds
charge. -/
theorem scheduledWeight_maskSchedule [DecidableEq K] (rounds : ℕ → RoundSpec Idx K)
    (T : ℕ → Idx → K) (s l : ℕ) :
    scheduledWeight (maskSchedule rounds) T s l = scheduledWeight rounds T s l :=
  rfl

/-- **The backward reading of a mask trail.** `T` is a `Hades.IsTrail` of the mask schedule
through `r` rounds exactly when, for every `n < r`, the backward image
`(maskLin L)⁻¹ (T (n + 1)) = Lᵀ (T (n + 1))` (`maskLin_symm_apply`) of the next mask under the
round's layer `L` has the support of `T n` and agrees with `T n` off the round's mask: the
intermediate mask of `IsTrail` is forced to be this backward image. -/
theorem isTrail_maskSchedule_iff_backward [DecidableEq K] (rounds : ℕ → RoundSpec Idx K)
    (T : ℕ → Idx → K) (r : ℕ) :
    IsTrail (maskSchedule rounds) T r ↔ ∀ n < r,
      activePattern ((maskLin (rounds n).lin).symm (T (n + 1))) = activePattern (T n) ∧
        ∀ i ∉ (rounds n).mask, (maskLin (rounds n).lin).symm (T (n + 1)) i = T n i := by
  constructor
  · intro h n hn
    obtain ⟨b, hb, hl, hout⟩ := h n hn
    have hb' : (maskLin (rounds n).lin).symm (T (n + 1)) = b := by
      rw [← hl]
      exact LinearEquiv.symm_apply_apply _ b
    rw [hb']
    exact ⟨hb, hout⟩
  · intro h n hn
    obtain ⟨hp, hout⟩ := h n hn
    exact ⟨_, hp, LinearEquiv.apply_symm_apply _ _, hout⟩

end Schedule

/-! ### Walsh values of masked S-box layers and of rounds -/

section Walsh

variable [Fintype K] [DecidableEq K] {G R : Type*} [AddCommGroup G] [CommRing R]

omit [DecidableEq K] in
/-- **The round constant contributes a phase**: `roundGamma R` is the masked S-box layer after
the constant `R.constant`, so its Walsh value is `ψ ⟨u, R.constant⟩` times that of the layer. -/
theorem walsh_roundGamma (ψ : AddChar G R) (P : Pairing K G) (R' : RoundSpec Idx K)
    (u v : Idx → K) :
    walsh ψ P.pi P.pi (roundGamma R') u v =
      ψ (P.pi.dot u R'.constant) *
        walsh ψ P.pi P.pi (maskedBricklayer R'.mask (fun i => R'.sbox i)) u v :=
  walsh_addKey ψ P.pi P.pi (maskedBricklayer R'.mask (fun i => R'.sbox i)) R'.constant u v

variable [IsDomain R] {ψ : AddChar G R}

/-- **The Walsh value of a masked S-box layer.** For a pairing `P` of `K` separating for `ψ`,
into a domain, the Walsh value of `maskedBricklayer mask s` at `(a, b)` is the product over the
coordinates of the S-box's Walsh value on the mask and of `|K| · [aᵢ = bᵢ]` off it: an identity
coordinate passes its mask unchanged. -/
theorem walsh_masked {P : Pairing K G} (hP : P.Separating ψ) (mask : Finset Idx)
    (s : Idx → K → K) (a b : Idx → K) :
    walsh ψ P.pi P.pi (maskedBricklayer mask s) a b =
      ∏ i, if i ∈ mask then walsh ψ P P (s i) (a i) (b i)
        else if a i = b i then (Fintype.card K : R) else 0 := by
  rw [maskedBricklayer, walsh_bricklayer]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ mask
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    exact walsh_of_adjoint (L := id) (Lt := id) hP (fun _ _ => rfl) (a i) (b i)

/-- **The bridge, for any separating pairing of `K`.** If the bundle pairing `P` is separating
for `ψ` into a domain, a trail whose correlation through the rounds `roundGamma (rounds n)` with
the maps `(maskLin (rounds n).lin)⁻¹` is nonzero is a `Hades.IsTrail` of the mask schedule: at
round `n`, the mask `b = (maskLin L)⁻¹ (T (n + 1))` at the output of the S-box layer has the
support of `T n` (`activePattern_eq_of_walsh_ne_zero`), agrees with `T n` off the mask
(`walsh_masked`), and `maskLin L b = T (n + 1)`. -/
theorem isTrail_of_trailCorr_ne_zero {P : Pairing K G} (hP : P.Separating ψ)
    (rounds : ℕ → RoundSpec Idx K) {r : ℕ} {T : ℕ → Idx → K}
    (h : trailCorr ψ P.pi (fun n => (maskLin (rounds n).lin).symm)
      (fun n => roundGamma (rounds n)) r T ≠ 0) :
    IsTrail (maskSchedule rounds) T r := by
  intro n hn
  set b := (maskLin (rounds n).lin).symm (T (n + 1)) with hbdef
  have hn' : walsh ψ P.pi P.pi (roundGamma (rounds n)) (T n) b ≠ 0 :=
    fun hz => h (Finset.prod_eq_zero (Finset.mem_range.mpr hn) hz)
  have hm : walsh ψ P.pi P.pi
      (bricklayer (fun i => if i ∈ (rounds n).mask then ((rounds n).sbox i : K → K) else id))
      (T n) b ≠ 0 := by
    intro hz
    apply hn'
    rw [walsh_roundGamma]
    change _ * walsh ψ P.pi P.pi (bricklayer _) (T n) b = 0
    rw [hz, mul_zero]
  have hbij : ∀ i, Function.Bijective
      (if i ∈ (rounds n).mask then ((rounds n).sbox i : K → K) else id) := fun i => by
    by_cases hi : i ∈ (rounds n).mask
    · rw [if_pos hi]
      exact ((rounds n).sbox i).bijective
    · rw [if_neg hi]
      exact Function.bijective_id
  refine ⟨b, activePattern_eq_of_walsh_ne_zero hP hbij hm, ?_, fun i hi => ?_⟩
  · change maskLin (rounds n).lin b = T (n + 1)
    rw [hbdef, LinearEquiv.apply_symm_apply]
  · change i ∉ (rounds n).mask at hi
    rw [walsh_bricklayer] at hm
    have hfac := fun hz => hm (Finset.prod_eq_zero (Finset.mem_univ i) hz)
    rw [if_neg hi, walsh_of_adjoint (L := id) (Lt := id) hP (fun _ _ => rfl)] at hfac
    by_contra hne
    exact hfac (if_neg (Ne.symm hne))

end Walsh

/-! ### Linear trails of HADES rounds -/

section Trails

variable [Fintype K] {G R : Type*} [AddCommGroup G] [CommRing R]

/-- **The correlation of a linear trail through HADES rounds**, unnormalised (divide by
`|Idx → K| ^ r`): `Linear.trailCorr` for the pairing `ℓ (u ⬝ᵥ x)`, the round maps
`roundGamma (rounds n)` (round constant, then the masked S-box layer) and the adjoints
`(maskLin (rounds n).lin)⁻¹` of the linear layers. It involves no key; the round constants
contribute phases (`walsh_roundGamma`). -/
def linCorr (ψ : AddChar G R) (ℓ : K →+ G) (rounds : ℕ → RoundSpec Idx K) (r : ℕ)
    (T : ℕ → Idx → K) : R :=
  trailCorr ψ (Pairing.traceForm ℓ).pi (fun n => (maskLin (rounds n).lin).symm)
    (fun n => roundGamma (rounds n)) r T

variable [IsDomain R] {ψ : AddChar G R} {ℓ : K →+ G}

/-- **The bridge.** For a pairing `ℓ (u ⬝ᵥ x)` separating for `ψ`, into a domain, a linear trail
of the HADES rounds with a nonzero correlation is a `Hades.IsTrail` of the mask schedule, so
every activity bound of `WideTrail.Hades` applies to it. This is the linear twin of
`Hades.isTrail_of_keyCount_ne_zero`. -/
theorem isTrail_of_linCorr_ne_zero [DecidableEq K] (hP : (Pairing.traceForm ℓ).Separating ψ)
    (rounds : ℕ → RoundSpec Idx K) {r : ℕ} {T : ℕ → Idx → K} (h : linCorr ψ ℓ rounds r T ≠ 0) :
    IsTrail (maskSchedule rounds) T r :=
  isTrail_of_trailCorr_ne_zero hP rounds h

/-- **The fixed-key expansion for HADES rounds.** With an additional key `k n` added before round
`n` (`Scheduled.run` with the linear layers of `rounds` and the maps `roundGamma`), for every key
vector `k`,
`|Idx → K| ^ r · walsh (r + 1 rounds) u v = ∑_d trailPhase k T_d · linCorr T_d`
over the trails `T_d = Scheduled.throughTrail u d v` from `u` to `v`. -/
theorem walsh_run_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (rounds : ℕ → RoundSpec Idx K) (r : ℕ) (k : Fin (r + 1) → Idx → K) (u v : Idx → K) :
    (Fintype.card (Idx → K) : R) ^ r * walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi
        (Scheduled.run (fun n => (rounds n).lin.toAddEquiv) (fun n => roundGamma (rounds n))
          (r + 1) k) u v
      = ∑ d : Fin r → Idx → K, trailPhase ψ (Pairing.traceForm ℓ).pi (r + 1) k
          (Scheduled.throughTrail u d v) * linCorr ψ ℓ rounds (r + 1)
            (Scheduled.throughTrail u d v) :=
  walsh_run_eq_sum_trails hP.pi (fun n => (rounds n).lin.toAddEquiv)
    (fun n => (maskLin (rounds n).lin).symm) (fun n => isAdjoint_maskLin ℓ (rounds n).lin)
    (fun n => roundGamma (rounds n)) r k u v

omit [Fintype Idx] [Fintype K] in
/-- `n + 1` rounds of `Hades.execute` are the first round, then `n` rounds of the rest. -/
theorem execute_succ' (rounds : ℕ → RoundSpec Idx K) (x : Idx → K) (n : ℕ) :
    execute rounds x (n + 1) = execute (fun j => rounds (j + 1)) ((rounds 0).apply x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [execute_succ, ih, execute_succ]

omit [Fintype Idx] [Fintype K] in
/-- **With the zero key, the keyed rounds are the permutation with its fixed constants.** -/
theorem run_zero_eq_execute (rounds : ℕ → RoundSpec Idx K) (r : ℕ) (x : Idx → K) :
    Scheduled.run (fun n => (rounds n).lin.toAddEquiv) (fun n => roundGamma (rounds n)) r 0 x =
      execute rounds x r := by
  induction r generalizing rounds x with
  | zero => rfl
  | succ r ih =>
    rw [execute_succ', ← ih (fun j => rounds (j + 1))]
    change Scheduled.run _ _ r (Fin.tail (0 : Fin (r + 1) → Idx → K)) _ = _
    have h0 : (Fin.tail (0 : Fin (r + 1) → Idx → K)) = 0 := rfl
    rw [h0]
    congr 1
    simp [RoundSpec.apply, roundGamma]

/-- **The permutation with its fixed constants.** The Walsh value of `r + 1` rounds of
`Hades.execute`, with the round constants of `rounds` and no key, satisfies
`|Idx → K| ^ r · walsh u v = ∑_d linCorr T_d` over the trails `T_d = throughTrail u d v` from `u`
to `v`. Each summand is one trail's correlation; the summands can reinforce or cancel. -/
theorem walsh_execute_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (rounds : ℕ → RoundSpec Idx K) (r : ℕ) (u v : Idx → K) :
    (Fintype.card (Idx → K) : R) ^ r * walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi
        (fun x => execute rounds x (r + 1)) u v
      = ∑ d : Fin r → Idx → K, linCorr ψ ℓ rounds (r + 1) (Scheduled.throughTrail u d v) := by
  have h := walsh_run_eq_sum_linCorr hP rounds r 0 u v
  simp only [funext fun x => run_zero_eq_execute rounds (r + 1) x] at h
  rw [h]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [trailPhase]

omit [IsDomain R] in
/-- **A linear layer before the rounds moves the input mask forward**: the Walsh value of
`x ↦ F (L x)` at `(u, v)` is that of `F` at `(maskLin L u, v)`, since
`⟨u, x⟩ = ⟨maskLin L u, L x⟩` (`maskLin_dotProduct`). -/
theorem walsh_comp_linearEquiv (ψ : AddChar G R) (ℓ : K →+ G) (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (F : (Idx → K) → (Idx → K)) (u v : Idx → K) :
    walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi (fun x => F (L x)) u v =
      walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi F (maskLin L u) v := by
  unfold walsh
  refine Fintype.sum_equiv L.toEquiv _ _ (fun x => ?_)
  simp only [LinearEquiv.coe_toEquiv, traceForm_pi_dot, maskLin_dotProduct]

/-- **A permutation that applies a linear layer `L₀` and then the rounds**, as Poseidon2 does with
its initial external layer: `|Idx → K| ^ r · walsh u v = ∑_d linCorr T_d` over the trails
`T_d = throughTrail (maskLin L₀ u) d v` of the rounds, from the input mask `maskLin L₀ u` to `v`,
with the fixed constants of `rounds` and no key. -/
theorem walsh_comp_execute_eq_sum_linCorr (hP : (Pairing.traceForm ℓ).Separating ψ)
    (L₀ : (Idx → K) ≃ₗ[K] (Idx → K)) (rounds : ℕ → RoundSpec Idx K) (r : ℕ) (u v : Idx → K) :
    (Fintype.card (Idx → K) : R) ^ r * walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi
        (fun x => execute rounds (L₀ x) (r + 1)) u v
      = ∑ d : Fin r → Idx → K,
          linCorr ψ ℓ rounds (r + 1) (Scheduled.throughTrail (maskLin L₀ u) d v) := by
  rw [walsh_comp_linearEquiv ψ ℓ L₀ (fun y => execute rounds y (r + 1))]
  exact walsh_execute_eq_sum_linCorr hP rounds r (maskLin L₀ u) v

end Trails

/-! ### Inactive spaces and middle bounds of the inverse -/

section Inverse

variable [DecidableEq K]

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- `(L⁻¹) ^ j` undoes `L ^ j`. -/
theorem symm_pow_pow_apply (L : (Idx → K) ≃ₗ[K] (Idx → K)) (j : ℕ) (y : Idx → K) :
    ((L.symm.toLinearMap : Module.End K (Idx → K)) ^ j)
      (((L.toLinearMap : Module.End K (Idx → K)) ^ j) y) = y := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    simp [ih]

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- One direction of `inactiveSpace_symm_eq_bot_iff`: a nonzero `a` surviving `r` rounds of `L`
gives the nonzero `L ^ (r - 1) a` surviving `r` rounds of `L⁻¹`. -/
theorem inactiveSpace_eq_bot_of_symm (L : (Idx → K) ≃ₗ[K] (Idx → K)) (mask : Finset Idx)
    (r : ℕ) (h : inactiveSpace L.symm.toLinearMap mask r = ⊥) :
    inactiveSpace L.toLinearMap mask r = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  have hmem : ((L.toLinearMap : Module.End K (Idx → K)) ^ (r - 1)) a ∈
      inactiveSpace L.symm.toLinearMap mask r := by
    intro j hj i hi
    have hsplit : r - 1 = j + (r - 1 - j) := by omega
    rw [hsplit, pow_add, Module.End.mul_apply, symm_pow_pow_apply]
    exact ha (r - 1 - j) (by omega) i hi
  rw [h, Submodule.mem_bot] at hmem
  have := symm_pow_pow_apply L (r - 1) a
  rw [hmem, map_zero] at this
  exact this.symm

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- **Inactive spaces of `L` and `L⁻¹` vanish together.** No nonzero difference stays inactive
through `r` consecutive rounds of `L⁻¹` with mask `mask` exactly when none does through `r`
rounds of `L`: `a` survives `r` rounds of `L⁻¹` exactly when `L⁻¹ ^ (r - 1) a` survives `r` rounds
of `L`. -/
theorem inactiveSpace_symm_eq_bot_iff (L : (Idx → K) ≃ₗ[K] (Idx → K)) (mask : Finset Idx)
    (r : ℕ) : inactiveSpace L.symm.toLinearMap mask r = ⊥ ↔
      inactiveSpace L.toLinearMap mask r = ⊥ :=
  ⟨inactiveSpace_eq_bot_of_symm L mask r, fun h =>
    inactiveSpace_eq_bot_of_symm L.symm mask r (by rwa [LinearEquiv.symm_symm])⟩

/-- **A middle bound for `L` is a middle bound for `L⁻¹`.** If every trail through `m`
consecutive rounds with linear map `L` and mask `mask`, from a nonzero difference, charges at
least `μ` S-boxes, then so does every such trail with linear map `L⁻¹`. A trail `T` through `m`
rounds of `L⁻¹` gives the trail `j ↦ L (T (m - j))` through `m` rounds of `L`: the round `n`
relation `L⁻¹ b = T (n + 1)` with `b` of the support of `T n` reads backwards as `T n ↦ L (T n)`
with `L (T (n + 1)) = b`. Its charged weight is that of `T`, round by round in reverse order. -/
theorem MiddleBound.symm {L : (Idx → K) ≃ₗ[K] (Idx → K)} {mask : Finset Idx} {m μ : ℕ}
    (h : MiddleBound L.toLinearMap mask m μ) : MiddleBound L.symm.toLinearMap mask m μ := by
  intro rounds T hT h0 hlin hmask
  have hlin' : ∀ n < m, ∀ b, (rounds n).lin b = L.symm b := fun n hn b =>
    LinearMap.congr_fun (hlin n hn) b
  let rounds' : ℕ → RoundSpec Idx K := fun _ => ⟨mask, fun _ => Equiv.refl K, L, 0⟩
  let U : ℕ → Idx → K := fun j => L (T (m - j))
  have hstep : ∀ n < m, activePattern (L (T (n + 1))) = activePattern (T n) ∧
      ∀ i ∉ mask, L (T (n + 1)) i = T n i := by
    intro n hn
    obtain ⟨b, hb, hl, hout⟩ := hT n hn
    have hbL : b = L (T (n + 1)) := by
      rw [← hl, hlin' n hn, LinearEquiv.apply_symm_apply]
    rw [← hbL]
    exact ⟨hb, fun i hi => hout i (by rw [hmask n hn]; exact hi)⟩
  have hU : IsTrail rounds' U m := by
    intro j hj
    obtain ⟨hsupp, hout⟩ := hstep (m - 1 - j) (by omega)
    have hj1 : m - 1 - j + 1 = m - j := by omega
    rw [hj1] at hsupp hout
    refine ⟨T (m - 1 - j), hsupp.symm, ?_, fun i hi => (hout i hi).symm⟩
    change L (T (m - 1 - j)) = L (T (m - (j + 1)))
    rw [show m - (j + 1) = m - 1 - j by omega]
  have hU0 : U 0 ≠ 0 := by
    change L (T (m - 0)) ≠ 0
    rw [Nat.sub_zero, map_ne_zero_iff _ L.injective]
    exact hT.ne_zero h0 m le_rfl
  have hμ := h rounds' U hU hU0 (fun _ _ => rfl) (fun _ _ => rfl)
  have hw : scheduledWeight rounds' U 0 m = scheduledWeight rounds T 0 m := by
    unfold scheduledWeight
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n < m := Finset.mem_range.mp hn
    obtain ⟨hsupp, _⟩ := hstep n hn'
    simp only [Nat.zero_add, hmask n hn']
    change sboxWeight mask (L (T (m - (m - 1 - n)))) = sboxWeight mask (T n)
    rw [show m - (m - 1 - n) = n + 1 by omega]
    simp only [sboxWeight, activeSboxes, hsupp]
  omega

/-- A middle bound holds for `L⁻¹` exactly when it holds for `L`. -/
theorem middleBound_symm_iff {L : (Idx → K) ≃ₗ[K] (Idx → K)} {mask : Finset Idx} {m μ : ℕ} :
    MiddleBound L.symm.toLinearMap mask m μ ↔ MiddleBound L.toLinearMap mask m μ :=
  ⟨fun h => by simpa using h.symm, MiddleBound.symm⟩

/-- **The forward mask map of a self-adjoint layer.** A middle bound for a self-adjoint `L` is a
middle bound for `maskLin L = L⁻¹`. -/
theorem MiddleBound.maskLin_of_selfAdjoint {L : (Idx → K) ≃ₗ[K] (Idx → K)}
    (hL : ∀ x y, L x ⬝ᵥ y = x ⬝ᵥ L y) {mask : Finset Idx} {m μ : ℕ}
    (h : MiddleBound L.toLinearMap mask m μ) :
    MiddleBound (maskLin L).toLinearMap mask m μ := by
  rw [maskLin_eq_symm_of_selfAdjoint L hL]
  exact h.symm

end Inverse

/-! ### Linear activity of HADES schedules -/

section Activity

variable [DecidableEq K] [Fintype K] {G R : Type*} [AddCommGroup G] [CommRing R] [IsDomain R]
  {ψ : AddChar G R} {ℓ : K →+ G}

/-- **Linear activity of the full rounds.** For a pairing `ℓ (u ⬝ᵥ x)` separating for `ψ`, into
a domain, if the forward mask maps of the full rounds of `hadesSchedule r m s` have branch number
at least `B`, every linear trail through the `r + m + s` rounds with a nonzero input mask and a
nonzero correlation charges at least `(r / 2 + s / 2) · B + r % 2 + s % 2` S-boxes. A lower
bound in the `IsTrail` model. -/
theorem hades_linear_outer_activity (hP : (Pairing.traceForm ℓ).Separating ψ)
    (r m s B : ℕ) (mask : Finset Idx) (boxes : ℕ → Idx → K ≃ K)
    (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K)) (values : ℕ → Idx → K)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (maskLin (linear j)) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (maskLin (linear (r + m + j))) B)
    {T : ℕ → Idx → K} (h0 : T 0 ≠ 0)
    (h : linCorr ψ ℓ (hadesSchedule r m s mask boxes linear values) (r + m + s) T ≠ 0) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 ≤
      scheduledWeight (hadesSchedule r m s mask boxes linear values) T 0 (r + m + s) :=
  (isTrail_of_linCorr_ne_zero hP _ h).outer_bound r m s B h0
    (fun _ hj => hadesMask_prefix r m s mask hj) (fun _ hj => hadesMask_suffix r m s mask hj)
    hbp hbs

/-- **Linear activity with a middle bound.** As `hades_linear_outer_activity`, and if the forward
mask maps of the `m` partial rounds are a common `A` with a middle bound `μ`
(`Hades.MiddleBound A mask m μ`), every such trail charges at least
`(r / 2 + s / 2) · B + r % 2 + s % 2 + μ` S-boxes. A lower bound in the `IsTrail` model. -/
theorem hades_linear_activity (hP : (Pairing.traceForm ℓ).Separating ψ)
    (r m s B μ : ℕ) (mask : Finset Idx) (boxes : ℕ → Idx → K ≃ K)
    (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K)) (values : ℕ → Idx → K)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (maskLin (linear j)) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (maskLin (linear (r + m + j))) B)
    (A : Module.End K (Idx → K))
    (hmid : ∀ j < m, ((maskLin (linear (r + j))).toLinearMap : Module.End K (Idx → K)) = A)
    (hμ : MiddleBound A mask m μ) {T : ℕ → Idx → K} (h0 : T 0 ≠ 0)
    (h : linCorr ψ ℓ (hadesSchedule r m s mask boxes linear values) (r + m + s) T ≠ 0) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 + μ ≤
      scheduledWeight (hadesSchedule r m s mask boxes linear values) T 0 (r + m + s) :=
  (isTrail_of_linCorr_ne_zero hP _ h).outer_middle_bound_of r m s B μ h0
    (fun _ hj => hadesMask_prefix r m s mask hj) (fun _ hj => hadesMask_suffix r m s mask hj)
    hbp hbs A mask hmid (fun _ hj => hadesMask_middle r m s mask hj) hμ

end Activity

end Hades

/-! ### Bounds through an absolute value -/

namespace Linear

/-- **A Walsh value is at most `|X|` in absolute value**, for an absolute value that is `1` on the
character's values: each of the `|X|` summands has absolute value `1`. -/
theorem abv_walsh_le_card {X Y G R S : Type*} [AddCommGroup X] [Fintype X] [AddCommGroup Y]
    [AddCommGroup G] [CommRing R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : AbsoluteValue R S) {ψ : AddChar G R} (hψ : ∀ t, abv (ψ t) = 1) (P : Pairing X G)
    (Q : Pairing Y G) (F : X → Y) (u : X) (v : Y) :
    abv (walsh ψ P Q F u v) ≤ Fintype.card X := by
  calc abv (walsh ψ P Q F u v) ≤ ∑ x, abv (ψ (Q.dot v (F x) - P.dot u x)) := abv.sum_le _ _
    _ = Fintype.card X := by simp [hψ]

/-- **Exchanging surplus factors.** If `x ≤ c ^ W · q ^ (N - W)` and `x ≤ q ^ N` with `A ≤ W ≤ N`
and `c, q ≥ 0`, then `x · q ^ A ≤ c ^ A · q ^ N`: when `c ≤ q` the surplus `W - A` factors `c` are
replaced by `q`, and otherwise `q ^ A ≤ c ^ A`. -/
theorem mul_pow_le_of_le {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    {x c q : S} {A W N : ℕ} (hc0 : 0 ≤ c) (hq0 : 0 ≤ q) (hAW : A ≤ W) (hWN : W ≤ N)
    (h1 : x ≤ c ^ W * q ^ (N - W)) (h2 : x ≤ q ^ N) : x * q ^ A ≤ c ^ A * q ^ N := by
  rcases le_total c q with hcq | hqc
  · calc x * q ^ A ≤ c ^ W * q ^ (N - W) * q ^ A :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hq0 A)
      _ = c ^ A * c ^ (W - A) * q ^ (N - W) * q ^ A := by
          rw [← pow_add, Nat.add_sub_cancel' hAW]
      _ ≤ c ^ A * q ^ (W - A) * q ^ (N - W) * q ^ A := by
          gcongr
      _ = c ^ A * q ^ N := by
          rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega
  · calc x * q ^ A ≤ q ^ N * c ^ A :=
          mul_le_mul h2 (pow_le_pow_left₀ hq0 hqc A) (pow_nonneg hq0 A) (pow_nonneg hq0 N)
      _ = c ^ A * q ^ N := mul_comm _ _

end Linear

namespace Hades

open Linear
open scoped Matrix

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K] [Fintype K]
  {G R S : Type*} [AddCommGroup G] [CommRing R] [CommRing S] [LinearOrder S]
  [IsStrictOrderedRing S] {ψ : AddChar G R} {ℓ : K →+ G}

section Bounds

variable [Nontrivial R]

/-- **One round's Walsh value through an absolute value.** For an absolute value that is `1` on
the character's values, if every S-box of the round's mask has `abv (walsh) ≤ c` at every nonzero
input mask, then `abv (walsh (roundGamma R) u v) ≤ c ^ w · |K| ^ (|Idx| - w)`, where
`w = sboxWeight R.mask u` is the number of charged S-boxes. -/
theorem abv_walsh_roundGamma_le (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1) {c : S}
    (R' : RoundSpec Idx K)
    (hc : ∀ i ∈ R'.mask, ∀ a : K, a ≠ 0 → ∀ b : K,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) (R'.sbox i) a b) ≤ c)
    (u v : Idx → K) :
    abv (walsh ψ (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi (roundGamma R') u v) ≤
      c ^ sboxWeight R'.mask u *
        (Fintype.card K : S) ^ (Fintype.card Idx - sboxWeight R'.mask u) := by
  set P := Pairing.traceForm ℓ
  set t := activeSboxes R'.mask u
  have hmem : ∀ i, i ∈ t ↔ i ∈ R'.mask ∧ u i ≠ 0 := fun i => by
    simp [t, activeSboxes, mem_activePattern]
  rw [walsh_roundGamma, abv.map_mul, hψ, one_mul, maskedBricklayer, walsh_bricklayer,
    AbsoluteValue.map_prod]
  have hle : ∀ i, abv (walsh ψ P P (if i ∈ R'.mask then ((R'.sbox i : K → K)) else id)
      (u i) (v i)) ≤ if i ∈ t then c else (Fintype.card K : S) := fun i => by
    by_cases hi : i ∈ t
    · obtain ⟨him, hui⟩ := (hmem i).mp hi
      rw [if_pos hi, if_pos him]
      exact hc i him (u i) hui (v i)
    · rw [if_neg hi]
      exact abv_walsh_le_card abv hψ P P _ _ _
  calc ∏ i, abv (walsh ψ P P (if i ∈ R'.mask then ((R'.sbox i : K → K)) else id) (u i) (v i))
      ≤ ∏ i, (if i ∈ t then c else (Fintype.card K : S)) :=
        Finset.prod_le_prod (fun _ _ => abv.nonneg _) (fun i _ => hle i)
    _ = c ^ t.card * (Fintype.card K : S) ^ (Fintype.card Idx - t.card) := by
        rw [← Finset.prod_mul_prod_compl t, ← Finset.card_compl]
        congr 1
        · rw [Finset.prod_congr rfl fun i hi => if_pos hi, Finset.prod_const]
        · rw [Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_compl.mp hi),
            Finset.prod_const]

omit [DecidableEq K] in
/-- A trail correlation is at most `|Idx → K| ^ r` in absolute value. -/
theorem abv_linCorr_le_card_pow (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (rounds : ℕ → RoundSpec Idx K) (r : ℕ) (T : ℕ → Idx → K) :
    abv (linCorr ψ ℓ rounds r T) ≤ (Fintype.card (Idx → K) : S) ^ r := by
  rw [linCorr, trailCorr, AbsoluteValue.map_prod]
  calc _ ≤ ∏ _n ∈ Finset.range r, (Fintype.card (Idx → K) : S) :=
        Finset.prod_le_prod (fun _ _ => abv.nonneg _)
          (fun _ _ => abv_walsh_le_card abv hψ _ _ _ _ _)
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

/-- **Every charged S-box costs a factor `c`.** For an absolute value that is `1` on the
character's values, if every S-box that the masks of the first `r` rounds charge has
`abv (walsh) ≤ c` at every nonzero input mask, then
`abv (linCorr) ≤ c ^ W · |K| ^ (r · |Idx| - W)` with `W = scheduledWeight rounds T 0 r`, the
number of charged S-boxes. The linear layers are arbitrary. This is the twin of
`Hades.keyCount_le_pow_mul_pow`. -/
theorem abv_linCorr_le (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1) {c : S}
    (rounds : ℕ → RoundSpec Idx K) (r : ℕ)
    (hc : ∀ n < r, ∀ i ∈ (rounds n).mask, ∀ a : K, a ≠ 0 → ∀ b : K,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) ((rounds n).sbox i) a b) ≤ c)
    (T : ℕ → Idx → K) :
    abv (linCorr ψ ℓ rounds r T) ≤
      c ^ scheduledWeight rounds T 0 r *
        (Fintype.card K : S) ^ (r * Fintype.card Idx - scheduledWeight rounds T 0 r) := by
  let w := fun n => sboxWeight (rounds n).mask (T n)
  have hw : ∀ n, w n ≤ Fintype.card Idx := fun n =>
    (sboxWeight_le_weight _ _).trans (Finset.card_le_univ _)
  have hW : scheduledWeight rounds T 0 r = ∑ n ∈ Finset.range r, w n := by
    simp [scheduledWeight, w]
  rw [linCorr, trailCorr, AbsoluteValue.map_prod, hW, ← sum_sub_of_le w hw r,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => abv.nonneg _) (fun n hn =>
    abv_walsh_roundGamma_le abv hψ (rounds n) (hc n (Finset.mem_range.mp hn)) _ _)

/-- **The exact ratio for a lower bound on the charged S-boxes.** Under the hypotheses of
`abv_linCorr_le`, for every `A ≤ scheduledWeight rounds T 0 r`,
`abv (linCorr) · |K| ^ A ≤ c ^ A · |Idx → K| ^ r`: divided by `|Idx → K| ^ r`, the trail's
correlation is at most `(c / |K|) ^ A`. No relation between `c` and `|K|` is assumed. -/
theorem abv_linCorr_mul_card_pow_le_of_le (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    {c : S} (hc0 : 0 ≤ c) (rounds : ℕ → RoundSpec Idx K) (r : ℕ)
    (hc : ∀ n < r, ∀ i ∈ (rounds n).mask, ∀ a : K, a ≠ 0 → ∀ b : K,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) ((rounds n).sbox i) a b) ≤ c)
    (T : ℕ → Idx → K) {A : ℕ} (hA : A ≤ scheduledWeight rounds T 0 r) :
    abv (linCorr ψ ℓ rounds r T) * (Fintype.card K : S) ^ A ≤
      c ^ A * (Fintype.card (Idx → K) : S) ^ r := by
  have hcard : (Fintype.card (Idx → K) : S) ^ r =
      (Fintype.card K : S) ^ (r * Fintype.card Idx) := by
    rw [Fintype.card_fun, Nat.cast_pow, ← pow_mul, mul_comm]
  have h2 := abv_linCorr_le_card_pow (ℓ := ℓ) abv hψ rounds r T
  rw [hcard] at h2 ⊢
  exact mul_pow_le_of_le hc0 (Nat.cast_nonneg _) hA (scheduledWeight_le_mul_card rounds T r)
    (abv_linCorr_le abv hψ rounds r hc T) h2

end Bounds

/-- **The linear trail bound of a HADES schedule.** Under the hypotheses of
`hades_linear_activity`, for an absolute value `abv` that is `1` on the values of `ψ`, and S-boxes
whose Walsh values at every nonzero input mask are at most `c` under `abv`, every linear trail
through the `r + m + s` rounds with a nonzero input mask satisfies
`abv (linCorr) · |K| ^ N ≤ c ^ N · |Idx → K| ^ (r + m + s)` with
`N = (r / 2 + s / 2) · B + r % 2 + s % 2 + μ`. Divided by `|Idx → K| ^ (r + m + s)`, the trail's
correlation is at most `(c / |K|) ^ N` under `abv`.

This bounds one trail: one summand of `walsh_run_eq_sum_linCorr`, whatever the key and the round
constants. It is not a bound on the correlation of the permutation, which is a sum over trails. -/
theorem hades_linear_bound [IsDomain R] (abv : AbsoluteValue R S) (hψ : ∀ t, abv (ψ t) = 1)
    (hP : (Pairing.traceForm ℓ).Separating ψ) (r m s B μ : ℕ) (mask : Finset Idx)
    (boxes : ℕ → Idx → K ≃ K) (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K)) (values : ℕ → Idx → K)
    {c : S} (hc0 : 0 ≤ c)
    (hc : ∀ n < r + m + s, ∀ i, ∀ a : K, a ≠ 0 → ∀ b : K,
      abv (walsh ψ (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) (boxes n i) a b) ≤ c)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (maskLin (linear j)) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (maskLin (linear (r + m + j))) B)
    (A : Module.End K (Idx → K))
    (hmid : ∀ j < m, ((maskLin (linear (r + j))).toLinearMap : Module.End K (Idx → K)) = A)
    (hμ : MiddleBound A mask m μ) {T : ℕ → Idx → K} (h0 : T 0 ≠ 0) :
    abv (linCorr ψ ℓ (hadesSchedule r m s mask boxes linear values) (r + m + s) T) *
        (Fintype.card K : S) ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + μ) ≤
      c ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + μ) *
        (Fintype.card (Idx → K) : S) ^ (r + m + s) := by
  by_cases hz : linCorr ψ ℓ (hadesSchedule r m s mask boxes linear values) (r + m + s) T = 0
  · rw [hz, abv.map_zero, zero_mul]
    exact mul_nonneg (pow_nonneg hc0 _) (pow_nonneg (Nat.cast_nonneg _) _)
  · exact abv_linCorr_mul_card_pow_le_of_le abv hψ hc0
      (hadesSchedule r m s mask boxes linear values) (r + m + s) (fun n hn i _ => hc n hn i) T
      (hades_linear_activity hP r m s B μ mask boxes linear values hbp hbs A hmid hμ h0 hz)

end Hades
