/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Poseidon2 internal matrix `c • (diag d + J)`

Poseidon2 mixes its partial rounds with a matrix of the form `c • (diag d + J)`, where
`J` is the all-ones matrix. Applied to a state `x` it costs one sum and one scaling per
coordinate:

  `diagPlusOnes c d x i = c * (d i * x i + ∑ j, x j)`.

For any finite index type and any commutative ring this file proves:

* `diagPlusOnes_eq_mulVec`: the map is multiplication by `c • (diagonal d + J)`;
* `diagPlusOnes_dotProduct`: it is self-adjoint for `dotProduct`, because the matrix is
  symmetric;
* `diagPlusOnes_eq_smul`: the scalar factors out, `diagPlusOnes c d = c • diagPlusOnes 1 d`.

Over a field it proves:

* `diagPlusOnesEquiv`: under `c ≠ 0`, `d i ≠ 0` for every `i`, and
  `1 + ∑ i, (d i)⁻¹ ≠ 0`, the map is a linear equivalence whose inverse is the explicit
  Sherman–Morrison formula `diagPlusOnesInv`;
* `diagPlusOnes_not_injective`: if every `d i` is nonzero but `1 + ∑ i, (d i)⁻¹ = 0`, the
  vector `i ↦ (d i)⁻¹` lies in the kernel, so `diagPlusOnes_injective_iff` gives an exact
  criterion when `c` and all `d i` are nonzero;
* `sum_inv_eq_of_mul_eq_one`, `ne_zero_of_mul_eq_one`: the side conditions from a table of
  explicit inverses, so that a concrete instance never has to compute an inverse.

Nothing is claimed when some `d i` vanishes. The matrix can still be invertible then (for
instance when exactly one `d i` is zero), but the inverse formula used here divides by
every `d i`, so that case is outside its hypotheses.
-/

set_option autoImplicit false

namespace Poseidon2

variable {Idx K : Type*} [Fintype Idx]

section CommRing

variable [CommRing K]

/-- The linear map `x ↦ c • (diag d + J) x`, with `J` the all-ones matrix:
coordinate `i` of the image is `c * (d i * x i + ∑ j, x j)`. -/
def diagPlusOnes (c : K) (d : Idx → K) : (Idx → K) →ₗ[K] (Idx → K) where
  toFun x i := c * (d i * x i + ∑ j, x j)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem diagPlusOnes_apply (c : K) (d : Idx → K) (x : Idx → K) (i : Idx) :
    diagPlusOnes c d x i = c * (d i * x i + ∑ j, x j) :=
  rfl

/-- The scalar factors out of the matrix `c • (diag d + J)`. -/
theorem diagPlusOnes_eq_smul (c : K) (d : Idx → K) :
    diagPlusOnes c d = c • diagPlusOnes 1 d := by
  ext x i
  simp [diagPlusOnes_apply]

/-- **Matrix form.** `diagPlusOnes c d` is multiplication by `c • (diagonal d + J)`, where
`J = Matrix.of fun _ _ => 1` is the all-ones matrix. -/
theorem diagPlusOnes_eq_mulVec [DecidableEq Idx] (c : K) (d : Idx → K) (x : Idx → K) :
    diagPlusOnes c d x = (c • (Matrix.diagonal d + Matrix.of fun _ _ => (1 : K))).mulVec x := by
  funext i
  simp [diagPlusOnes_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_assoc]

/-- The same statement as an equality of linear maps. -/
theorem diagPlusOnes_eq_toLin' [DecidableEq Idx] (c : K) (d : Idx → K) :
    diagPlusOnes c d = Matrix.toLin' (c • (Matrix.diagonal d + Matrix.of fun _ _ => (1 : K))) :=
  LinearMap.ext fun x => by rw [Matrix.toLin'_apply, diagPlusOnes_eq_mulVec]

/-- **Self-adjointness.** `c • (diag d + J)` is symmetric, so moving it across
`dotProduct` changes nothing. Both sides equal
`c * ∑ i, d i * a i * b i + c * (∑ i, a i) * (∑ i, b i)`. -/
theorem diagPlusOnes_dotProduct (c : K) (d : Idx → K) (a b : Idx → K) :
    diagPlusOnes c d a ⬝ᵥ b = a ⬝ᵥ diagPlusOnes c d b := by
  have key : ∀ x y : Idx → K, diagPlusOnes c d x ⬝ᵥ y =
      c * ∑ i, d i * x i * y i + c * (∑ i, x i) * ∑ i, y i := by
    intro x y
    simp only [dotProduct, diagPlusOnes_apply, mul_add, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [key, dotProduct_comm, key]
  have hsym : ∑ i, d i * a i * b i = ∑ i, d i * b i * a i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hsym]
  ring

end CommRing

section Field

variable [Field K]

/-- The Sherman–Morrison inverse of `diagPlusOnes c d`. With `u = y / c`, coordinate `i`
of the preimage is `(u i - (∑ j, u j / d j) / (1 + ∑ j, (d j)⁻¹)) / d i`. -/
def diagPlusOnesInv (c : K) (d : Idx → K) (y : Idx → K) (i : Idx) : K :=
  (y i / c - (∑ j, y j / c / d j) / (1 + ∑ j, (d j)⁻¹)) / d i

variable {c : K} {d : Idx → K}

/-- `diagPlusOnesInv` undoes `diagPlusOnes`. With `S = ∑ k, x k`, the scaled image is
`d j * x j + S`; dividing by `d j` and summing gives `S * (1 + ∑ j, (d j)⁻¹)`, which
recovers `S` and then each `x i`. -/
theorem diagPlusOnesInv_diagPlusOnes (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (x : Idx → K) :
    diagPlusOnesInv c d (diagPlusOnes c d x) = x := by
  funext i
  have hu : ∀ j, diagPlusOnes c d x j / c = d j * x j + ∑ k, x k := fun j => by
    rw [diagPlusOnes_apply, mul_div_cancel_left₀ _ hc]
  have hsum : ∑ j, diagPlusOnes c d x j / c / d j =
      (∑ k, x k) * (1 + ∑ j, (d j)⁻¹) := by
    simp only [hu]
    have hterm : ∀ j, (d j * x j + ∑ k, x k) / d j = x j + (∑ k, x k) * (d j)⁻¹ :=
      fun j => by field_simp [hd j]
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [diagPlusOnesInv, hsum, mul_div_cancel_right₀ _ hs, hu, add_sub_cancel_right,
    mul_div_cancel_left₀ _ (hd i)]

/-- `diagPlusOnes` undoes `diagPlusOnesInv`. The preimage sums to the correction term
`s = (∑ j, y j / c / d j) / (1 + ∑ j, (d j)⁻¹)`, which cancels in each coordinate. -/
theorem diagPlusOnes_diagPlusOnesInv (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (y : Idx → K) :
    diagPlusOnes c d (diagPlusOnesInv c d y) = y := by
  funext i
  set s := (∑ j, y j / c / d j) / (1 + ∑ j, (d j)⁻¹) with hs_def
  have hx : ∀ j, diagPlusOnesInv c d y j = (y j / c - s) / d j := fun _ => rfl
  have hS : ∑ j, diagPlusOnesInv c d y j = s := by
    have h1 : ∑ j, y j / c / d j = s * (1 + ∑ j, (d j)⁻¹) := by
      rw [hs_def, div_mul_cancel₀ _ hs]
    have h2 : ∑ j, s / d j = s * ∑ j, (d j)⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => div_eq_mul_inv s (d j)
    simp only [hx, sub_div, Finset.sum_sub_distrib, h1, h2]
    ring
  rw [diagPlusOnes_apply, hS, hx, mul_div_cancel₀ _ (hd i), sub_add_cancel,
    mul_div_cancel₀ _ hc]

variable (c d) in
/-- **The internal layer as a linear equivalence.** Under the three Sherman–Morrison
hypotheses `diagPlusOnes c d` is invertible, with inverse `diagPlusOnesInv c d`. The
hypotheses are sufficient; `d i ≠ 0` is not necessary for invertibility. -/
def diagPlusOnesEquiv (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0) (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) :
    (Idx → K) ≃ₗ[K] (Idx → K) :=
  { diagPlusOnes c d with
    invFun := diagPlusOnesInv c d
    left_inv := diagPlusOnesInv_diagPlusOnes hc hd hs
    right_inv := diagPlusOnes_diagPlusOnesInv hc hd hs }

theorem diagPlusOnesEquiv_apply (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (x : Idx → K) :
    diagPlusOnesEquiv c d hc hd hs x = diagPlusOnes c d x :=
  rfl

theorem diagPlusOnesEquiv_toLinearMap (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) :
    (diagPlusOnesEquiv c d hc hd hs).toLinearMap = diagPlusOnes c d :=
  rfl

theorem diagPlusOnesEquiv_symm_apply (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (y : Idx → K) :
    (diagPlusOnesEquiv c d hc hd hs).symm y = diagPlusOnesInv c d y :=
  rfl

/-- The side conditions from explicit inverses: if `d i * e i = 1` for every `i`, then
`∑ i, (d i)⁻¹ = ∑ i, e i`. Over `ZMod p` with a literal table `e`, both `he` and the
resulting condition `1 + ∑ i, e i ≠ 0` are closed by `decide`, which does not have to
compute an inverse. -/
theorem sum_inv_eq_of_mul_eq_one {e : Idx → K} (he : ∀ i, d i * e i = 1) :
    ∑ i, (d i)⁻¹ = ∑ i, e i :=
  Finset.sum_congr rfl fun i _ => inv_eq_of_mul_eq_one_right (he i)

omit [Fintype Idx] in
/-- An entry with an explicit inverse is nonzero. -/
theorem ne_zero_of_mul_eq_one {e : Idx → K} (he : ∀ i, d i * e i = 1) (i : Idx) :
    d i ≠ 0 :=
  left_ne_zero_of_mul_eq_one (he i)

/-- **The sum condition cannot be dropped.** If every `d i` is nonzero but
`1 + ∑ i, (d i)⁻¹ = 0`, the nonzero vector `i ↦ (d i)⁻¹` is sent to zero, whatever `c`
is. -/
theorem diagPlusOnes_not_injective (hd : ∀ i, d i ≠ 0) (hs : 1 + ∑ i, (d i)⁻¹ = 0) :
    ¬ Function.Injective (diagPlusOnes c d) := by
  intro hinj
  have hker : diagPlusOnes c d (fun i => (d i)⁻¹) = diagPlusOnes c d 0 := by
    funext i
    rw [diagPlusOnes_apply, mul_inv_cancel₀ (hd i), hs, map_zero, Pi.zero_apply, mul_zero]
  have hzero := hinj hker
  have hne : Nonempty Idx := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    simp at hs
  obtain ⟨i⟩ := hne
  exact inv_ne_zero (hd i) (congrFun hzero i)

/-- With `c` and every `d i` nonzero, `diagPlusOnes c d` is injective exactly when
`1 + ∑ i, (d i)⁻¹ ≠ 0`. -/
theorem diagPlusOnes_injective_iff (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0) :
    Function.Injective (diagPlusOnes c d) ↔ 1 + ∑ i, (d i)⁻¹ ≠ 0 :=
  ⟨fun hinj hs => diagPlusOnes_not_injective hd hs hinj,
    fun hs => (diagPlusOnesEquiv c d hc hd hs).injective⟩

end Field

end Poseidon2
