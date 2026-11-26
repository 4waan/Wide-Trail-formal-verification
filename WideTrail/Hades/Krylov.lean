/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Subspace
import WideTrail.Algebra.DiagPlusOnes

/-!
# Deciding the inactive space of a concrete partial-round matrix

`Subspace.lean` reduces the partial-round count to one hypothesis,
`inactiveSpace L mask r = ⊥`. For one S-box coordinate `i0` this is a rank condition:
the `r` functionals `a ↦ (L ^ j) a i0`, `j < r`, must have no common nonzero zero. This
file turns that condition into finite checks on explicit tables.

* `inactiveSpace_smul`: a nonzero scalar factor of `L` does not change the space, so a
  Montgomery-style constant in front of the matrix can be dropped.
* `pow_apply_eq_dotProduct`: if `L` is self-adjoint for `dotProduct`, the functional
  `a ↦ (L ^ j) a i` is `dotProduct a ((L ^ j) (Pi.single i 1))`. Its coefficient vectors
  are the Krylov vectors `u j = L ^ j e_i0`, computed by applying `L` forward.
* `mem_inactiveSpace_singleton_iff`: for self-adjoint `L`, membership in
  `inactiveSpace L {i0} r` is orthogonality to `u 0, …, u (r - 1)`.
* `inactiveSpace_eq_bot_of_krylov`: the certificate. Given a table `u` satisfying
  `u 0 = e_i0` and `u (j + 1) = L (u j)`, and a table `D` with `D * U = 1` (where `U` has
  rows `u j`), the inactive space is trivial. Every hypothesis except self-adjointness
  is a finite equation between explicit tables, which `decide` can check for a concrete
  `L` over `ZMod p`. Indices are encoded as `∀ j k : Fin r, (k : ℕ) = j + 1 → …` so that
  the statements are decidable without side proofs.
* `inactiveSpace_diagPlusOnes_eq_bot`: the same certificate for the Poseidon2 internal
  matrix `c • (diag d + J)`, where self-adjointness and the scalar `c` are discharged
  once and for all.

Only the direction "certificate implies trivial space" is proved. For self-adjoint `L`
the certificate exists whenever the space is trivial (`U` then has full column rank), but
that converse is not stated here. Nothing in this file depends on `L` being invertible.
-/

set_option autoImplicit false

namespace Hades

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx]

section CommRing

variable [CommRing K]

omit [DecidableEq Idx] in
/-- Powers of a `dotProduct`-self-adjoint map are self-adjoint. -/
theorem pow_dotProduct_comm (L : Module.End K (Idx → K))
    (hL : ∀ a b : Idx → K, L a ⬝ᵥ b = a ⬝ᵥ L b) (j : ℕ) (a b : Idx → K) :
    (L ^ j) a ⬝ᵥ b = a ⬝ᵥ (L ^ j) b := by
  induction j generalizing a b with
  | zero => simp
  | succ j ih =>
    calc (L ^ (j + 1)) a ⬝ᵥ b = (L ^ j) (L a) ⬝ᵥ b := by rw [pow_succ, Module.End.mul_apply]
      _ = L a ⬝ᵥ (L ^ j) b := ih (L a) b
      _ = a ⬝ᵥ L ((L ^ j) b) := hL a _
      _ = a ⬝ᵥ (L ^ (j + 1)) b := by rw [pow_succ', Module.End.mul_apply]

/-- **The inactivity conditions as dot products.** For `L` self-adjoint, coordinate `i`
of `(L ^ j) a` is the dot product of `a` with the Krylov vector `(L ^ j) e_i`. -/
theorem pow_apply_eq_dotProduct (L : Module.End K (Idx → K))
    (hL : ∀ a b : Idx → K, L a ⬝ᵥ b = a ⬝ᵥ L b) (j : ℕ) (a : Idx → K) (i : Idx) :
    (L ^ j) a i = a ⬝ᵥ (L ^ j) (Pi.single i 1) := by
  rw [← pow_dotProduct_comm L hL, dotProduct_single_one]

omit [Fintype Idx] [DecidableEq Idx] in
/-- A table satisfying the forward recurrence `u 0 = v`, `u (j + 1) = L (u j)` lists the
powers `(L ^ j) v`. The recurrence is phrased with two `Fin r` indices so that it is
decidable for explicit tables. -/
theorem eq_pow_apply_of_recurrence (L : Module.End K (Idx → K)) (v : Idx → K) {r : ℕ}
    (u : Fin r → Idx → K) (hu0 : ∀ j : Fin r, (j : ℕ) = 0 → u j = v)
    (hu : ∀ j k : Fin r, (k : ℕ) = j + 1 → u k = L (u j)) (j : Fin r) :
    u j = (L ^ (j : ℕ)) v := by
  obtain ⟨n, hn⟩ := j
  induction n with
  | zero => simpa using hu0 ⟨0, hn⟩ rfl
  | succ n ih =>
    have hprev : u ⟨n, by omega⟩ = (L ^ n) v := ih (by omega)
    change u ⟨n + 1, hn⟩ = (L ^ (n + 1)) v
    rw [hu ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl, hprev, pow_succ', Module.End.mul_apply]

end CommRing

section Field

variable [Field K]

omit [Fintype Idx] [DecidableEq Idx] in
/-- **A nonzero scalar factor is invisible.** `(c • L) ^ j = c ^ j • L ^ j`, and
`c ^ j ≠ 0` does not change which coordinates vanish. -/
theorem inactiveSpace_smul (L : Module.End K (Idx → K)) (mask : Finset Idx) (r : ℕ)
    {c : K} (hc : c ≠ 0) : inactiveSpace (c • L) mask r = inactiveSpace L mask r := by
  ext a
  simp only [mem_inactiveSpace, smul_pow, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    mul_eq_zero, pow_ne_zero _ hc, false_or]

/-- **Membership for one S-box coordinate.** For `L` self-adjoint and `u j = L ^ j e_i0`,
a difference stays off coordinate `i0` for `r` rounds exactly when it is orthogonal to
`u 0, …, u (r - 1)`. -/
theorem mem_inactiveSpace_singleton_iff (L : Module.End K (Idx → K))
    (hL : ∀ a b : Idx → K, L a ⬝ᵥ b = a ⬝ᵥ L b) (i0 : Idx) (r : ℕ) (u : Fin r → Idx → K)
    (hu : ∀ j : Fin r, u j = (L ^ (j : ℕ)) (Pi.single i0 1)) (a : Idx → K) :
    a ∈ inactiveSpace L {i0} r ↔ ∀ j : Fin r, u j ⬝ᵥ a = 0 := by
  rw [mem_inactiveSpace]
  constructor
  · intro ha j
    rw [hu j, dotProduct_comm, ← pow_apply_eq_dotProduct L hL]
    exact ha j j.isLt i0 (Finset.mem_singleton_self i0)
  · intro ha j hj i hi
    have huj : u ⟨j, hj⟩ = (L ^ j) (Pi.single i0 1) := hu ⟨j, hj⟩
    rw [Finset.mem_singleton.mp hi, pow_apply_eq_dotProduct L hL, dotProduct_comm, ← huj]
    exact ha ⟨j, hj⟩

/-- **Krylov certificate for a trivial inactive space.** Let `L` be self-adjoint for
`dotProduct`. Suppose the table `u` lists `e_i0, L e_i0, …, L ^ (r - 1) e_i0` (checked
through the recurrence `hu0`, `hu`), and the table `D` is a left inverse of the matrix
with rows `u j` (`hD`). Then no nonzero difference stays off coordinate `i0` for `r`
consecutive applications of `L`.

For a concrete `L` over `ZMod p` given by an explicit formula, and literal tables `u`
and `D`, the hypotheses `hu0`, `hu` and `hD` are closed by `decide`. -/
theorem inactiveSpace_eq_bot_of_krylov (L : Module.End K (Idx → K))
    (hL : ∀ a b : Idx → K, L a ⬝ᵥ b = a ⬝ᵥ L b) (i0 : Idx) (r : ℕ) (u : Fin r → Idx → K)
    (hu0 : ∀ j : Fin r, (j : ℕ) = 0 → u j = Pi.single i0 1)
    (hu : ∀ j k : Fin r, (k : ℕ) = j + 1 → u k = L (u j))
    (D : Idx → Fin r → K) (hD : ∀ i k, ∑ j, D i j * u j k = if i = k then 1 else 0) :
    inactiveSpace L {i0} r = ⊥ := by
  have hrow := mem_inactiveSpace_singleton_iff L hL i0 r u
    (eq_pow_apply_of_recurrence L (Pi.single i0 1) u hu0 hu)
  rw [Submodule.eq_bot_iff]
  intro a ha
  have horth := (hrow a).mp ha
  funext i
  calc a i = ∑ k, (if i = k then 1 else 0) * a k := by simp
    _ = ∑ k, (∑ j, D i j * u j k) * a k := by simp only [hD]
    _ = ∑ j, D i j * (u j ⬝ᵥ a) := by
        simp only [dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [horth]

omit [DecidableEq Idx] in
/-- The scalar in front of the Poseidon2 internal matrix can be dropped. -/
theorem inactiveSpace_diagPlusOnes {c : K} (hc : c ≠ 0) (d : Idx → K) (mask : Finset Idx)
    (r : ℕ) :
    inactiveSpace (Poseidon2.diagPlusOnes c d) mask r =
      inactiveSpace (Poseidon2.diagPlusOnes 1 d) mask r := by
  rw [Poseidon2.diagPlusOnes_eq_smul, inactiveSpace_smul _ _ _ hc]

/-- **Krylov certificate for the Poseidon2 internal matrix `c • (diag d + J)`.** The
recurrence uses the unscaled map `x ↦ (i ↦ d i * x i + ∑ m, x m)`; the scalar `c` only
needs to be nonzero, and self-adjointness holds for every `d`. The remaining hypotheses
are finite equations between explicit tables. -/
theorem inactiveSpace_diagPlusOnes_eq_bot {c : K} (hc : c ≠ 0) (d : Idx → K) (i0 : Idx)
    (r : ℕ) (u : Fin r → Idx → K)
    (hu0 : ∀ j : Fin r, (j : ℕ) = 0 → u j = Pi.single i0 1)
    (hu : ∀ j k : Fin r, (k : ℕ) = j + 1 → u k = fun i => d i * u j i + ∑ m, u j m)
    (D : Idx → Fin r → K) (hD : ∀ i k, ∑ j, D i j * u j k = if i = k then 1 else 0) :
    inactiveSpace (Poseidon2.diagPlusOnes c d) {i0} r = ⊥ := by
  rw [inactiveSpace_diagPlusOnes hc]
  refine inactiveSpace_eq_bot_of_krylov _ (Poseidon2.diagPlusOnes_dotProduct 1 d) i0 r u hu0
    (fun j k hjk => ?_) D hD
  rw [hu j k hjk]
  funext i
  rw [Poseidon2.diagPlusOnes_apply, one_mul]

end Field

end Hades
