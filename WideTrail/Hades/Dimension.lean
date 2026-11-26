/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Krylov

/-!
# Exact inactive dimensions, and a criterion for the Poseidon2 internal layer

`inactiveSpace L mask r` is the space of differences `a` with `(L ^ j) a i = 0` for every
`j < r` and every `i ∈ mask`: the inactive differences, which avoid the partial-round S-boxes
through `r` consecutive partial rounds, with `r - 1` applications of `L` between them. This file
describes how that space shrinks as `r` grows. For one S-box coordinate and a state of width
`t = card Idx`, `card_sub_le_finrank_inactiveSpace` leaves a nonzero inactive difference for
every `r ≤ t - 1`; the results here say when no nonzero difference stays inactive through `t`
consecutive partial rounds, and that each round then removes exactly one dimension. This is the
linear-algebra fact behind the rule that at most `t - 1` partial rounds can be linearized.

## General results, for any linear map `L` on `Idx → K` and any mask

* `inactiveSpace_succ`: the recurrence
  `inactiveSpace L mask (r + 1) = inactiveSpace L mask 1 ⊓ (inactiveSpace L mask r).comap L`.
* `inactiveSpace_eq_of_succ_eq`: once two consecutive spaces agree, the chain is constant from
  there on. `inactiveSpace_eq_card`: for `card Idx ≤ r` the space equals the one for
  `r = card Idx`. The proof counts dimensions: each strict step lowers `finrank` by at least
  one (`finrank_inactiveSpace_add_le`), so at most `card Idx` strict steps occur.
* The stable space `V = inactiveSpace L mask (card Idx)` is invariant under `L`
  (`apply_mem_inactiveSpace_card`), lies in `inactiveSpace L mask 1`
  (`inactiveSpace_card_le_one`), and contains every `L`-invariant subspace that lies in
  `inactiveSpace L mask 1` (`le_inactiveSpace_of_invariant`). Membership in `V` is
  inactivity for every number of rounds (`mem_inactiveSpace_card_iff`), so `V = ⊥` exactly
  when no nonzero difference stays inactive forever (`no_infinite_inactive_trail`).
* `finrank_inactiveSpace_sub_succ_le`: one more round lowers the dimension by at most
  `mask.card`. For a single S-box coordinate `i0` with `V = ⊥`, the dimension is exactly
  `card Idx - r` for `r ≤ card Idx` (`finrank_inactiveSpace_singleton`).

## The Poseidon2 internal layer `c • (diag d + J)`

* `inactiveSpace_diagPlusOnes_card_eq_bot_iff`: for `c ≠ 0` and any `d : Idx → K`, no nonzero
  difference stays off coordinate `i0` through `card Idx` consecutive partial rounds exactly when
  the diagonal entries `d i`, `i ≠ i0`, are pairwise distinct. The entry `d i0` plays no role,
  and no entry needs to be nonzero.
* `finrank_inactiveSpace_diagPlusOnes`: under that condition the dimension is exactly
  `card Idx - r` for `r ≤ card Idx`.

This is a second, general route to statements such as
`Poseidon2.KoalaBear.internal_inactive_trivial`.
The first route, `inactiveSpace_eq_bot_of_krylov` and `inactiveSpace_diagPlusOnes_eq_bot` in
`Krylov.lean`, checks literal Krylov tables for one concrete field by `decide`; the route here
reduces the question to the distinctness of the diagonal entries, for every field.

## What is not claimed

Everything here concerns inactive differences of the partial rounds only, for a fixed linear
map and mask. It is not a proof of resistance to subspace trails in general (only the subspaces
cut out by inactivity of the masked coordinates are considered), and it says nothing about the
full rounds, the S-boxes, the round constants, or algebraic attacks.
-/

set_option autoImplicit false

namespace Hades

variable {Idx K : Type*} [Field K]

/-! ### The recurrence -/

/-- Zero rounds impose no condition. -/
theorem inactiveSpace_zero (L : Module.End K (Idx → K)) (mask : Finset Idx) :
    inactiveSpace L mask 0 = ⊤ :=
  eq_top_iff.mpr fun _ _ j hj => absurd hj (Nat.not_lt_zero j)

/-- One round: the masked coordinates of the difference itself vanish. -/
theorem mem_inactiveSpace_one {L : Module.End K (Idx → K)} {mask : Finset Idx}
    {a : Idx → K} : a ∈ inactiveSpace L mask 1 ↔ ∀ i ∈ mask, a i = 0 := by
  rw [mem_inactiveSpace]
  constructor
  · intro h i hi
    simpa using h 0 Nat.one_pos i hi
  · intro h j hj i hi
    rw [Nat.lt_one_iff.mp hj, pow_zero, Module.End.one_apply]
    exact h i hi

/-- **The recurrence.** A difference stays inactive through `r + 1` consecutive partial rounds
exactly when it is inactive in the first one and its image under `L` stays inactive through the
next `r`. -/
theorem inactiveSpace_succ (L : Module.End K (Idx → K)) (mask : Finset Idx) (r : ℕ) :
    inactiveSpace L mask (r + 1) =
      inactiveSpace L mask 1 ⊓ (inactiveSpace L mask r).comap L := by
  ext a
  rw [Submodule.mem_inf, Submodule.mem_comap, mem_inactiveSpace, mem_inactiveSpace,
    mem_inactiveSpace]
  constructor
  · intro h
    refine ⟨fun j hj i hi => h j (by omega) i hi, fun j hj i hi => ?_⟩
    have hj' := h (j + 1) (by omega) i hi
    rwa [pow_succ, Module.End.mul_apply] at hj'
  · rintro ⟨h1, h2⟩ j hj i hi
    cases j with
    | zero => exact h1 0 Nat.one_pos i hi
    | succ j =>
      rw [pow_succ, Module.End.mul_apply]
      exact h2 j (by omega) i hi

/-! ### Stabilisation -/

/-- **Once the chain stops, it stays stopped.** If one more round removes no difference at
step `r`, then no further round does. -/
theorem inactiveSpace_eq_of_succ_eq {L : Module.End K (Idx → K)} {mask : Finset Idx} {r : ℕ}
    (h : inactiveSpace L mask (r + 1) = inactiveSpace L mask r) {n : ℕ} (hn : r ≤ n) :
    inactiveSpace L mask n = inactiveSpace L mask r := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih => rw [inactiveSpace_succ, ih, ← inactiveSpace_succ, h]

variable [Fintype Idx]

/-- **Each strict step costs a dimension.** If the first `k` steps of the chain are all
strict, then `finrank (inactiveSpace L mask k) + k ≤ card Idx`. -/
theorem finrank_inactiveSpace_add_le (L : Module.End K (Idx → K)) (mask : Finset Idx) {k : ℕ}
    (h : ∀ m < k, inactiveSpace L mask (m + 1) ≠ inactiveSpace L mask m) :
    Module.finrank K (inactiveSpace L mask k) + k ≤ Fintype.card Idx := by
  induction k with
  | zero =>
    have hle := Submodule.finrank_le (inactiveSpace L mask 0)
    rw [Module.finrank_fintype_fun_eq_card] at hle
    omega
  | succ k ih =>
    have hk := ih fun m hm => h m (by omega)
    have hlt : inactiveSpace L mask (k + 1) < inactiveSpace L mask k :=
      lt_of_le_of_ne (inactiveSpace_anti L mask (Nat.le_succ k)) (h k (Nat.lt_succ_self k))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

/-- **The chain is constant from `card Idx` on.** For `card Idx ≤ r`, the differences that stay
inactive through `r` consecutive partial rounds are those that stay inactive through
`card Idx` of them. -/
theorem inactiveSpace_eq_card (L : Module.End K (Idx → K)) (mask : Finset Idx) {r : ℕ}
    (hr : Fintype.card Idx ≤ r) :
    inactiveSpace L mask r = inactiveSpace L mask (Fintype.card Idx) := by
  by_cases hex : ∃ m < Fintype.card Idx, inactiveSpace L mask (m + 1) = inactiveSpace L mask m
  · obtain ⟨m, hm, heq⟩ := hex
    rw [inactiveSpace_eq_of_succ_eq heq (by omega : m ≤ r),
      inactiveSpace_eq_of_succ_eq heq hm.le]
  · push Not at hex
    have hcount := finrank_inactiveSpace_add_le L mask hex
    have hbot : inactiveSpace L mask (Fintype.card Idx) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by omega)
    rw [hbot]
    exact le_bot_iff.mp (hbot ▸ inactiveSpace_anti L mask hr)

/-! ### The stable space -/

/-- The stable space lies in the space of differences inactive in one round. -/
theorem inactiveSpace_card_le_one (L : Module.End K (Idx → K)) (mask : Finset Idx) :
    inactiveSpace L mask (Fintype.card Idx) ≤ inactiveSpace L mask 1 := by
  rw [← inactiveSpace_eq_card L mask (Nat.le_succ _)]
  exact inactiveSpace_anti L mask (by omega)

/-- **The stable space is invariant under `L`.** -/
theorem apply_mem_inactiveSpace_card {L : Module.End K (Idx → K)} {mask : Finset Idx}
    {a : Idx → K} (ha : a ∈ inactiveSpace L mask (Fintype.card Idx)) :
    L a ∈ inactiveSpace L mask (Fintype.card Idx) := by
  rw [← inactiveSpace_eq_card L mask (Nat.le_succ _), inactiveSpace_succ] at ha
  exact ha.2

omit [Fintype Idx] in
/-- **Every invariant subspace of inactive differences stays inactive.** An `L`-invariant
subspace `W` of `inactiveSpace L mask 1` lies in `inactiveSpace L mask r` for every `r`; in
particular in the stable space, which is therefore the largest such subspace. -/
theorem le_inactiveSpace_of_invariant (L : Module.End K (Idx → K)) (mask : Finset Idx)
    {W : Submodule K (Idx → K)} (hW : ∀ a ∈ W, L a ∈ W) (h1 : W ≤ inactiveSpace L mask 1)
    (r : ℕ) : W ≤ inactiveSpace L mask r := by
  intro a ha j _ i hi
  have hpow : ∀ m : ℕ, (L ^ m) a ∈ W := by
    intro m
    induction m with
    | zero => simpa using ha
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  exact mem_inactiveSpace_one.mp (h1 (hpow j)) i hi

/-- **Inactive through `card Idx` rounds is inactive forever.** A difference stays inactive
through `card Idx` consecutive partial rounds exactly when `(L ^ j) a i = 0` for every `j` and
every `i ∈ mask`. -/
theorem mem_inactiveSpace_card_iff {L : Module.End K (Idx → K)} {mask : Finset Idx}
    {a : Idx → K} :
    a ∈ inactiveSpace L mask (Fintype.card Idx) ↔ ∀ j : ℕ, ∀ i ∈ mask, (L ^ j) a i = 0 := by
  constructor
  · intro ha j i hi
    rw [← inactiveSpace_eq_card L mask (Nat.le_add_right (Fintype.card Idx) (j + 1))] at ha
    exact ha j (by omega) i hi
  · intro h j _ i hi
    exact h j i hi

/-- **No infinite inactive trail.** The stable space is trivial exactly when no nonzero
difference `a` has `(L ^ j) a i = 0` for every `j` and every `i ∈ mask`. -/
theorem no_infinite_inactive_trail (L : Module.End K (Idx → K)) (mask : Finset Idx) :
    inactiveSpace L mask (Fintype.card Idx) = ⊥ ↔
      ¬ ∃ a : Idx → K, a ≠ 0 ∧ ∀ j : ℕ, ∀ i ∈ mask, (L ^ j) a i = 0 := by
  rw [Submodule.eq_bot_iff]
  simp only [mem_inactiveSpace_card_iff]
  constructor
  · rintro h ⟨a, ha, hall⟩
    exact ha (h a hall)
  · intro h a ha
    by_contra hne
    exact h ⟨a, hne, ha⟩

/-! ### Dimensions -/

omit [Fintype Idx] in
/-- **One more round costs at most `mask.card` dimensions.** The extra round adds the
`mask.card` conditions `(L ^ r) a i = 0`, `i ∈ mask`. -/
theorem finrank_inactiveSpace_sub_succ_le [Finite Idx] (L : Module.End K (Idx → K))
    (mask : Finset Idx) (r : ℕ) :
    Module.finrank K (inactiveSpace L mask r) - Module.finrank K (inactiveSpace L mask (r + 1))
      ≤ mask.card := by
  cases nonempty_fintype Idx
  let φ : (Idx → K) →ₗ[K] (mask → K) :=
    LinearMap.funLeft K K (fun i : mask => (i : Idx)) ∘ₗ (L ^ r)
  have hS : inactiveSpace L mask (r + 1) = inactiveSpace L mask r ⊓ LinearMap.ker φ := by
    ext a
    rw [Submodule.mem_inf, LinearMap.mem_ker, mem_inactiveSpace, mem_inactiveSpace]
    constructor
    · intro h
      refine ⟨fun j hj i hi => h j (by omega) i hi, ?_⟩
      funext i
      exact h r (Nat.lt_succ_self r) i i.2
    · rintro ⟨h, hφ⟩ j hj i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h j hj i hi
      · exact congrFun hφ ⟨i, hi⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (inactiveSpace L mask r) (LinearMap.ker φ)
  have h2 := Submodule.finrank_le (inactiveSpace L mask r ⊔ LinearMap.ker φ)
  have h3 := LinearMap.finrank_range_add_finrank_ker φ
  have h4 := Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_fintype_fun_eq_card] at h2 h3
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h4
  rw [hS]
  omega

omit [Fintype Idx] in
/-- Iterating `finrank_inactiveSpace_sub_succ_le`: `k` more rounds cost at most
`k * mask.card` dimensions. -/
theorem finrank_inactiveSpace_le_add [Finite Idx] (L : Module.End K (Idx → K))
    (mask : Finset Idx) (r k : ℕ) :
    Module.finrank K (inactiveSpace L mask r)
      ≤ Module.finrank K (inactiveSpace L mask (r + k)) + k * mask.card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := finrank_inactiveSpace_sub_succ_le L mask (r + k)
    have hmono := Submodule.finrank_mono
      (inactiveSpace_anti L mask (Nat.le_succ (r + k)))
    rw [show r + (k + 1) = r + k + 1 by omega, Nat.succ_mul]
    omega

/-- **Exact dimensions for one S-box coordinate.** If no nonzero difference stays off
coordinate `i0` through `card Idx` consecutive partial rounds, then for `r ≤ card Idx` the
differences that stay off `i0` through `r` consecutive partial rounds form a space of dimension
exactly `card Idx - r`: each round removes exactly one dimension. -/
theorem finrank_inactiveSpace_singleton (L : Module.End K (Idx → K)) (i0 : Idx)
    (hV : inactiveSpace L {i0} (Fintype.card Idx) = ⊥) {r : ℕ} (hr : r ≤ Fintype.card Idx) :
    Module.finrank K (inactiveSpace L {i0} r) = Fintype.card Idx - r := by
  have hlower := card_sub_le_finrank_inactiveSpace L {i0} r
  have hupper := finrank_inactiveSpace_le_add L {i0} r (Fintype.card Idx - r)
  rw [Finset.card_singleton, mul_one] at hlower hupper
  rw [show r + (Fintype.card Idx - r) = Fintype.card Idx by omega, hV, finrank_bot] at hupper
  omega

/-! ### The Poseidon2 internal layer -/

/-- **Criterion for the internal layer.** For `c ≠ 0` and any diagonal `d`, no nonzero
difference stays off coordinate `i0` through `card Idx` consecutive partial rounds with
`c • (diag d + J)` exactly when the entries `d i`, `i ≠ i0`, are pairwise distinct.

If `d i = d j` for distinct `i, j ≠ i0`, the difference `e_i - e_j` has coordinate sum `0` and
is an eigenvector, so it never reaches `i0`. Conversely, on the stable space the coordinate
sum vanishes, so the layer acts there as `diag d` (up to `c`); multiplying by the factors
`d k - d l`, `l ≠ i0, k0`, isolates coordinate `k0`. -/
theorem inactiveSpace_diagPlusOnes_card_eq_bot_iff {c : K} (hc : c ≠ 0) (d : Idx → K)
    (i0 : Idx) :
    inactiveSpace (Poseidon2.diagPlusOnes c d) {i0} (Fintype.card Idx) = ⊥ ↔
      Set.InjOn d {i | i ≠ i0} := by
  classical
  constructor
  · intro hbot
    by_contra hinj
    simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨i, hi, j, hj, hdij, hij⟩ := hinj
    replace hi : i ≠ i0 := hi
    replace hj : j ≠ i0 := hj
    let v : Idx → K := Pi.single i 1 - Pi.single j 1
    have hsum : ∑ m, v m = 0 := by simp [v, Finset.sum_sub_distrib]
    have hLv : Poseidon2.diagPlusOnes c d v = (c * d i) • v := by
      funext k
      rw [Poseidon2.diagPlusOnes_apply, hsum, add_zero, Pi.smul_apply, smul_eq_mul, mul_assoc]
      congr 1
      by_cases hkj : k = j
      · rw [hkj, hdij]
      · by_cases hki : k = i
        · rw [hki]
        · simp [v, hkj, hki]
    have hpow : ∀ m : ℕ, (Poseidon2.diagPlusOnes c d ^ m) v = (c * d i) ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hLv, smul_smul, pow_succ]
    have hmem : v ∈ inactiveSpace (Poseidon2.diagPlusOnes c d) {i0} (Fintype.card Idx) := by
      intro m _ k hk
      rw [Finset.mem_singleton.mp hk, hpow, Pi.smul_apply, smul_eq_mul]
      simp [v, Ne.symm hi, Ne.symm hj]
    rw [hbot, Submodule.mem_bot] at hmem
    have hvi := congrFun hmem i
    simp [v, hij] at hvi
  · intro hinj
    rw [inactiveSpace_diagPlusOnes hc]
    set V := inactiveSpace (Poseidon2.diagPlusOnes (1 : K) d) {i0} (Fintype.card Idx)
    have h0 : ∀ w ∈ V, w i0 = 0 := fun w hw =>
      mem_inactiveSpace_one.mp (inactiveSpace_card_le_one _ _ hw) i0 (Finset.mem_singleton_self _)
    have hsum : ∀ w ∈ V, ∑ k, w k = 0 := by
      intro w hw
      have h := h0 _ (apply_mem_inactiveSpace_card hw)
      rwa [Poseidon2.diagPlusOnes_apply, h0 w hw, mul_zero, zero_add, one_mul] at h
    have hD : ∀ w ∈ V, (fun k => d k * w k) ∈ V := by
      intro w hw
      have h := apply_mem_inactiveSpace_card hw
      have heq : Poseidon2.diagPlusOnes (1 : K) d w = fun k => d k * w k := by
        funext k
        rw [Poseidon2.diagPlusOnes_apply, hsum w hw, add_zero, one_mul]
      rwa [heq] at h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hprod : ∀ S : Finset Idx, (fun k => (∏ l ∈ S, (d k - d l)) * v k) ∈ V := by
      intro S
      induction S using Finset.induction_on with
      | empty => simpa using hv
      | insert a S ha ih =>
        have heq : (fun k => (∏ l ∈ insert a S, (d k - d l)) * v k) =
            (fun k => d k * ((∏ l ∈ S, (d k - d l)) * v k)) -
              d a • fun k => (∏ l ∈ S, (d k - d l)) * v k := by
          funext k
          simp only [Finset.prod_insert ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [heq]
        exact V.sub_mem (hD _ ih) (V.smul_mem _ ih)
    funext k0
    by_cases hk0 : k0 = i0
    · rw [hk0]
      exact h0 v hv
    · let S : Finset Idx := Finset.univ.filter fun l => l ≠ i0 ∧ l ≠ k0
      have hs := hsum _ (hprod S)
      rw [Finset.sum_eq_single k0] at hs
      · have hne : ∏ l ∈ S, (d k0 - d l) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro l hl
          have hl' := (Finset.mem_filter.mp hl).2
          exact sub_ne_zero.mpr fun h => hl'.2 (hinj hk0 hl'.1 h).symm
        exact (mul_eq_zero.mp hs).resolve_left hne
      · intro k _ hk
        by_cases hki : k = i0
        · rw [hki, h0 v hv, mul_zero]
        · have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki, hk⟩
          rw [Finset.prod_eq_zero hkS (sub_self _), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ k0) h

/-- **Exact dimensions for the internal layer.** For `c ≠ 0` and diagonal entries `d i`,
`i ≠ i0`, pairwise distinct, the differences that stay off coordinate `i0` through `r`
consecutive partial rounds with `c • (diag d + J)` form a space of dimension exactly
`card Idx - r`, for every `r ≤ card Idx`. -/
theorem finrank_inactiveSpace_diagPlusOnes {c : K} (hc : c ≠ 0) (d : Idx → K) (i0 : Idx)
    (hinj : Set.InjOn d {i | i ≠ i0}) {r : ℕ} (hr : r ≤ Fintype.card Idx) :
    Module.finrank K (inactiveSpace (Poseidon2.diagPlusOnes c d) {i0} r) =
      Fintype.card Idx - r :=
  finrank_inactiveSpace_singleton _ i0
    ((inactiveSpace_diagPlusOnes_card_eq_bot_iff hc d i0).mpr hinj) hr

end Hades
