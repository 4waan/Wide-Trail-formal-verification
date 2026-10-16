/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Propagation.Cipher
import WideTrail.Differential.Bricklayer
import WideTrail.Differential.Markov

/-!
# From active S-boxes to a probability

This file closes the chain. Propagation layer produces a number of active S-boxes; `Bricklayer.lean`
turns each active S-box into a factor of at most `u` out of `|K|`; `Markov.lean` multiplies
the rounds. What is left is arithmetic, and one bridge.

The arithmetic is `trailKeyCount_bricklayer_le`. Writing `q = |K|`, `m = |Idx|` and
`W = patternWeight T r`, the product formula and the bundle-wise bound give

`trailKeyCount ≤ u ^ W * q ^ (r·m - W)`,

and if the S-box uniformity clears a factor `2 ^ d`, that is `u · 2 ^ d ≤ q`, then

`trailKeyCount · 2 ^ (d · W) ≤ q ^ (r·m) = |X| ^ r`,

which says exactly `DP ≤ 2 ^ (-d·W)` with no division. For AES, `u = 4`, `q = 256`,
`d = 6`: every active S-box costs a factor `2⁻⁶`.

The bridge is `isTrail_of_trailKeyCount_ne_zero`. Propagation layer's count applies to a
`WideTrailSpec.IsTrail`, a sequence whose consecutive entries are related by the linear
layer applied to something carrying the current support. A differential trail with a
nonzero count is such a sequence, and the reason is
`activePattern_eq_of_diffCount_ne_zero`: an S-box layer of injective S-boxes cannot produce
an output difference whose support differs from its input's. So Propagation layer's
`sbox_preserves` hypothesis is not re-assumed here, it is derived from invertibility. The
`sbox` field of the specification is never read; only its linear layer is.

## What is modelled and what is not

* The cipher is round-uniform: the same `λ = θ ∘ π` in every round. Real AES omits
  `MixColumns` in the last round. The count is over the input differences of rounds
  `0 … r-1`, so the last round's linear layer is not what the bound rests on, but the
  statement here is about the uniform cipher.
* Round keys are independent and uniform. This is where `trailKeyCount` counts key
  vectors, and it is not a property of any keyed instance.
* One trail, not one differential. See `Differential.diffCount_comp`.
-/

set_option autoImplicit false
-- As in `Markov.lean`: `DecidableEq` is carried for computability of the counts, and does
-- not appear in every statement.
set_option linter.unusedDecidableInType false

variable {Idx Col K : Type*} [Fintype Idx] [DecidableEq Idx] [DecidableEq Col] [Fintype Col]
  [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- `∑ (m - wₙ) = r·m - ∑ wₙ` when every `wₙ ≤ m`. Truncated subtraction makes this a real
hypothesis rather than a rearrangement. -/
theorem sum_sub_of_le {m : Nat} (w : Nat → Nat) (h : ∀ n, w n ≤ m) (r : Nat) :
    ∑ n ∈ Finset.range r, (m - w n) = r * m - ∑ n ∈ Finset.range r, w n := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hle : ∑ n ∈ Finset.range r, w n ≤ r * m := by
      calc ∑ n ∈ Finset.range r, w n ≤ ∑ _n ∈ Finset.range r, m :=
            Finset.sum_le_sum (fun n _ => h n)
        _ = r * m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hr : (r + 1) * m = r * m + m := by ring
    have h2 := h r
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    omega

/-- **The trail probability bound.** Every active S-box costs a factor `2 ^ d`, and the
inequality is exact `ℕ` arithmetic: dividing both sides by `|X| ^ r`, the size of the
round-key space, reads `DP(trail) ≤ 2 ^ (-d · W)`. -/
theorem trailKeyCount_bricklayer_le {s : Idx → K → K} {u d : Nat}
    (hu : ∀ i, IsDiffUniform (s i) u) (hd : u * 2 ^ d ≤ Fintype.card K)
    (lam : (Idx → K) ≃+ (Idx → K)) (r : Nat) (T : Nat → (Idx → K)) (x : Idx → K) :
    trailKeyCount lam (bricklayer s) r T x * 2 ^ (d * patternWeight T r)
      ≤ Fintype.card (Idx → K) ^ r := by
  have hwle : ∀ n, weight (T n) ≤ Fintype.card Idx := fun n => Finset.card_le_univ _
  have hWle : patternWeight T r ≤ r * Fintype.card Idx := by
    calc patternWeight T r ≤ ∑ _n ∈ Finset.range r, Fintype.card Idx :=
          Finset.sum_le_sum (fun n _ => hwle n)
      _ = r * Fintype.card Idx := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hcount : trailKeyCount lam (bricklayer s) r T x
      ≤ u ^ patternWeight T r
        * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r) := by
    rw [trailKeyCount_eq_prod]
    calc ∏ n ∈ Finset.range r, diffCount (bricklayer s) (T n) (lam.symm (T (n + 1)))
        ≤ ∏ n ∈ Finset.range r,
            (u ^ weight (T n) * Fintype.card K ^ (Fintype.card Idx - weight (T n))) :=
          Finset.prod_le_prod' (fun n _ => diffCount_bricklayer_le hu _ _)
      _ = u ^ (∑ n ∈ Finset.range r, weight (T n))
            * Fintype.card K ^ (∑ n ∈ Finset.range r, (Fintype.card Idx - weight (T n))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
      _ = _ := by rw [sum_sub_of_le (fun n => weight (T n)) hwle r]; rfl
  calc trailKeyCount lam (bricklayer s) r T x * 2 ^ (d * patternWeight T r)
      ≤ (u ^ patternWeight T r
          * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r))
          * 2 ^ (d * patternWeight T r) := Nat.mul_le_mul_right _ hcount
    _ = (u * 2 ^ d) ^ patternWeight T r
          * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r) := by
        rw [mul_pow, pow_mul]; ring
    _ ≤ Fintype.card K ^ patternWeight T r
          * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd _)
    _ = Fintype.card K ^ (r * Fintype.card Idx) := by
        rw [← pow_add]; congr 1; omega
    _ = Fintype.card (Idx → K) ^ r := by
        rw [Fintype.card_fun, ← pow_mul]; congr 1; ring

/-- **A differential trail with a nonzero count is a wide-trail pattern sequence.**

This is the join. The only property of the S-box layer used is that its S-boxes are
injective, and it yields the support constraint `WideTrailSpec.IsTrail` asks for, so
Propagation layer's active-S-box count applies to a real trail without re-assuming anything. -/
theorem isTrail_of_trailKeyCount_ne_zero {S : WideTrailSpec Idx Col K}
    {s : Idx → K → K} (hs : ∀ i, Function.Injective (s i))
    {lam : (Idx → K) ≃+ (Idx → K)} (hlam : ∀ b, lam b = S.lin b)
    {r : Nat} {T : Nat → (Idx → K)} {x : Idx → K}
    (h : trailKeyCount lam (bricklayer s) r T x ≠ 0) : S.IsTrail T r := by
  rw [trailKeyCount_eq_prod] at h
  intro n hn
  refine ⟨lam.symm (T (n + 1)), activePattern_eq_of_diffCount_ne_zero hs (fun hzero =>
    h (Finset.prod_eq_zero (Finset.mem_range.mpr hn) hzero)), ?_⟩
  rw [← hlam (lam.symm (T (n + 1))), lam.apply_symm_apply]

/-- **The wide-trail differential bound.** For a key-alternating cipher whose S-box layer
is a bricklayer of injective S-boxes with differential uniformity clearing `2 ^ d`, and
whose linear layer is the `θ ∘ π` of a wide-trail specification, every `r`-round
differential trail out of a nonzero difference has probability at most `2` to the minus
`d` times the active-S-box bound of Propagation layer.

Nothing about the S-boxes enters except injectivity and `u`; nothing about the linear layer
enters except its wide-trail specification. -/
theorem trailKeyCount_le_of_spec (S : WideTrailSpec Idx Col K)
    {s : Idx → K → K} {u d : Nat} (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) u) (hd : u * 2 ^ d ≤ Fintype.card K)
    {lam : (Idx → K) ≃+ (Idx → K)} (hlam : ∀ b, lam b = S.lin b)
    {r : Nat} {T : Nat → (Idx → K)} (h0 : T 0 ≠ 0) (x : Idx → K) :
    trailKeyCount lam (bricklayer s) r T x
        * 2 ^ (d * (r / 4 * S.fourRoundBound + (if 2 ≤ r % 4 then S.branch else 0)))
      ≤ Fintype.card (Idx → K) ^ r := by
  by_cases hz : trailKeyCount lam (bricklayer s) r T x = 0
  · simp [hz]
  · have hW := (isTrail_of_trailKeyCount_ne_zero hs hlam hz).bound_rounds h0
    exact le_trans
      (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left d hW)))
      (trailKeyCount_bricklayer_le hu hd lam r T x)

/-- An additive map on a finite state space that kills only the zero pattern is an additive
bijection, so a wide-trail specification whose linear layer is additive supplies the `lam`
the theorems above ask for. -/
noncomputable def linAddEquiv {lin : (Idx → K) → (Idx → K)}
    (hadd : ∀ x y, lin (x + y) = lin x + lin y) (hnd : NonDegenerate lin) :
    (Idx → K) ≃+ (Idx → K) :=
  have hinj : Function.Injective lin := by
    intro x y hxy
    have hsub : lin (x - y) + lin y = lin x := by rw [← hadd]; congr 1; abel
    rw [hxy] at hsub
    refine sub_eq_zero.mp (hnd _ ?_)
    have : lin (x - y) + lin y = 0 + lin y := by rw [hsub, zero_add]
    exact add_right_cancel this
  AddEquiv.ofBijective (AddMonoidHom.mk' lin hadd) (Finite.injective_iff_bijective.mp hinj)

omit [DecidableEq Idx] [DecidableEq K] in
@[simp] theorem linAddEquiv_apply {lin : (Idx → K) → (Idx → K)}
    (hadd : ∀ x y, lin (x + y) = lin x + lin y) (hnd : NonDegenerate lin) (b : Idx → K) :
    linAddEquiv hadd hnd b = lin b := rfl
