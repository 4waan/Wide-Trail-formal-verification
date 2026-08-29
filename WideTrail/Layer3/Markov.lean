/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer3.Differential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Multiplying the rounds: the Markov cipher model

The wide-trail bound counts active S-boxes. Turning that count into a probability needs
one more step, and it is the step every account of the subject hedges: the differential
probability of a trail is the *product* of its per-round differential probabilities, and
that product is only valid if the round keys are independent and uniform. This is the
Markov cipher assumption.

This file does not assume the product formula. It makes the assumption explicit in the
shape of what is counted, and then proves the product.

`Follows lam γ r k T x` says the pair `(x, x + T 0)` exhibits the difference `T n` after
`n` rounds of `ρₙ(z) = λ(γ(z + kₙ))`, for `n ≤ r`. `trailKeyCount` counts the **round-key
vectors** `k : Fin r → X` under which that happens, for a fixed input `x`. The size of the
round-key space is `|X| ^ r`, so `trailKeyCount / |X| ^ r` is the probability that the
trail is followed, averaged over independent uniform round keys, and

`trailKeyCount lam γ r T x = ∏ n < r, diffCount γ (T n) (λ⁻¹ (T (n+1)))`

is a theorem (`trailKeyCount_eq_prod`) rather than a hypothesis.

Two things are worth being blunt about, because the theorem is easy to over-read.

* **It is an average over keys, not a statement about any one key.** A real cipher has a
  key schedule, its round keys are not independent, and for a fixed key the product
  formula is simply false. `sanity-check/Toy.lean` exhibits a concrete cipher, trail and
  key where the key-averaged count is positive and the fixed-key count is zero. So this
  hypothesis is load-bearing, not decorative.
* **It is one trail, not one differential.** `Differential.diffCount_comp` shows the
  differential of a composition is a *sum* over intermediate differences; a trail bound
  controls one summand. That gap is the hull effect and nothing here closes it.

The counting is arranged so `Follows` peels its first round, which is what makes the
induction a single application of `Finset.card_bij'` plus `Finset.prod_range_succ'`.
-/

set_option autoImplicit false
-- `DecidableEq X` is used inside the proofs (to split a count over the first round key,
-- and to filter at all) but does not appear in every statement, which this linter flags.
-- The suggested fix, `classical` in the proof, would make these counts noncomputable and
-- so break the kernel-evaluated toy-cipher checks that this layer relies on.
set_option linter.unusedDecidableInType false

variable {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]

/-- `x` and `x + T 0` exhibit the differences `T 0, T 1, …, T r` through `r` rounds of the
key-alternating cipher `z ↦ λ(γ(z + kₙ))` under the round-key vector `k`. -/
def Follows (lam γ : X → X) : (r : Nat) → (Fin r → X) → (Nat → X) → X → Prop
  | 0, _, _, _ => True
  | r + 1, k, T, x =>
      lam (γ (x + T 0 + k 0)) - lam (γ (x + k 0)) = T 1
        ∧ Follows lam γ r (Fin.tail k) (fun n => T (n + 1)) (lam (γ (x + k 0)))

instance decidableFollows (lam γ : X → X) :
    ∀ (r : Nat) (k : Fin r → X) (T : Nat → X) (x : X), Decidable (Follows lam γ r k T x)
  | 0, _, _, _ => inferInstanceAs (Decidable True)
  | r + 1, k, T, x =>
      let _ := decidableFollows lam γ r (Fin.tail k) (fun n => T (n + 1)) (lam (γ (x + k 0)))
      inferInstanceAs (Decidable (_ ∧ _))

/-- The round-key vectors under which `x` follows the trail `T`. -/
def followKeys (lam γ : X → X) (r : Nat) (T : Nat → X) (x : X) : Finset (Fin r → X) :=
  Finset.univ.filter (fun k => Follows lam γ r k T x)

/-- How many of the `|X| ^ r` round-key vectors make `x` follow the trail `T`. Dividing by
`|X| ^ r` gives the trail's probability *averaged over independent round keys*, and that
averaging is the Markov cipher assumption, made visible by what is being counted. -/
def trailKeyCount (lam γ : X → X) (r : Nat) (T : Nat → X) (x : X) : Nat :=
  (followKeys lam γ r T x).card

/-- One round of a key-alternating cipher has the S-box layer's differential counts, read
at a relabelled output difference. The key contributes nothing (`diffCount_addKey`) and
the linear layer only relabels (`diffCount_addEquiv`). -/
theorem diffCount_keyedRound (lam : X ≃+ X) (γ : X → X) (k a b : X) :
    diffCount (fun x => lam (γ (x + k))) a b = diffCount γ a (lam.symm b) := by
  rw [diffCount_addEquiv lam (fun x => γ (x + k)) a b, diffCount_addKey]

omit [AddCommGroup X] in
/-- Splitting a filtered count over `Fin (r+1) → X` by the value of the first coordinate.
`Fin.cons` and `Fin.tail` are mutually inverse on each fiber, which is the only content. -/
theorem card_filter_cons {r : Nat} (R : (Fin (r + 1) → X) → Prop) [DecidablePred R] :
    (Finset.univ.filter R).card
      = ∑ k₀ : X, (Finset.univ.filter (fun k : Fin r → X => R (Fin.cons k₀ k))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun k : Fin (r + 1) → X => k 0)
    (t := (Finset.univ : Finset X)) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun k₀ _ => ?_)
  refine Finset.card_bij' (fun k _ => Fin.tail k) (fun k _ => Fin.cons k₀ k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [← hk.2, Fin.cons_self_tail]
    exact hk.1
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨hk, Fin.cons_zero _ _⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [← hk.2, Fin.cons_self_tail]
  · intro k _
    exact Fin.tail_cons _ _

/-- **The Markov product formula, proved.** Over independent round keys the count of
round-key vectors realising a trail is the product of the rounds' differential counts.

The hypothesis is not that the probabilities multiply; the hypothesis is that the count
ranges over independent round keys, and it is visible in the type of `trailKeyCount`. -/
theorem trailKeyCount_eq_prod (lam : X ≃+ X) (γ : X → X) (r : Nat) :
    ∀ (T : Nat → X) (x : X), trailKeyCount lam γ r T x
      = ∏ n ∈ Finset.range r, diffCount γ (T n) (lam.symm (T (n + 1))) := by
  induction r with
  | zero => intro T x; simp [trailKeyCount, followKeys, Follows]
  | succ r ih =>
    intro T x
    rw [trailKeyCount, followKeys, card_filter_cons, Finset.prod_range_succ']
    have hstep : ∀ k₀ : X,
        (Finset.univ.filter
            (fun k : Fin r → X => Follows lam γ (r + 1) (Fin.cons k₀ k) T x)).card
          = if lam (γ (x + T 0 + k₀)) - lam (γ (x + k₀)) = T 1 then
              ∏ n ∈ Finset.range r, diffCount γ (T (n + 1)) (lam.symm (T (n + 1 + 1)))
            else 0 := by
      intro k₀
      have hunfold : ∀ k : Fin r → X, Follows lam γ (r + 1) (Fin.cons k₀ k) T x
          ↔ (lam (γ (x + T 0 + k₀)) - lam (γ (x + k₀)) = T 1
              ∧ Follows lam γ r k (fun n => T (n + 1)) (lam (γ (x + k₀)))) := by
        intro k; simp [Follows]
      by_cases hC : lam (γ (x + T 0 + k₀)) - lam (γ (x + k₀)) = T 1
      · rw [if_pos hC, ← ih (fun n => T (n + 1)) (lam (γ (x + k₀))), trailKeyCount, followKeys]
        exact congrArg Finset.card (Finset.filter_congr (fun k _ => by simp [hunfold k, hC]))
      · rw [if_neg hC, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun k _ h => hC ((hunfold k).mp h).1
    -- The first round's condition on `k₀` *is* membership of `x + k₀` in the S-box layer's
    -- differential set, once the key addition is absorbed and the linear layer inverted.
    have hfirst : (Finset.univ.filter
          (fun k₀ : X => lam (γ (x + T 0 + k₀)) - lam (γ (x + k₀)) = T 1)).card
        = diffCount γ (T 0) (lam.symm (T 1)) := by
      refine Finset.card_equiv
        ⟨fun k₀ => x + k₀, fun y => y - x, fun k₀ => by simp, fun y => by simp⟩ (fun k₀ => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_fn_mk, mem_diffSet]
      have hcomm : x + k₀ + T 0 = x + T 0 + k₀ := by abel
      rw [hcomm, ← map_sub lam]
      exact ⟨fun h => by rw [← h, lam.symm_apply_apply],
        fun h => by rw [h, lam.apply_symm_apply]⟩
    rw [Finset.sum_congr rfl (fun k₀ _ => hstep k₀), ← Finset.sum_filter,
      Finset.sum_const, smul_eq_mul, hfirst, Nat.mul_comm]

/-- The key-averaged probability of a trail does not depend on the input it starts from.
That is not obvious from the definition and it is what makes "the probability of a trail"
a well-posed phrase in the Markov model. -/
theorem trailKeyCount_const (lam : X ≃+ X) (γ : X → X) (r : Nat) (T : Nat → X) (x y : X) :
    trailKeyCount lam γ r T x = trailKeyCount lam γ r T y := by
  rw [trailKeyCount_eq_prod lam γ r T x, trailKeyCount_eq_prod lam γ r T y]

/-- The count of *inputs* following a trail under one fixed round-key vector. The Markov
theorem says nothing about this quantity, and `sanity-check/Toy.lean` shows it does not
obey the product formula. -/
def fixedKeyCount (lam γ : X → X) (r : Nat) (T : Nat → X) (k : Fin r → X) : Nat :=
  (Finset.univ.filter (fun x => Follows lam γ r k T x)).card
