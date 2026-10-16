import WideTrail.Differential.Markov

/-! The independent-key counting theorem for round-specific nonlinear and linear maps. -/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Scheduled

variable {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]

def Follows (lam : Nat → X ≃+ X) (γ : Nat → X → X) :
    (r : Nat) → (Fin r → X) → (Nat → X) → X → Prop
  | 0, _, _, _ => True
  | r + 1, k, T, x =>
      lam 0 (γ 0 (x + T 0 + k 0)) - lam 0 (γ 0 (x + k 0)) = T 1
        ∧ Follows (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
          (Fin.tail k) (fun n => T (n + 1)) (lam 0 (γ 0 (x + k 0)))

instance decidableFollows (lam : Nat → X ≃+ X) (γ : Nat → X → X) :
    ∀ (r : Nat) (k : Fin r → X) (T : Nat → X) (x : X), Decidable (Follows lam γ r k T x)
  | 0, _, _, _ => inferInstanceAs (Decidable True)
  | r + 1, k, T, x =>
      let _ := decidableFollows (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
        (Fin.tail k) (fun n => T (n + 1)) (lam 0 (γ 0 (x + k 0)))
      inferInstanceAs (Decidable (_ ∧ _))

def trailKeyCount (lam : Nat → X ≃+ X) (γ : Nat → X → X)
    (r : Nat) (T : Nat → X) (x : X) : Nat :=
  (Finset.univ.filter (fun k : Fin r → X => Follows lam γ r k T x)).card

/-- Round independence is encoded by counting all key vectors, not assumed as a product. -/
theorem trailKeyCount_eq_prod (lam : Nat → X ≃+ X) (γ : Nat → X → X) (r : Nat) :
    ∀ (T : Nat → X) (x : X), trailKeyCount lam γ r T x =
      ∏ n ∈ Finset.range r, diffCount (γ n) (T n) ((lam n).symm (T (n + 1))) := by
  induction r generalizing lam γ with
  | zero => intro T x; simp [trailKeyCount, Follows]
  | succ r ih =>
    intro T x
    rw [trailKeyCount, card_filter_cons, Finset.prod_range_succ']
    have hstep : ∀ k₀ : X,
        (Finset.univ.filter
          (fun k : Fin r → X => Follows lam γ (r + 1) (Fin.cons k₀ k) T x)).card =
        if lam 0 (γ 0 (x + T 0 + k₀)) - lam 0 (γ 0 (x + k₀)) = T 1 then
          ∏ n ∈ Finset.range r,
            diffCount (γ (n + 1)) (T (n + 1)) ((lam (n + 1)).symm (T (n + 1 + 1)))
        else 0 := by
      intro k₀
      have hunfold : ∀ k : Fin r → X, Follows lam γ (r + 1) (Fin.cons k₀ k) T x ↔
          (lam 0 (γ 0 (x + T 0 + k₀)) - lam 0 (γ 0 (x + k₀)) = T 1 ∧
          Follows (fun n => lam (n + 1)) (fun n => γ (n + 1)) r k
            (fun n => T (n + 1)) (lam 0 (γ 0 (x + k₀)))) := by
        intro k; simp [Follows]
      by_cases hC : lam 0 (γ 0 (x + T 0 + k₀)) - lam 0 (γ 0 (x + k₀)) = T 1
      · rw [if_pos hC, ← ih (fun n => lam (n + 1)) (fun n => γ (n + 1))
          (fun n => T (n + 1)) (lam 0 (γ 0 (x + k₀))), trailKeyCount]
        exact congrArg Finset.card (Finset.filter_congr (fun k _ => by simp [hunfold k, hC]))
      · rw [if_neg hC, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun k _ h => hC ((hunfold k).mp h).1
    have hfirst : (Finset.univ.filter
          (fun k₀ : X => lam 0 (γ 0 (x + T 0 + k₀)) - lam 0 (γ 0 (x + k₀)) = T 1)).card
        = diffCount (γ 0) (T 0) ((lam 0).symm (T 1)) := by
      refine Finset.card_equiv
        ⟨fun k₀ => x + k₀, fun y => y - x, fun k₀ => by simp, fun y => by simp⟩ (fun k₀ => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_fn_mk, mem_diffSet]
      have hcomm : x + k₀ + T 0 = x + T 0 + k₀ := by abel
      rw [hcomm, ← map_sub (lam 0)]
      exact ⟨fun h => by rw [← h, (lam 0).symm_apply_apply],
        fun h => by rw [h, (lam 0).apply_symm_apply]⟩
    rw [Finset.sum_congr rfl (fun k₀ _ => hstep k₀), ← Finset.sum_filter,
      Finset.sum_const, smul_eq_mul, hfirst, Nat.mul_comm]

/-- Constant schedules recover the existing count, not merely the same bound. -/
theorem uniform_specialization (lam : X ≃+ X) (γ : X → X) (r : Nat)
    (T : Nat → X) (x : X) :
    trailKeyCount (fun _ => lam) (fun _ => γ) r T x = _root_.trailKeyCount lam γ r T x := by
  rw [trailKeyCount_eq_prod, _root_.trailKeyCount_eq_prod]

end Scheduled
