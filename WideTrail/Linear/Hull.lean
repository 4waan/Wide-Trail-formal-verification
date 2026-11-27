/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Trail

/-!
# The linear hull in the independent-key model

For the keyed cipher `Scheduled.run lam γ r k` of `Trail.lean`, in the binary case (a pairing
`P` into `ZMod 2` and the sign character `sign₂`),

`elpCount P lam γ r u v = ∑_{k : Fin r → X} |walsh (run lam γ r k) u v| ^ 2`,

a natural number (as the differential counts are). Divided by `|X| ^ r · |X| ^ 2` it is the
expected linear probability of the masks `(u, v)`: the squared correlation averaged over an
additional independent uniform key per round. Fixed round constants belong to `γ n`; only the
additional keys are averaged over. Apart from `elpCount_one` and `run_injective`, the results
below assume that `P` is separating for `sign₂`, which forces `x + x = 0` on the states
(`Pairing.Separating.add_self_eq_zero`).

## Results

* `sum_sq_sum_sign`, `sum_sq_sum_walsh_run`: **averaging over a key removes the cross terms.**
  `∑_k (∑_c a c · walsh (run r k) c w) ^ 2 = ∑_c a c ^ 2 · elpCount r c w` for every `r` and all
  weights `a`. For `r ≥ 1` the first key multiplies the Walsh value at `c` by `(-1) ^ ⟨c, k 0⟩`;
  for `r = 0` there is no key, and the identity holds because
  `elpCount 0 c w = |X| ^ 2 · [c = w]` (`elpCount_zero`).
* `elpCount_succ`, `elpCount_add`: **Markov composition.**
  `elpCount (r₁ + r₂) u w · |X| ^ 2 = ∑_v elpCount r₁ u v · elpCount' r₂ v w`, with `elpCount'`
  the count of the last `r₂` rounds. The case `r₂ = 0` is covered by `elpCount_zero`. No
  adjoint and no hypothesis on the maps `γ n` is needed.
* `elpCount_one`, `elpCount_two`: with adjoints `lamT n` of the linear layers,
  `elpCount 1 u v = |X| · walsh (γ 0) u (lamT 0 v) ^ 2` and
  `elpCount 2 u v = ∑_c walsh (γ 0) u (lamT 0 c) ^ 2 · walsh (γ 1) c (lamT 1 v) ^ 2`.
* `elpCount_succ_eq_sum_trails`: **Nyberg's identity.**
  `elpCount (r + 1) u v · |X| ^ (2 r) = |X| ^ (r + 1) · ∑_d trailCorr (throughTrail u d v) ^ 2`:
  the key-averaged squared correlation is the sum of the squared correlations of all trails from
  `u` to `v`. The signs of the fixed-key expansion `walsh_run_eq_sum_trails` average out.
* `sum_elpCount_left`, `sum_elpCount_right`, `elpCount_zero_right`: the columns of the count
  sum to `|X| ^ (r + 2)` for every map; the rows do when the first `r` maps `γ n` are
  injective; a nonzero input mask never reaches the zero output mask.
* `elpCount_window_bound`: a bound `elpCount · Q ≤ V` on a window of `w` rounds at every nonzero
  input mask gives `elpCount (j + w + m) u v · Q ≤ V · |X| ^ (j + m)` for `u ≠ 0`, when the
  first `j` maps are injective. The rounds after the window need no hypothesis.
* `elpCount_two_round_bound_of_eq`, `elpCount_two_round_bound`: **the two-round bound.** Let
  rounds `0` and `1` be bricklayer layers of bijective S-boxes with linearity bound `c` under a
  separating bundle pairing, with adjoints `lamT n`, and let the backward map `lamT 0` have
  branch number at least `B`. Then for `u ≠ 0` and every `v`,
  `elpCount 2 u v · |K| ^ (2 (B - 1)) ≤ c ^ (2 (B - 1)) · |Idx → K| ^ 4`: the expected linear
  probability is at most `(c / |K|) ^ (2 (B - 1))`. The proof is `elpCount_two` and
  `Scheduled.sum_prod_le_of_weight`, used unchanged, with `Φ = Scheduled.codeword (lamT 0)`,
  the weights `walsh (s 1 i) (·) (β i) ^ 2` and `walsh (s 0 i) (u i) (·) ^ 2` (`β = lamT 1 v`),
  the per-position bound `c ^ 2` and the per-position sum `|K| ^ 2` (Parseval).
* `elpCount_bound_of_two_rounds`: the same ratio over `R` rounds, when the first `j` maps are
  injective and rounds `j` and `j + 1 ≤ R - 1` satisfy the two-round hypotheses:
  `elpCount R u v · |K| ^ (2 (B - 1)) ≤ c ^ (2 (B - 1)) · |Idx → K| ^ (R + 2)`.

These are the linear twins of the results of `Differential/Hull.lean`.

## What is not claimed

Every count here is over additional independent uniform keys. Nothing is said about the
cipher's correlation for one fixed key, a key schedule or fixed round constants:
`Checks/Toy.lean` gives a fixed key under which the squared correlation is four times the
key-averaged bound. Only two rounds are charged; the other rounds enter only through
injectivity (before the window) or not at all (after it). Nothing is said about `u = 0`. The
bound `(c / |K|) ^ (2 (B - 1))` is not claimed to be close to the true maximum for any instance.
-/

set_option autoImplicit false

namespace Linear

variable {X : Type*} [AddCommGroup X] [Fintype X]

/-! ### The count -/

/-- The **key-averaged squared correlation**, unnormalised: the sum over all key vectors
`k : Fin r → X` of the squared Walsh value of `r` keyed rounds at the masks `(u, v)`. Divided by
`|X| ^ r · |X| ^ 2` it is the expected linear probability of `(u, v)`: the squared correlation
averaged over an additional independent uniform key per round. -/
def elpCount (P : Pairing X (ZMod 2)) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ) (u v : X) :
    ℕ :=
  ∑ k : Fin r → X, (walsh sign₂ P P (Scheduled.run lam γ r k) u v).natAbs ^ 2

/-- `elpCount` read in `ℤ`: the sum of the squared Walsh values. -/
theorem elpCount_cast (P : Pairing X (ZMod 2)) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (u v : X) :
    (elpCount P lam γ r u v : ℤ)
      = ∑ k : Fin r → X, walsh sign₂ P P (Scheduled.run lam γ r k) u v ^ 2 := by
  rw [elpCount, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_pow, Int.natAbs_sq]

omit [AddCommGroup X] in
/-- Splitting a sum over `Fin (r + 1) → X` by the first coordinate. -/
theorem sum_fin_cons {M : Type*} [AddCommMonoid M] (r : ℕ)
    (f : (Fin (r + 1) → X) → M) :
    ∑ k, f k = ∑ k₀ : X, ∑ k : Fin r → X, f (Fin.cons k₀ k) := by
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => X)).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ### Key averaging -/

section Averaging

variable {P : Pairing X (ZMod 2)}

omit [Fintype X] in
/-- A `ZMod 2`-valued separating pairing forces every state to have order at most `2`. -/
theorem Pairing.Separating.add_self_eq_zero (hP : P.Separating sign₂) (x : X) : x + x = 0 :=
  hP.eq_zero_of_dot_right fun u => by
    rw [map_add]
    generalize P.dot u x = a
    revert a
    decide

/-- **One key kills the cross terms.** For a separating pairing and any weights `f`,
`∑_k (∑_c f c · (-1) ^ ⟨c, k⟩) ^ 2 = |X| · ∑_c f c ^ 2`. -/
theorem sum_sq_sum_sign (hP : P.Separating sign₂) (f : X → ℤ) :
    ∑ k : X, (∑ c, f c * sign₂ (P.dot c k)) ^ 2 = Fintype.card X * ∑ c, f c ^ 2 := by
  classical
  have hterm : ∀ c c' : X, ∑ k : X, f c * sign₂ (P.dot c k) * (f c' * sign₂ (P.dot c' k))
      = if c = c' then (Fintype.card X : ℤ) * f c ^ 2 else 0 := by
    intro c c'
    have hk : ∀ k, f c * sign₂ (P.dot c k) * (f c' * sign₂ (P.dot c' k))
        = f c * f c' * sign₂ (P.dot (c + c') k) := fun k => by
      rw [map_add, AddMonoidHom.add_apply, AddChar.map_add_eq_mul]
      ring
    simp_rw [hk, ← Finset.mul_sum, sum_char_dot_left hP]
    by_cases h : c = c'
    · subst h
      rw [if_pos (hP.add_self_eq_zero c), if_pos rfl]
      ring
    · have hne : c + c' ≠ 0 := fun h0 => h (by
        have h2 := hP.add_self_eq_zero c
        exact add_left_cancel (h2.trans h0.symm))
      rw [if_neg hne, if_neg h, mul_zero]
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  simp_rw [fun c => Finset.sum_comm (s := (Finset.univ : Finset X)) (t := Finset.univ)
    (f := fun k c' => f c * sign₂ (P.dot c k) * (f c' * sign₂ (P.dot c' k))), hterm,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, sq]

/-- After zero rounds the count is that of the identity: `|X| ^ 2` if `u = v`, else `0`. -/
theorem elpCount_zero [DecidableEq X] (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (u v : X) : elpCount P lam γ 0 u v = if u = v then Fintype.card X ^ 2 else 0 := by
  rw [elpCount, Fintype.sum_unique, walsh_run_zero hP]
  split_ifs <;> simp

/-- **Averaging over the keys of `r` rounds kills the cross terms.** For a separating pairing,
every `r` and all weights `a`,
`∑_k (∑_c a c · walsh (run lam γ r k) c w) ^ 2 = ∑_c a c ^ 2 · elpCount P lam γ r c w`.
For `r ≥ 1` the first key of the `r` rounds multiplies the Walsh value at the input mask `c` by
the phase `(-1) ^ ⟨c, k 0⟩`, and `sum_sq_sum_sign` removes the cross terms. For `r = 0` there is
no key; the identity holds because the Walsh value of the identity is `|X| · [c = w]`
(`elpCount_zero`). -/
theorem sum_sq_sum_walsh_run (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (r : ℕ) (a : X → ℤ) (w : X) :
    ∑ k : Fin r → X, (∑ c, a c * walsh sign₂ P P (Scheduled.run lam γ r k) c w) ^ 2
      = ∑ c, a c ^ 2 * (elpCount P lam γ r c w : ℤ) := by
  classical
  cases r with
  | zero =>
    simp_rw [walsh_run_zero hP, elpCount_zero hP, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fintype.sum_unique]
    push_cast
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    ring
  | succ r =>
    let H : (Fin r → X) → X → ℤ := fun k c => walsh sign₂ P P (fun x =>
      Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r k (lam 0 (γ 0 x))) c w
    have hW : ∀ (k₀ : X) (k : Fin r → X) (c : X),
        walsh sign₂ P P (Scheduled.run lam γ (r + 1) (Fin.cons k₀ k)) c w
          = sign₂ (P.dot c k₀) * H k c := fun k₀ k c => by
      rw [walsh_run_succ_eq_phase, Fin.cons_zero, Fin.tail_cons]
    have hR : ∀ c, (elpCount P lam γ (r + 1) c w : ℤ) = Fintype.card X * ∑ k, H k c ^ 2 := by
      intro c
      rw [elpCount_cast, sum_fin_cons, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsq : ∀ k₀ : X, walsh sign₂ P P (Scheduled.run lam γ (r + 1) (Fin.cons k₀ k)) c w ^ 2
          = H k c ^ 2 := fun k₀ => by
        rw [hW, mul_pow, sq (sign₂ _), sign₂_mul_self, one_mul]
      rw [Finset.sum_congr rfl fun k₀ _ => hsq k₀, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [sum_fin_cons, Finset.sum_comm]
    simp_rw [hW, hR]
    have hk : ∀ k : Fin r → X, ∑ k₀ : X, (∑ c, a c * (sign₂ (P.dot c k₀) * H k c)) ^ 2
        = Fintype.card X * ∑ c, (a c * H k c) ^ 2 := fun k => by
      rw [← sum_sq_sum_sign hP]
      refine Finset.sum_congr rfl fun k₀ _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    simp_rw [hk, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k _ => ?_
    ring

end Averaging

/-! ### Composition -/

section Composition

variable {P : Pairing X (ZMod 2)}

omit [Fintype X] in
/-- `Scheduled.run` over a key vector `Fin.cons k₀ k`: the first round with key `k₀`, then the
remaining rounds with the keys `k`. -/
theorem run_succ_cons (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ) (k₀ : X) (k : Fin r → X)
    (x : X) :
    Scheduled.run lam γ (r + 1) (Fin.cons k₀ k) x
      = Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r k (lam 0 (γ 0 (x + k₀))) := by
  change Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
    (Fin.tail (Fin.cons k₀ k : Fin (r + 1) → X))
    (lam 0 (γ 0 (x + (Fin.cons k₀ k : Fin (r + 1) → X) 0))) = _
  rw [Fin.tail_cons, Fin.cons_zero]

/-- `elpCount` over one round, as a sum over the round key. -/
theorem elpCount_one_cast (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (u v : X) :
    (elpCount P lam γ 1 u v : ℤ)
      = ∑ k₀ : X, walsh sign₂ P P (fun x => lam 0 (γ 0 (x + k₀))) u v ^ 2 := by
  rw [elpCount_cast, sum_fin_cons]
  refine Finset.sum_congr rfl fun k₀ _ => ?_
  rw [Fintype.sum_unique]
  congr 2

/-- **One round, then the rest (Markov composition at `r₁ = 1`).** For a separating pairing,
`elpCount (r + 1) u w · |X| ^ 2 = ∑_c elpCount 1 u c · elpCount' r c w`, where `elpCount'` is
the count of the last `r` rounds. Every map `γ n` is allowed. -/
theorem elpCount_succ (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (u w : X) :
    elpCount P lam γ (r + 1) u w * Fintype.card X ^ 2
      = ∑ c, elpCount P lam γ 1 u c
          * elpCount P (fun n => lam (n + 1)) (fun n => γ (n + 1)) r c w := by
  have key : ∀ (k₀ : X) (k : Fin r → X),
      walsh sign₂ P P (Scheduled.run lam γ (r + 1) (Fin.cons k₀ k)) u w ^ 2
          * (Fintype.card X : ℤ) ^ 2
        = (∑ c, walsh sign₂ P P (fun x => lam 0 (γ 0 (x + k₀))) u c
            * walsh sign₂ P P (Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r k)
                c w) ^ 2 := by
    intro k₀ k
    have h := walsh_comp (P := P) P hP (fun x => lam 0 (γ 0 (x + k₀)))
      (Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r k) u w
    rw [← h]
    have hrun : Scheduled.run lam γ (r + 1) (Fin.cons k₀ k) = fun x =>
        Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r k (lam 0 (γ 0 (x + k₀))) :=
      funext (run_succ_cons lam γ r k₀ k)
    rw [hrun]
    ring
  have hZ : ((elpCount P lam γ (r + 1) u w * Fintype.card X ^ 2 : ℕ) : ℤ)
      = ((∑ c, elpCount P lam γ 1 u c
          * elpCount P (fun n => lam (n + 1)) (fun n => γ (n + 1)) r c w : ℕ) : ℤ) := by
    push_cast
    rw [elpCount_cast, Finset.sum_mul, sum_fin_cons]
    simp_rw [key, sum_sq_sum_walsh_run hP]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [elpCount_one_cast, Finset.sum_mul]
  exact_mod_cast hZ

/-- **Markov composition.** For a separating pairing and every pair of block lengths,
`elpCount (r₁ + r₂) u w · |X| ^ 2 = ∑_v elpCount r₁ u v · elpCount' r₂ v w`, where `elpCount'`
is the count of the last `r₂` rounds. The cross terms between different middle masks `v` vanish
on averaging over the first key of the second block. When `r₂ = 0` the second block has no key,
and the identity holds because `elpCount 0 v w = |X| ^ 2 · [v = w]` (`elpCount_zero`). Every map
`γ n` is allowed. -/
theorem elpCount_add (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (r₁ r₂ : ℕ) (u w : X) :
    elpCount P lam γ (r₁ + r₂) u w * Fintype.card X ^ 2
      = ∑ v, elpCount P lam γ r₁ u v
          * elpCount P (fun n => lam (n + r₁)) (fun n => γ (n + r₁)) r₂ v w := by
  classical
  induction r₁ generalizing lam γ u with
  | zero =>
    simp only [Nat.zero_add, elpCount_zero hP, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Nat.add_zero]
    exact mul_comm _ _
  | succ r ih =>
    have hX : 0 < Fintype.card X ^ 2 := pow_pos Fintype.card_pos 2
    rw [show r + 1 + r₂ = (r + r₂) + 1 by omega]
    refine Nat.eq_of_mul_eq_mul_right hX ?_
    rw [elpCount_succ hP lam γ (r + r₂) u w, Finset.sum_mul, Finset.sum_mul]
    simp_rw [mul_assoc, ih (fun n => lam (n + 1)) (fun n => γ (n + 1)), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    change _ = elpCount P lam γ (r + 1) u v
      * (elpCount P (fun n => lam (n + r + 1)) (fun n => γ (n + r + 1)) r₂ v w
        * Fintype.card X ^ 2)
    rw [mul_comm (elpCount P (fun n => lam (n + r + 1)) _ r₂ v w), ← mul_assoc,
      elpCount_succ hP lam γ r u v, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring

end Composition

/-! ### Trails: Nyberg's identity -/

section Trails

variable {P : Pairing X (ZMod 2)}

/-- **One round.** For a separating pairing and an adjoint `lamT 0` of `lam 0`,
`elpCount 1 u v = |X| · walsh (γ 0) u (lamT 0 v) ^ 2`: the key changes only the sign. -/
theorem elpCount_one (lam : ℕ → X ≃+ X) (lamT : ℕ → X → X)
    (hadj : ∀ n, IsAdjoint P P (lam n) (lamT n)) (γ : ℕ → X → X) (u v : X) :
    elpCount P lam γ 1 u v = Fintype.card X * (walsh sign₂ P P (γ 0) u (lamT 0 v)).natAbs ^ 2 := by
  have h : (elpCount P lam γ 1 u v : ℤ)
      = Fintype.card X * (walsh sign₂ P P (γ 0) u (lamT 0 v)).natAbs ^ 2 := by
    rw [elpCount_one_cast, Int.natAbs_sq]
    have hk : ∀ k₀ : X, walsh sign₂ P P (fun x => lam 0 (γ 0 (x + k₀))) u v ^ 2
        = walsh sign₂ P P (γ 0) u (lamT 0 v) ^ 2 := fun k₀ => by
      rw [walsh_keyedRound sign₂ P (hadj 0) (γ 0) k₀ u v, mul_pow, sq (sign₂ _),
        sign₂_mul_self, one_mul]
    rw [Finset.sum_congr rfl fun k₀ _ => hk k₀, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  exact_mod_cast h

/-- **Two rounds as a sum over the middle mask.** For a separating pairing and adjoints `lamT n`,
`elpCount 2 u v = ∑_c walsh (γ 0) u (lamT 0 c) ^ 2 · walsh (γ 1) c (lamT 1 v) ^ 2`: the sum of
the squared correlations of the two-round trails `u → c → v`. -/
theorem elpCount_two (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (lamT : ℕ → X → X)
    (hadj : ∀ n, IsAdjoint P P (lam n) (lamT n)) (γ : ℕ → X → X) (u v : X) :
    elpCount P lam γ 2 u v = ∑ c, (walsh sign₂ P P (γ 0) u (lamT 0 c)).natAbs ^ 2
        * (walsh sign₂ P P (γ 1) c (lamT 1 v)).natAbs ^ 2 := by
  have h := elpCount_succ hP lam γ 1 u v
  simp_rw [elpCount_one lam lamT hadj γ, elpCount_one (fun n => lam (n + 1))
    (fun n => lamT (n + 1)) (fun n => hadj (n + 1)) (fun n => γ (n + 1))] at h
  refine Nat.eq_of_mul_eq_mul_right (pow_pos Fintype.card_pos 2) (h.trans ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **Nyberg's identity: the linear hull in the independent-key model.** For a separating
pairing and adjoints `lamT n` of the linear layers,

`elpCount (r + 1) u v · |X| ^ (2 r) = |X| ^ (r + 1) · ∑_d trailCorr (throughTrail u d v) ^ 2`.

Divided by `|X| ^ (r + 1) · |X| ^ 2 · |X| ^ (2 r)`, the left side is the squared correlation of
`(u, v)` averaged over an additional independent uniform key per round, and the right side is
the sum, over all trails from `u` to `v`, of the trails' squared correlations. The key-dependent
signs of the fixed-key expansion (`walsh_run_eq_sum_trails`) average out. -/
theorem elpCount_succ_eq_sum_trails (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X)
    (lamT : ℕ → X → X) (hadj : ∀ n, IsAdjoint P P (lam n) (lamT n)) (γ : ℕ → X → X) (r : ℕ)
    (u v : X) :
    elpCount P lam γ (r + 1) u v * Fintype.card X ^ (2 * r)
      = Fintype.card X ^ (r + 1) * ∑ d : Fin r → X,
          (trailCorr sign₂ P lamT γ (r + 1) (Scheduled.throughTrail u d v)).natAbs ^ 2 := by
  induction r generalizing lam lamT γ u with
  | zero =>
    rw [elpCount_one lam lamT hadj γ u v, Fintype.sum_unique, trailCorr_succ, trailCorr_zero,
      mul_one]
    simp [Scheduled.throughTrail]
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 + 2 * r by ring, pow_add, ← mul_assoc,
      elpCount_succ hP lam γ (r + 1) u v, Finset.sum_mul, sum_fin_cons, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [elpCount_one lam lamT hadj γ u c, mul_assoc,
      ih (fun n => lam (n + 1)) (fun n => lamT (n + 1)) (fun n => hadj (n + 1))
        (fun n => γ (n + 1)) c]
    simp_rw [trailCorr_throughTrail_cons, Int.natAbs_mul, mul_pow]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring

end Trails

/-! ### Rows, columns and the zero mask -/

section Parseval

variable {P : Pairing X (ZMod 2)}

omit [Fintype X] in
/-- Injective rounds give an injective run, for every key vector. -/
theorem run_injective (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (hγ : ∀ n < r, Function.Injective (γ n)) (k : Fin r → X) :
    Function.Injective (Scheduled.run lam γ r k) := by
  induction r generalizing lam γ with
  | zero => exact fun x y h => h
  | succ r ih =>
    exact (ih (fun n => lam (n + 1)) (fun n => γ (n + 1)) (fun n hn => hγ (n + 1) (by omega))
      (Fin.tail k)).comp ((lam 0).injective.comp
        ((hγ 0 (by omega)).comp (add_left_injective (k 0))))

/-- The squared Walsh values of a column sum to `|X| ^ 2`, in `ℕ`. -/
theorem sum_natAbs_walsh_sq_left {Y : Type*} [AddCommGroup Y] {Q : Pairing Y (ZMod 2)}
    (hP : P.Separating sign₂) (F : X → Y) (v : Y) :
    ∑ u, (walsh sign₂ P Q F u v).natAbs ^ 2 = Fintype.card X ^ 2 := by
  have h := sum_walsh_sq_left (Q := Q) hP F v
  have h' : ((∑ u, (walsh sign₂ P Q F u v).natAbs ^ 2 : ℕ) : ℤ)
      = ((Fintype.card X ^ 2 : ℕ) : ℤ) := by
    push_cast
    simp_rw [sq_abs]
    exact h
  exact_mod_cast h'

/-- The squared Walsh values of a row of an injective map sum to `|X| · |Y|`, in `ℕ`. -/
theorem sum_natAbs_walsh_sq_right {Y : Type*} [AddCommGroup Y] [Fintype Y]
    {Q : Pairing Y (ZMod 2)} (hQ : Q.Separating sign₂) {F : X → Y} (hF : Function.Injective F)
    (u : X) : ∑ v, (walsh sign₂ P Q F u v).natAbs ^ 2 = Fintype.card X * Fintype.card Y := by
  have h := sum_walsh_sq_right (P := P) hQ hF u
  have h' : ((∑ v, (walsh sign₂ P Q F u v).natAbs ^ 2 : ℕ) : ℤ)
      = ((Fintype.card X * Fintype.card Y : ℕ) : ℤ) := by
    push_cast
    simp_rw [sq_abs]
    exact h
  exact_mod_cast h'

/-- **Columns sum to `|X| ^ (r + 2)`**, for every map: `∑_u elpCount r u v = |X| ^ r · |X| ^ 2`.
Divided by `|X| ^ r · |X| ^ 2`, the expected linear probabilities into `v` sum to `1`. -/
theorem sum_elpCount_left (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (r : ℕ) (v : X) : ∑ u, elpCount P lam γ r u v = Fintype.card X ^ (r + 2) := by
  simp_rw [elpCount]
  rw [Finset.sum_comm]
  simp_rw [sum_natAbs_walsh_sq_left hP]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
    pow_add]

/-- **Rows sum to `|X| ^ (r + 2)` when the rounds are injective**: if `γ n` is injective for
every `n < r`, then `∑_v elpCount r u v = |X| ^ r · |X| ^ 2`. -/
theorem sum_elpCount_right (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (r : ℕ) (hγ : ∀ n < r, Function.Injective (γ n)) (u : X) :
    ∑ v, elpCount P lam γ r u v = Fintype.card X ^ (r + 2) := by
  simp_rw [elpCount]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ =>
    sum_natAbs_walsh_sq_right (P := P) hP (run_injective lam γ r hγ k) u]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
    pow_add, sq]

/-- **A nonzero mask never reaches the zero mask**, for every map:
`elpCount r u 0 = 0` for `u ≠ 0`. -/
theorem elpCount_zero_right (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (r : ℕ) {u : X} (hu : u ≠ 0) : elpCount P lam γ r u 0 = 0 :=
  Finset.sum_eq_zero fun k _ => by rw [walsh_zero_right hP _ hu]; rfl

/-- **A window bound carries over to the schedule.** Suppose that the first `j` maps `γ n` are
injective and that the `w` rounds starting at round `j` satisfy `elpCount · Q ≤ V` at every
nonzero input mask. Then for `u ≠ 0`, `elpCount (j + w + m) u v · Q ≤ V · |X| ^ (j + m)`. The
first `j` rounds keep the mask nonzero (`elpCount_zero_right`) and their rows sum to
`|X| ^ (j + 2)` (`sum_elpCount_right`); the columns of the last `m` rounds sum to `|X| ^ (m + 2)`
for every map (`sum_elpCount_left`), so those rounds need no hypothesis. -/
theorem elpCount_window_bound (hP : P.Separating sign₂) (lam : ℕ → X ≃+ X) (γ : ℕ → X → X)
    (j w m : ℕ) (hpre : ∀ n < j, Function.Injective (γ n)) {Q V : ℕ}
    (hwin : ∀ c : X, c ≠ 0 → ∀ e : X,
      elpCount P (fun n => lam (n + j)) (fun n => γ (n + j)) w c e * Q ≤ V)
    {u : X} (hu : u ≠ 0) (v : X) :
    elpCount P lam γ (j + w + m) u v * Q ≤ V * Fintype.card X ^ (j + m) := by
  set N := Fintype.card X with hNdef
  have hN : 0 < N ^ 2 * N ^ 2 :=
    Nat.mul_pos (pow_pos Fintype.card_pos 2) (pow_pos Fintype.card_pos 2)
  refine Nat.le_of_mul_le_mul_right ?_ hN
  have hA := elpCount_add hP lam γ j (w + m) u v
  have hB : ∀ c, elpCount P (fun n => lam (n + j)) (fun n => γ (n + j)) (w + m) c v * N ^ 2
      = ∑ e, elpCount P (fun n => lam (n + j)) (fun n => γ (n + j)) w c e
          * elpCount P (fun n => lam (n + w + j)) (fun n => γ (n + w + j)) m e v :=
    fun c => elpCount_add hP _ _ w m c v
  have hcol := sum_elpCount_left hP (fun n => lam (n + w + j)) (fun n => γ (n + w + j)) m v
  have hrow := sum_elpCount_right hP lam γ j hpre u
  calc elpCount P lam γ (j + w + m) u v * Q * (N ^ 2 * N ^ 2)
      = elpCount P lam γ (j + (w + m)) u v * N ^ 2 * (N ^ 2 * Q) := by
        rw [Nat.add_assoc]; ring
    _ = ∑ c, elpCount P lam γ j u c
          * ((elpCount P (fun n => lam (n + j)) (fun n => γ (n + j)) (w + m) c v * N ^ 2) * Q) := by
        rw [hA, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ ≤ ∑ c, elpCount P lam γ j u c * (V * N ^ (m + 2)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        by_cases hc : c = 0
        · rw [hc, elpCount_zero_right hP lam γ j hu, zero_mul, zero_mul]
        · refine Nat.mul_le_mul_left _ ?_
          rw [hB c, Finset.sum_mul, ← hcol, Finset.mul_sum]
          refine Finset.sum_le_sum fun e _ => ?_
          rw [mul_right_comm]
          exact Nat.mul_le_mul_right _ (hwin c hc e)
    _ = V * N ^ (j + m) * (N ^ 2 * N ^ 2) := by
        rw [← Finset.sum_mul, hrow]
        ring

end Parseval

/-! ### Two bricklayer rounds -/

section TwoRounds

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [AddCommGroup K] [Fintype K]
  [DecidableEq K] {P : Pairing K (ZMod 2)}

/-- The squared absolute value of a product of integers is the product of the squared absolute
values: `(∏ᵢ fᵢ).natAbs ^ 2 = ∏ᵢ (fᵢ.natAbs) ^ 2`. -/
theorem natAbs_prod_sq {ι : Type*} [Fintype ι] (f : ι → ℤ) :
    (∏ i, f i).natAbs ^ 2 = ∏ i, (f i).natAbs ^ 2 := by
  rw [show (∏ i, f i).natAbs = ∏ i, (f i).natAbs from map_prod Int.natAbsHom f _,
    Finset.prod_pow]

/-- **The two-round linear hull bound.** Let rounds `0` and `1` be bricklayer layers
`γ n = bricklayer (s n)` of bijective S-boxes with linearity bound `c`, under a separating
bundle pairing, let `lamT n` be adjoints of the linear layers, and let the backward map `lamT 0`
have branch number at least `B`. Then for every nonzero input mask `u` and every output mask `v`,
`elpCount 2 u v · |K| ^ (2 (B - 1)) ≤ c ^ (2 (B - 1)) · |Idx → K| ^ 4`: the squared correlation
of `(u, v)`, averaged over an additional independent uniform key per round, is at most
`(c / |K|) ^ (2 (B - 1))`.

This bounds the hull, the sum over all two-round trails from `u` to `v`, in the independent-key
model. It says nothing about one fixed key or about fixed round constants. -/
theorem elpCount_two_round_bound_of_eq (hP : P.Separating sign₂)
    (lam : ℕ → (Idx → K) ≃+ (Idx → K)) (lamT : ℕ → (Idx → K) → (Idx → K))
    (hadj : ∀ n, IsAdjoint P.pi P.pi (lam n) (lamT n)) (γ : ℕ → (Idx → K) → (Idx → K))
    (s : ℕ → Idx → K → K) (hγ : ∀ n < 2, γ n = bricklayer (s n))
    (hs : ∀ n < 2, ∀ i, Function.Bijective (s n i)) {c B : ℕ}
    (hc : ∀ n < 2, ∀ i, IsLinearityBound P (s n i) c) (hB : isBranchBound id (lamT 0) B)
    {u : Idx → K} (hu : u ≠ 0) (v : Idx → K) :
    elpCount P.pi lam γ 2 u v * Fintype.card K ^ (2 * (B - 1))
      ≤ c ^ (2 * (B - 1)) * Fintype.card (Idx → K) ^ 4 := by
  have hPi : (P.pi (Idx := Idx)).Separating sign₂ := hP.pi
  set β := lamT 1 v with hβ
  let Φ : (Idx → K) →+ (Idx ⊕ Idx → K) :=
    Scheduled.codeword (AddMonoidHom.mk' (lamT 0) ((hadj 0).map_add hPi))
  have hΦ : ∀ x, Φ x = Sum.elim x (lamT 0 x) := fun x => rfl
  let g : Idx ⊕ Idx → K → ℕ :=
    Sum.elim (fun i a => (walsh sign₂ P P (s 1 i) a (β i)).natAbs ^ 2)
      (fun i b => (walsh sign₂ P P (s 0 i) (u i) b).natAbs ^ 2)
  have hsum : elpCount P.pi lam γ 2 u v = ∑ x : Idx → K, ∏ j, g j (Φ x j) := by
    rw [elpCount_two hPi lam lamT hadj γ u v]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hγ 0 (by norm_num), hγ 1 (by norm_num), walsh_bricklayer, walsh_bricklayer,
      natAbs_prod_sq, natAbs_prod_sq, Fintype.prod_sum_type, mul_comm]
    simp only [hΦ, Sum.elim_inl, Sum.elim_inr, g]
    rfl
  have hcard : Fintype.card (Idx → K) ^ 4
      = (Fintype.card K ^ 2) ^ Fintype.card (Idx ⊕ Idx) := by
    rw [Fintype.card_fun, Fintype.card_sum, ← pow_mul, ← pow_mul]
    ring_nf
  rw [hsum, hcard, pow_mul, pow_mul]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  refine Scheduled.sum_prod_le_of_weight Φ ?_ ?_ g
    ((activePattern β).disjSum (activePattern u)) ⟨Sum.inr i₀, ?_⟩ ?_ ?_ ?_ ?_ ?_
  · intro x x' h
    funext i
    exact congrFun h (Sum.inl i)
  · intro x hx
    rw [hΦ, Scheduled.weight_sumElim]
    simpa [colWeight_id] using hB x hx
  · simpa using hi₀
  · rintro (i | i) hj a
    · simp only [Finset.inl_mem_disjSum, mem_activePattern] at hj
      by_cases ha : a = 0
      · simp [g, ha, walsh_zero_left hP (hs 1 (by norm_num) i) hj]
      · exact Nat.pow_le_pow_left (hc 1 (by norm_num) i a ha (β i)) 2
    · simp only [Finset.inr_mem_disjSum, mem_activePattern] at hj
      exact Nat.pow_le_pow_left (hc 0 (by norm_num) i (u i) hj a) 2
  · rintro (i | i) _
    · exact (sum_natAbs_walsh_sq_left hP (s 1 i) (β i)).le
    · exact ((sum_natAbs_walsh_sq_right hP (hs 0 (by norm_num) i).injective (u i)).trans
        (sq _).symm).le
  · rintro (i | i) hj
    · simp only [Finset.inl_mem_disjSum, mem_activePattern] at hj
      simp [g, walsh_zero_left hP (hs 1 (by norm_num) i) hj]
    · simp only [Finset.inr_mem_disjSum, mem_activePattern] at hj
      simp [g, walsh_zero_right hP (s 0 i) hj]
  · rintro (i | i) hj a ha
    · simp only [Finset.inl_mem_disjSum, mem_activePattern, not_not] at hj
      by_contra ha0
      exact ha (by simp [g, hj, walsh_zero_right hP (s 1 i) ha0])
    · simp only [Finset.inr_mem_disjSum, mem_activePattern, not_not] at hj
      by_contra ha0
      exact ha (by simp [g, hj, walsh_zero_left hP (hs 0 (by norm_num) i) ha0])
  · rintro (i | i) _
    · exact Nat.pow_le_pow_left (natAbs_walsh_le_card P P _ _ _) 2
    · exact Nat.pow_le_pow_left (natAbs_walsh_le_card P P _ _ _) 2

/-- `elpCount_two_round_bound_of_eq` for bricklayer S-box layers, `γ n = bricklayer (s n)`. -/
theorem elpCount_two_round_bound (hP : P.Separating sign₂)
    (lam : ℕ → (Idx → K) ≃+ (Idx → K)) (lamT : ℕ → (Idx → K) → (Idx → K))
    (hadj : ∀ n, IsAdjoint P.pi P.pi (lam n) (lamT n)) (s : ℕ → Idx → K → K)
    (hs : ∀ n < 2, ∀ i, Function.Bijective (s n i)) {c B : ℕ}
    (hc : ∀ n < 2, ∀ i, IsLinearityBound P (s n i) c) (hB : isBranchBound id (lamT 0) B)
    {u : Idx → K} (hu : u ≠ 0) (v : Idx → K) :
    elpCount P.pi lam (fun n => bricklayer (s n)) 2 u v * Fintype.card K ^ (2 * (B - 1))
      ≤ c ^ (2 * (B - 1)) * Fintype.card (Idx → K) ^ 4 :=
  elpCount_two_round_bound_of_eq hP lam lamT hadj _ s (fun _ _ => rfl) hs hc hB hu v

/-- **The two-round hull bound for a whole schedule.** If the first `j` maps `γ n` are injective
and rounds `j` and `j + 1 ≤ R - 1` satisfy the hypotheses of `elpCount_two_round_bound_of_eq`,
with `lamT j` of branch number at least `B`, then for `u ≠ 0`,
`elpCount R u v · |K| ^ (2 (B - 1)) ≤ c ^ (2 (B - 1)) · |Idx → K| ^ (R + 2)`. The other rounds
are not charged; the rounds after the window need no hypothesis. The same model: an additional
independent uniform key per round. -/
theorem elpCount_bound_of_two_rounds (hP : P.Separating sign₂)
    (lam : ℕ → (Idx → K) ≃+ (Idx → K)) (lamT : ℕ → (Idx → K) → (Idx → K))
    (hadj : ∀ n, IsAdjoint P.pi P.pi (lam n) (lamT n)) (γ : ℕ → (Idx → K) → (Idx → K))
    (s : ℕ → Idx → K → K) (R j : ℕ) (hj : j + 2 ≤ R)
    (hpre : ∀ n < j, Function.Injective (γ n))
    (hγ : ∀ n, j ≤ n → n < j + 2 → γ n = bricklayer (s n))
    (hs : ∀ n, j ≤ n → n < j + 2 → ∀ i, Function.Bijective (s n i)) {c B : ℕ}
    (hc : ∀ n, j ≤ n → n < j + 2 → ∀ i, IsLinearityBound P (s n i) c)
    (hB : isBranchBound id (lamT j) B) {u : Idx → K} (hu : u ≠ 0) (v : Idx → K) :
    elpCount P.pi lam γ R u v * Fintype.card K ^ (2 * (B - 1))
      ≤ c ^ (2 * (B - 1)) * Fintype.card (Idx → K) ^ (R + 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h := elpCount_window_bound hP.pi lam γ j 2 m hpre
    (fun x hx e => elpCount_two_round_bound_of_eq hP (fun n => lam (n + j))
      (fun n => lamT (n + j)) (fun n => hadj (n + j)) (fun n => γ (n + j)) (fun n => s (n + j))
      (fun n hn => hγ (n + j) (by omega) (by omega))
      (fun n hn => hs (n + j) (by omega) (by omega))
      (fun n hn => hc (n + j) (by omega) (by omega)) (by simpa using hB) hx e) hu v
  calc elpCount P.pi lam γ (j + 2 + m) u v * Fintype.card K ^ (2 * (B - 1))
      ≤ c ^ (2 * (B - 1)) * Fintype.card (Idx → K) ^ 4 * Fintype.card (Idx → K) ^ (j + m) := h
    _ = c ^ (2 * (B - 1)) * Fintype.card (Idx → K) ^ (j + 2 + m + 2) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega

end TwoRounds

end Linear
