/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Differential.Scheduled
import WideTrail.Differential.Bricklayer

/-!
# Differentials in the additional-independent-key model

`Markov.lean` and `Scheduled.lean` count the key vectors under which one input pair follows one
trail. A differential is an input difference `a` and an output difference `b` with every
intermediate difference allowed, so its count is a sum over all trails from `a` to `b`
(`diffCount_comp` for the composition of two fixed maps; `diffKeyCount_succ_eq_sum_trailKeyCount`
below for any positive number of keyed rounds). This file counts differentials in the same model
and bounds them over two bricklayer rounds.

## The model

Round `n` maps `z` to `lam n (γ n (z + k n))`, where `lam n` is an additive bijection, `γ n` is
any map, and `k n` is an additional key, independent and uniform for each round. `run lam γ r k`
is `r` such rounds under the key vector `k : Fin r → X`. `diffKeyCount lam γ r a b x` is the
number of key vectors `k` with `run lam γ r k (x + a) - run lam γ r k x = b`; divided by
`|X| ^ r` it is the probability of the differential `(a, b)` at the input `x`, averaged over the
keys. Fixed round constants belong to `γ n` (as in `Hades.roundGamma`); only the additional keys
are averaged over.

## Results

* `diffKeyCount_const`: the count does not depend on `x`.
* `diffKeyCount_succ`, `diffKeyCount_add`: over `r₁ + r₂` rounds the count is
  `∑ c, (count of the first r₁ rounds, a to c) * (count of the last r₂ rounds, c to b)`.
  `diffKeyCount_succ_eq_sum_trailKeyCount`: over `r + 1` rounds the count is the sum of
  `trailKeyCount` over all trails from `a` to `b`, one for each choice of the `r` intermediate
  differences (`throughTrail`); `diffKeyCount_two_eq_sum_trailKeyCount` is the two-round case.
* `sum_diffKeyCount`: every row sums to `|X| ^ r`. `sum_diffKeyCount_col`: every column sums to
  `|X| ^ r` when every `γ n` is bijective (from `sum_diffCount_col`). `diffKeyCount_eq_zero`:
  injective rounds never take `a ≠ 0` to `0`.
* `diffKeyCount_two_round_bound`: **the two-round bound.** Over `Idx → K`, let both rounds have
  bricklayer differential counts, `diffCount (γ n) a b = ∏ i, diffCount (s n i) (a i) (b i)`,
  with every S-box `s n i` bijective and of differential uniformity at most `u`, and let `lam 0`
  have branch number at least `B`. Then for `a ≠ 0` and every `b` and `x`,
  `diffKeyCount lam γ 2 a b x * |K| ^ (B - 1) ≤ u ^ (B - 1) * |Idx → K| ^ 2`: the key-averaged
  probability of every two-round differential with a nonzero input difference is at most
  `(u / |K|) ^ (B - 1)`. `bricklayer_two_round_bound` states it for `γ n = bricklayer (s n)`.
* `diffKeyCount_bound_of_two_rounds`: the same ratio for `R` rounds, when every round is
  bijective and rounds `j` and `j + 1` satisfy the hypotheses above. The other rounds are not
  charged. `diffKeyCount_window_bound` is the general form: a bound on every window of `w`
  rounds at a nonzero input difference carries over to the whole schedule.

## The proof of the two-round bound

The count is `∑ c, DC₀(a, c) * DC₁(lam 0 c, β)` with `β = (lam 1)⁻¹ b` (`diffKeyCount_two`),
and each factor is a product over coordinates. A nonzero term needs `supp c = supp a` and
`supp (lam 0 c) = supp β`. So `(c, lam 0 c)`, a state indexed by `Idx ⊕ Idx` (`codeword`), is
nonzero, has weight at least `B`, and is supported on `S`, the `weight a + weight β` positions
of `supp a` on the input side and `supp β` on the output side. Fix `B - 1` positions `D` of `S`.
Two such `c` that agree on `S \ D` differ by a codeword supported on `D`. For `B ≥ 1` its weight
is at most `B - 1 < B`, so it is `0`; for `B = 0` the set `D` is empty and the codeword is `0`
outright. Since `c ↦ (c, lam 0 c)` is injective, the two are equal. The factors on `D` are each
at most `u`. The factors on `S \ D` are summed over all values, by row sums on the input side and
column sums on the output side, which needs bijective S-boxes. Every factor outside `S` is
`diffCount (s n i) 0 0 = |K|`. The total is `u ^ (B - 1) * |K| ^ (2 |Idx| - (B - 1))`, and the
count is `0` if `S` has fewer than `B - 1` positions. `sum_prod_le_of_weight` is this argument for
any injective additive map whose nonzero values have weight at least `B`.

This bounds a differential, the sum over all trails, and not one trail. The Poseidon designers
(Grassi et al., ePrint 2019/458, the full version of the USENIX Security 2021 paper, Appendix
C.1.1) call the permutation secure against differential cryptanalysis when every differential
has probability at most `p ^ (-t)`, and, "since it is in general hard to compute the probability
of a differential", require instead that every characteristic have probability at most
`p ^ (-2t)`. The theorems here bound the differential itself, in the independent-key model, and
charge two full rounds only. They do not establish the criterion `p ^ (-t)` for any instance,
and nothing here concerns the other attacks that the designers' round margins cover. Bounds of
this kind for maximal and semi-maximal diffusion layers are studied by Hong et al. (FSE 2000) and
Kang et al. (ETRI Journal 23(4), 2001); the statement for a general branch number `B` is proved
here directly.

## What is not claimed

Every count here is over the additional independent uniform keys. Nothing is said about the
permutation with its fixed round constants or about any one key: `Checks/Hull.lean` gives a
two-round differential whose count over the inputs, with the keys fixed to zero, exceeds the
bound. Only two rounds are charged; the other rounds of a schedule enter only through
bijectivity. Nothing is said about a differential with `a = 0`.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

section Zero

variable {X Y : Type*} [Fintype X] [AddCommGroup X] [AddCommGroup Y] [DecidableEq Y]

/-- An injective map sends no input pair with a nonzero difference to a pair with difference
`0`: `diffCount F a 0 = 0` for `a ≠ 0`. -/
theorem diffCount_eq_zero_of_injective {F : X → Y} (hF : Function.Injective F) {a : X}
    (ha : a ≠ 0) : diffCount F a 0 = 0 := by
  rw [diffCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_diffSet, sub_eq_zero] at hx
  exact ha (by simpa using hF hx)

end Zero

namespace Scheduled

section Keyed

variable {X : Type*} [Fintype X] [DecidableEq X] [AddCommGroup X]

/-- `r` rounds under the key vector `k : Fin r → X`: round `n` maps `z` to
`lam n (γ n (z + k n))`. The first round is peeled off, as in `Follows`. -/
def run (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) : (r : ℕ) → (Fin r → X) → X → X
  | 0, _, x => x
  | r + 1, k, x =>
      run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r (Fin.tail k) (lam 0 (γ 0 (x + k 0)))

/-- The number of key vectors `k : Fin r → X` under which the input pair `(x, x + a)` has
output difference `b` after `r` rounds. Divided by `|X| ^ r` it is the probability of the
differential `(a, b)`, averaged over an additional independent uniform key per round. -/
def diffKeyCount (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ) (a b x : X) : ℕ :=
  (Finset.univ.filter (fun k : Fin r → X => run lam γ r k (x + a) - run lam γ r k x = b)).card

/-- After zero rounds the difference is the input difference. -/
theorem diffKeyCount_zero (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (a b x : X) :
    diffKeyCount lam γ 0 a b x = if a = b then 1 else 0 := by
  by_cases h : a = b <;> simp [diffKeyCount, run, h]

/-- Splitting the count by the first round key `k₀`: the rest is the count of the remaining
`r` rounds, at the difference and the input that the first round produces. -/
theorem diffKeyCount_succ_eq_sum_key (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (a b x : X) :
    diffKeyCount lam γ (r + 1) a b x = ∑ k₀ : X,
      diffKeyCount (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
        (lam 0 (γ 0 (x + k₀ + a)) - lam 0 (γ 0 (x + k₀))) b (lam 0 (γ 0 (x + k₀))) := by
  rw [diffKeyCount, card_filter_cons]
  refine Finset.sum_congr rfl (fun k₀ _ => ?_)
  rw [diffKeyCount]
  congr 1
  apply Finset.filter_congr
  intro k _
  simp only [run, Fin.tail_cons, Fin.cons_zero]
  rw [add_sub_cancel, add_right_comm x a k₀]

/-- **The count does not depend on the input.** For every `x` and `y`,
`diffKeyCount lam γ r a b x = diffKeyCount lam γ r a b y`. -/
theorem diffKeyCount_const (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ) (a b x y : X) :
    diffKeyCount lam γ r a b x = diffKeyCount lam γ r a b y := by
  induction r generalizing lam γ a x y with
  | zero => simp [diffKeyCount_zero]
  | succ r ih =>
    rw [diffKeyCount_succ_eq_sum_key, diffKeyCount_succ_eq_sum_key]
    let f : X → ℕ := fun z => diffKeyCount (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
      (lam 0 (γ 0 (z + a)) - lam 0 (γ 0 z)) b 0
    calc _ = ∑ k₀ : X, f (x + k₀) := Finset.sum_congr rfl fun k₀ _ => ih _ _ _ _ _
      _ = ∑ z : X, f z := Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
      _ = ∑ k₀ : X, f (y + k₀) := (Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun _ => rfl)).symm
      _ = _ := Finset.sum_congr rfl fun k₀ _ => (ih _ _ _ _ _).symm

/-- **One round, then the rest.** The count over `r + 1` rounds is
`∑ c, diffCount (γ 0) a c * (count of the last r rounds from lam 0 c to b)`, at any input `y`
of the last `r` rounds. -/
theorem diffKeyCount_succ (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ) (a b x y : X) :
    diffKeyCount lam γ (r + 1) a b x = ∑ c : X, diffCount (γ 0) a c *
      diffKeyCount (fun n => lam (n + 1)) (fun n => γ (n + 1)) r (lam 0 c) b y := by
  rw [diffKeyCount_succ_eq_sum_key]
  let f : X → ℕ := fun c => diffKeyCount (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
    (lam 0 c) b y
  calc _ = ∑ k₀ : X, f (γ 0 (x + k₀ + a) - γ 0 (x + k₀)) := by
        refine Finset.sum_congr rfl fun k₀ _ => ?_
        rw [diffKeyCount_const _ _ _ _ _ _ y, ← map_sub]
    _ = ∑ z : X, f (γ 0 (z + a) - γ 0 z) :=
        Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
    _ = ∑ c : X, ∑ z ∈ Finset.univ.filter (fun z => γ 0 (z + a) - γ 0 z = c), f c :=
        (Finset.sum_fiberwise' _ _ _).symm
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_const, smul_eq_mul]
        rfl

/-- **Composition.** The count over `r₁ + r₂` rounds is the sum, over the difference `c` after
the first `r₁` rounds, of the count of the first `r₁` rounds from `a` to `c` times the count of
the last `r₂` rounds from `c` to `b`. Both counts are over their own keys, and the second may be
taken at any input `y`. -/
theorem diffKeyCount_add (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r₁ r₂ : ℕ) (a b x y : X) :
    diffKeyCount lam γ (r₁ + r₂) a b x = ∑ c : X, diffKeyCount lam γ r₁ a c x *
      diffKeyCount (fun n => lam (n + r₁)) (fun n => γ (n + r₁)) r₂ c b y := by
  induction r₁ generalizing lam γ a x with
  | zero =>
    simp only [Nat.zero_add, diffKeyCount_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact diffKeyCount_const _ _ _ _ _ _ _
  | succ r ih =>
    rw [show r + 1 + r₂ = (r + r₂) + 1 by omega, diffKeyCount_succ lam γ (r + r₂) a b x y]
    simp_rw [ih (fun n => lam (n + 1)) (fun n => γ (n + 1)) _ y,
      diffKeyCount_succ lam γ r a _ x y, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

/-- **Rows sum to `|X| ^ r`.** Each key vector gives exactly one output difference. -/
theorem sum_diffKeyCount (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ) (a x : X) :
    ∑ b : X, diffKeyCount lam γ r a b x = Fintype.card X ^ r := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun k : Fin r → X => run lam γ r k (x + a) - run lam γ r k x)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  exact h.symm

/-- **Columns sum to `|X| ^ r` when every round is bijective.** This uses `sum_diffCount_col`
in each round. -/
theorem sum_diffKeyCount_col (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (hγ : ∀ n < r, Function.Bijective (γ n)) (b x : X) :
    ∑ a : X, diffKeyCount lam γ r a b x = Fintype.card X ^ r := by
  induction r generalizing lam γ b x with
  | zero => simp [diffKeyCount_zero]
  | succ r ih =>
    simp_rw [diffKeyCount_succ lam γ r _ b x x]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, sum_diffCount_col (hγ 0 (by omega))]
    rw [← Finset.mul_sum, Fintype.sum_equiv (lam 0).toEquiv
      (fun c => diffKeyCount (fun n => lam (n + 1)) (fun n => γ (n + 1)) r (lam 0 c) b x)
      (fun d => diffKeyCount (fun n => lam (n + 1)) (fun n => γ (n + 1)) r d b x)
      (fun _ => rfl), ih _ _ (fun n hn => hγ (n + 1) (by omega)), pow_succ, mul_comm]

/-- If the first `r` maps `γ n` are injective, no key vector takes a nonzero input difference to
the output difference `0`. -/
theorem diffKeyCount_eq_zero (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (hγ : ∀ n < r, Function.Injective (γ n)) {a : X} (ha : a ≠ 0) (x : X) :
    diffKeyCount lam γ r a 0 x = 0 := by
  induction r generalizing lam γ a x with
  | zero => simp [diffKeyCount_zero, ha]
  | succ r ih =>
    rw [diffKeyCount_succ lam γ r a 0 x x]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = 0
    · rw [hc, diffCount_eq_zero_of_injective (hγ 0 (by omega)) ha, zero_mul]
    · have hlc : lam 0 c ≠ 0 := fun h => hc ((lam 0).injective (by rw [h, map_zero]))
      rw [ih _ _ (fun n hn => hγ (n + 1) (by omega)) hlc x, mul_zero]

/-- **A window bound carries over to the schedule.** Suppose that the first `j` maps `γ n` are
injective, that the `m` maps `γ n` with `j + w ≤ n < j + w + m` (the rounds after the window) are
bijective, and that the `w` rounds starting at round `j` satisfy `count * Q ≤ V` at every
nonzero input difference. Then for `a ≠ 0`,
`diffKeyCount lam γ (j + w + m) a b x * Q ≤ V * |X| ^ (j + m)`: the first `j` rounds keep the
difference nonzero, and their row sums and the column sums of the last `m` rounds are
`|X| ^ j` and `|X| ^ m`. -/
theorem diffKeyCount_window_bound (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (j w m : ℕ)
    (hpre : ∀ n < j, Function.Injective (γ n))
    (hpost : ∀ n, j + w ≤ n → n < j + w + m → Function.Bijective (γ n)) {Q V : ℕ}
    (hwin : ∀ c : X, c ≠ 0 → ∀ e y : X,
      diffKeyCount (fun n => lam (n + j)) (fun n => γ (n + j)) w c e y * Q ≤ V)
    {a : X} (ha : a ≠ 0) (b x : X) :
    diffKeyCount lam γ (j + w + m) a b x * Q ≤ V * Fintype.card X ^ (j + m) := by
  rw [Nat.add_assoc, diffKeyCount_add lam γ j (w + m) a b x x]
  simp_rw [diffKeyCount_add (fun n => lam (n + j)) (fun n => γ (n + j)) w m _ b x x]
  have hcol : ∑ e : X, diffKeyCount (fun n => lam (n + w + j)) (fun n => γ (n + w + j)) m e b x
      = Fintype.card X ^ m :=
    sum_diffKeyCount_col _ _ m (fun n hn => hpost (n + w + j) (by omega) (by omega)) b x
  rw [Finset.sum_mul]
  calc ∑ c : X, diffKeyCount lam γ j a c x * (∑ e : X,
        diffKeyCount (fun n => lam (n + j)) (fun n => γ (n + j)) w c e x *
        diffKeyCount (fun n => lam (n + w + j)) (fun n => γ (n + w + j)) m e b x) * Q
      ≤ ∑ c : X, diffKeyCount lam γ j a c x * (V * Fintype.card X ^ m) := by
        refine Finset.sum_le_sum fun c _ => ?_
        by_cases hc : c = 0
        · rw [hc, diffKeyCount_eq_zero lam γ j hpre ha x]
          simp
        · rw [mul_assoc]
          refine Nat.mul_le_mul_left _ ?_
          rw [Finset.sum_mul, ← hcol, Finset.mul_sum]
          refine Finset.sum_le_sum fun e _ => ?_
          rw [mul_right_comm]
          exact Nat.mul_le_mul_right _ (hwin c hc e x)
    _ = V * Fintype.card X ^ (j + m) := by
        rw [← Finset.sum_mul, sum_diffKeyCount, pow_add]
        ring

/-! ### Two rounds -/

/-- One round: `diffKeyCount lam γ 1 a b x = diffCount (γ 0) a ((lam 0).symm b)`. -/
theorem diffKeyCount_one (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (a b x : X) :
    diffKeyCount lam γ 1 a b x = diffCount (γ 0) a ((lam 0).symm b) := by
  rw [diffKeyCount_succ lam γ 0 a b x x, Finset.sum_eq_single ((lam 0).symm b)]
  · rw [diffKeyCount_zero, AddEquiv.apply_symm_apply, if_pos rfl, mul_one]
  · intro c _ hc
    rw [diffKeyCount_zero, if_neg, mul_zero]
    intro h
    exact hc (by rw [← h, AddEquiv.symm_apply_apply])
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Two rounds as a sum over the middle difference.** The two-round count is
`∑ c, diffCount (γ 0) a c * diffCount (γ 1) (lam 0 c) ((lam 1).symm b)`, where `c` is the output
difference of `γ 0`. -/
theorem diffKeyCount_two (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (a b x : X) :
    diffKeyCount lam γ 2 a b x =
      ∑ c : X, diffCount (γ 0) a c * diffCount (γ 1) (lam 0 c) ((lam 1).symm b) := by
  rw [diffKeyCount_succ lam γ 1 a b x x]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [diffKeyCount_one]

/-- **Two rounds as a sum over trails.** The two-round count is the sum of `trailKeyCount`, the
count of `Scheduled.lean`, over all trails `a → d → b`. -/
theorem diffKeyCount_two_eq_sum_trailKeyCount (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (a b x : X) :
    diffKeyCount lam γ 2 a b x =
      ∑ d : X, trailKeyCount lam γ 2 (fun n => if n = 0 then a else if n = 1 then d else b) x := by
  rw [diffKeyCount_two]
  simp only [trailKeyCount_eq_prod, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  exact Fintype.sum_equiv (lam 0).toEquiv _ _ (fun c => by simp)

omit [Fintype X] [DecidableEq X] [AddCommGroup X] in
/-- The trail through the intermediate differences `d : Fin r → X`: `a` at position `0`,
`d (n - 1)` at position `n` for `1 ≤ n ≤ r`, and `b` from position `r + 1` on. -/
def throughTrail {r : ℕ} (a : X) (d : Fin r → X) (b : X) (n : ℕ) : X :=
  if n = 0 then a else if h : n - 1 < r then d ⟨n - 1, h⟩ else b

omit [Fintype X] [DecidableEq X] [AddCommGroup X] in
/-- Dropping the first position of `throughTrail a d b` leaves the trail from `d 0` through
`Fin.tail d` to `b`. -/
theorem throughTrail_succ {r : ℕ} (a : X) (d : Fin (r + 1) → X) (b : X) (n : ℕ) :
    throughTrail a d b (n + 1) = throughTrail (d 0) (Fin.tail d) b n := by
  rcases n with _ | n
  · simp [throughTrail]
  · simp only [throughTrail, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel]
    by_cases h : n < r
    · rw [dif_pos (by omega), dif_pos h]
      rfl
    · rw [dif_neg (by omega), dif_neg h]

/-- **`r + 1` rounds as a sum over trails.** The count over `r + 1` rounds is the sum of
`trailKeyCount`, the count of `Scheduled.lean`, over all trails from `a` to `b`: one trail
`throughTrail a d b` for each choice of the intermediate differences `d : Fin r → X`. -/
theorem diffKeyCount_succ_eq_sum_trailKeyCount (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (a b x : X) :
    diffKeyCount lam γ (r + 1) a b x =
      ∑ d : Fin r → X, trailKeyCount lam γ (r + 1) (throughTrail a d b) x := by
  induction r generalizing lam γ a x with
  | zero =>
    rw [diffKeyCount_one, Fintype.sum_unique, trailKeyCount_eq_prod]
    simp [throughTrail]
  | succ r ih =>
    rw [diffKeyCount_succ lam γ (r + 1) a b x x,
      ← (Fin.consEquiv (fun _ : Fin (r + 1) => X)).sum_comp, Fintype.sum_prod_type]
    conv_lhs => rw [← (lam 0).symm.toEquiv.sum_comp]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [trailKeyCount_eq_prod, trailKeyCount_eq_prod, Finset.prod_range_succ' _ (r + 1),
      mul_comm]
    have hd : Fin.tail ((Fin.consEquiv fun _ : Fin (r + 1) => X) (c, d)) = d := rfl
    have hc : (Fin.consEquiv fun _ : Fin (r + 1) => X) (c, d) 0 = c := rfl
    have he : (lam 0).symm.toEquiv c = (lam 0).symm c := rfl
    simp only [he, AddEquiv.apply_symm_apply, throughTrail_succ, hd, hc]
    simp [throughTrail]

end Keyed

/-! ### Counting codewords -/

section Codewords

variable {V J K : Type*} [Fintype V] [AddCommGroup V] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K] [AddCommGroup K]

/-- **Counting codewords.** Let `Φ` be an injective additive map whose nonzero values have
weight at least `B`, and let `g j : K → ℕ` weigh the value at position `j`. On a
nonempty set `S` of positions, let `g j` be at most `u`, sum to at most `q`, and vanish at `0`;
off `S`, let `g j` vanish away from `0` and be at most `q` at `0`. Then
`(∑ c, ∏ j, g j (Φ c j)) * q ^ (B - 1) ≤ u ^ (B - 1) * q ^ |J|`. -/
theorem sum_prod_le_of_weight (Φ : V →+ (J → K)) (hΦ : Function.Injective Φ) {B : ℕ}
    (hdist : ∀ c : V, c ≠ 0 → B ≤ weight (Φ c)) (g : J → K → ℕ) (S : Finset J)
    (hS : S.Nonempty) {u q : ℕ} (hle : ∀ j ∈ S, ∀ v, g j v ≤ u)
    (hsum : ∀ j ∈ S, ∑ v, g j v ≤ q) (hzero : ∀ j ∈ S, g j 0 = 0)
    (hout : ∀ j ∉ S, ∀ v, g j v ≠ 0 → v = 0) (houtq : ∀ j ∉ S, g j 0 ≤ q) :
    (∑ c : V, ∏ j, g j (Φ c j)) * q ^ (B - 1) ≤ u ^ (B - 1) * q ^ Fintype.card J := by
  classical
  have hoff : ∀ c : V, (∏ j, g j (Φ c j)) ≠ 0 → ∀ j ∉ S, Φ c j = 0 := fun c hc j hj =>
    hout j hj _ (fun h => hc (Finset.prod_eq_zero (Finset.mem_univ j) h))
  have hsupp : ∀ c : V, (∏ j, g j (Φ c j)) ≠ 0 → activePattern (Φ c) ⊆ S := by
    intro c hc j hj
    by_contra hjS
    exact (mem_activePattern.mp hj) (hoff c hc j hjS)
  by_cases hsmall : S.card < B - 1
  · have hall : ∀ c : V, (∏ j, g j (Φ c j)) = 0 := by
      intro c
      by_contra hc
      by_cases hc0 : c = 0
      · obtain ⟨j, hj⟩ := hS
        apply hc
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        rw [hc0, map_zero, Pi.zero_apply, hzero j hj]
      · have h1 := hdist c hc0
        have h2 : weight (Φ c) ≤ S.card := Finset.card_le_card (hsupp c hc)
        omega
    simp [hall]
  · rw [not_lt] at hsmall
    obtain ⟨D, hDS, hDcard⟩ := Finset.exists_subset_card_eq hsmall
    set T := Finset.univ.filter (fun c : V => (∏ j, g j (Φ c j)) ≠ 0) with hT
    have hinj : ∀ c ∈ T, ∀ c' ∈ T, (∀ j ∈ S \ D, Φ c j = Φ c' j) → c = c' := by
      intro c hc c' hc' hI
      rw [hT, Finset.mem_filter] at hc hc'
      by_contra hne
      have hsub : activePattern (Φ (c - c')) ⊆ D := by
        intro j hj
        rw [mem_activePattern, map_sub, Pi.sub_apply, sub_ne_zero] at hj
        by_contra hjD
        by_cases hjS : j ∈ S
        · exact hj (hI j (Finset.mem_sdiff.mpr ⟨hjS, hjD⟩))
        · exact hj (by rw [hoff c hc.2 j hjS, hoff c' hc'.2 j hjS])
      have h1 := hdist (c - c') (sub_ne_zero.mpr hne)
      have h2 : weight (Φ (c - c')) ≤ D.card := Finset.card_le_card hsub
      have hw0 : (activePattern (Φ (c - c'))).card = 0 := by
        change weight (Φ (c - c')) = 0
        omega
      have hz : Φ (c - c') = 0 := activePattern_eq_empty.mp (Finset.card_eq_zero.mp hw0)
      exact hne (sub_eq_zero.mp (hΦ (by rw [hz, map_zero])))
    have hterm : ∀ c ∈ T, (∏ j, g j (Φ c j))
        ≤ u ^ (B - 1) * (∏ j ∈ S \ D, g j (Φ c j)) * q ^ (Fintype.card J - S.card) := by
      intro c hc
      rw [hT, Finset.mem_filter] at hc
      rw [← Finset.prod_mul_prod_compl S, ← Finset.prod_sdiff hDS]
      have hD : ∏ j ∈ D, g j (Φ c j) ≤ u ^ (B - 1) := by
        calc _ ≤ ∏ _j ∈ D, u := Finset.prod_le_prod' fun j hj => hle j (hDS hj) _
          _ = u ^ (B - 1) := by rw [Finset.prod_const, hDcard]
      have hC : ∏ j ∈ Sᶜ, g j (Φ c j) ≤ q ^ (Fintype.card J - S.card) := by
        calc _ ≤ ∏ _j ∈ Sᶜ, q := Finset.prod_le_prod' fun j hj => by
                have hjS := Finset.mem_compl.mp hj
                rw [hoff c hc.2 j hjS]
                exact houtq j hjS
          _ = _ := by rw [Finset.prod_const, Finset.card_compl]
      calc (∏ j ∈ S \ D, g j (Φ c j)) * (∏ j ∈ D, g j (Φ c j)) * ∏ j ∈ Sᶜ, g j (Φ c j)
          ≤ (∏ j ∈ S \ D, g j (Φ c j)) * u ^ (B - 1) * q ^ (Fintype.card J - S.card) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hD) hC
        _ = _ := by ring
    have hproj : ∑ c ∈ T, ∏ j ∈ S \ D, g j (Φ c j) ≤ q ^ (S \ D).card := by
      let π : V → (↥(S \ D) → K) := fun c j => Φ c j
      have hπ : Set.InjOn π T := fun c hc c' hc' h =>
        hinj c hc c' hc' (fun j hj => congrFun h ⟨j, hj⟩)
      calc ∑ c ∈ T, ∏ j ∈ S \ D, g j (Φ c j)
          = ∑ c ∈ T, ∏ j : ↥(S \ D), g j (π c j) :=
            Finset.sum_congr rfl fun c _ => (Finset.prod_coe_sort (S \ D) _).symm
        _ = ∑ w ∈ T.image π, ∏ j : ↥(S \ D), g j (w j) :=
            (Finset.sum_image (f := fun w : ↥(S \ D) → K => ∏ j : ↥(S \ D), g j (w j)) hπ).symm
        _ ≤ ∑ w : ↥(S \ D) → K, ∏ j : ↥(S \ D), g j (w j) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = ∏ j : ↥(S \ D), ∑ v, g j v := (Fintype.prod_sum _).symm
        _ ≤ ∏ _j : ↥(S \ D), q := Finset.prod_le_prod' fun j _ =>
            hsum j (Finset.mem_sdiff.mp j.2).1
        _ = q ^ (S \ D).card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    have hIcard : (S \ D).card + (B - 1) = S.card := by
      rw [Finset.card_sdiff_of_subset hDS, hDcard]
      omega
    have hSJ : S.card ≤ Fintype.card J := Finset.card_le_univ S
    calc (∑ c : V, ∏ j, g j (Φ c j)) * q ^ (B - 1)
        = (∑ c ∈ T, ∏ j, g j (Φ c j)) * q ^ (B - 1) := by rw [hT, Finset.sum_filter_ne_zero]
      _ ≤ (∑ c ∈ T, u ^ (B - 1) * (∏ j ∈ S \ D, g j (Φ c j))
            * q ^ (Fintype.card J - S.card)) * q ^ (B - 1) :=
          Nat.mul_le_mul_right _ (Finset.sum_le_sum hterm)
      _ = u ^ (B - 1) * (∑ c ∈ T, ∏ j ∈ S \ D, g j (Φ c j))
            * (q ^ (Fintype.card J - S.card) * q ^ (B - 1)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          ring
      _ ≤ u ^ (B - 1) * q ^ (S \ D).card * (q ^ (Fintype.card J - S.card) * q ^ (B - 1)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hproj)
      _ = u ^ (B - 1) * q ^ Fintype.card J := by
          rw [mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega

end Codewords

/-! ### Two bricklayer rounds -/

section TwoRounds

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Fintype K] [DecidableEq K]
  [AddCommGroup K]

/-- The pair `(c, L c)` as one state indexed by `Idx ⊕ Idx`: `Sum.inl i` reads `c i` and
`Sum.inr i` reads `L c i`. Its weight is `weight c + weight (L c)` (`weight_sumElim`). -/
def codeword (L : (Idx → K) →+ (Idx → K)) : (Idx → K) →+ (Idx ⊕ Idx → K) where
  toFun c := Sum.elim c (L c)
  map_zero' := by
    funext j
    cases j <;> simp
  map_add' c c' := by
    funext j
    cases j <;> simp

omit [Fintype Idx] [DecidableEq Idx] [Fintype K] [DecidableEq K] in
theorem codeword_apply (L : (Idx → K) →+ (Idx → K)) (c : Idx → K) :
    codeword L c = Sum.elim c (L c) := rfl

omit [DecidableEq Idx] [Fintype K] in
/-- The weight of a state on `Idx ⊕ Idx` is the sum of the weights of its two halves. -/
theorem weight_sumElim (f g : Idx → K) : weight (Sum.elim f g) = weight f + weight g := by
  have h : activePattern (Sum.elim f g) = (activePattern f).disjSum (activePattern g) := by
    ext j
    cases j <;> simp
  rw [weight, h, Finset.card_disjSum]
  rfl

/-- **The two-round bound.** Let rounds `0` and `1` have bricklayer differential counts over the
S-boxes `s n i`, each bijective with differential uniformity at most `u`, and let `lam 0` have
branch number at least `B`. Then for every nonzero input difference `a`, every output difference
`b` and every input `x`,
`diffKeyCount lam γ 2 a b x * |K| ^ (B - 1) ≤ u ^ (B - 1) * |Idx → K| ^ 2`.

This bounds the differential, the sum over all two-round trails from `a` to `b`, averaged over an
additional independent uniform key per round. It says nothing about fixed keys or fixed round
constants. -/
theorem diffKeyCount_two_round_bound (lam : ℕ → (Idx → K) ≃+ (Idx → K))
    (γ : ℕ → (Idx → K) → (Idx → K)) (s : ℕ → Idx → K → K)
    (hγ : ∀ n < 2, ∀ a b, diffCount (γ n) a b = ∏ i, diffCount (s n i) (a i) (b i))
    (hs : ∀ n < 2, ∀ i, Function.Bijective (s n i)) {u B : ℕ}
    (hu : ∀ n < 2, ∀ i, IsDiffUniform (s n i) u) (hB : isBranchBound id (lam 0) B)
    {a : Idx → K} (ha : a ≠ 0) (b x : Idx → K) :
    diffKeyCount lam γ 2 a b x * Fintype.card K ^ (B - 1)
      ≤ u ^ (B - 1) * Fintype.card (Idx → K) ^ 2 := by
  set β := (lam 1).symm b with hβ
  let g : Idx ⊕ Idx → K → ℕ :=
    Sum.elim (fun i v => diffCount (s 0 i) (a i) v) (fun i v => diffCount (s 1 i) v (β i))
  have hsum : diffKeyCount lam γ 2 a b x =
      ∑ c : Idx → K, ∏ j, g j (codeword (lam 0).toAddMonoidHom c j) := by
    rw [diffKeyCount_two]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hγ 0 (by norm_num), hγ 1 (by norm_num), Fintype.prod_sum_type]
    rfl
  have hcard : Fintype.card (Idx → K) ^ 2 = Fintype.card K ^ Fintype.card (Idx ⊕ Idx) := by
    rw [Fintype.card_fun, Fintype.card_sum, ← pow_mul]
    ring_nf
  rw [hsum, hcard]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha
  refine sum_prod_le_of_weight _ ?_ ?_ g
    ((activePattern a).disjSum (activePattern β)) ⟨Sum.inl i₀, ?_⟩ ?_ ?_ ?_ ?_ ?_
  · intro c c' h
    funext i
    exact congrFun h (Sum.inl i)
  · intro c hc
    rw [codeword_apply, weight_sumElim]
    simpa [colWeight_id] using hB c hc
  · simpa using hi₀
  · rintro (i | i) hj v
    · simp only [Finset.inl_mem_disjSum, mem_activePattern] at hj
      exact hu 0 (by norm_num) i (a i) hj v
    · simp only [Finset.inr_mem_disjSum, mem_activePattern] at hj
      by_cases hv : v = 0
      · simp [g, hv, diffCount_zero_left, hj]
      · exact hu 1 (by norm_num) i v hv (β i)
  · rintro (i | i) _
    · exact (sum_diffCount (s 0 i) (a i)).le
    · exact (sum_diffCount_col (hs 1 (by norm_num) i) (β i)).le
  · rintro (i | i) hj
    · simp only [Finset.inl_mem_disjSum, mem_activePattern] at hj
      exact diffCount_eq_zero_of_injective (hs 0 (by norm_num) i).injective hj
    · simp only [Finset.inr_mem_disjSum, mem_activePattern] at hj
      simp [g, diffCount_zero_left, hj]
  · rintro (i | i) hj v hv
    · simp only [Finset.inl_mem_disjSum, mem_activePattern, not_not] at hj
      by_contra hv0
      simp [g, hj, diffCount_zero_left, hv0] at hv
    · simp only [Finset.inr_mem_disjSum, mem_activePattern, not_not] at hj
      by_contra hv0
      exact hv (by
        simp only [g, Sum.elim_inr, hj]
        exact diffCount_eq_zero_of_injective (hs 1 (by norm_num) i).injective hv0)
  · intro j _
    cases j <;> exact diffCount_le_card _ _ _

/-- `diffKeyCount_two_round_bound` for bricklayer S-box layers, `γ n = bricklayer (s n)`. -/
theorem bricklayer_two_round_bound (lam : ℕ → (Idx → K) ≃+ (Idx → K)) (s : ℕ → Idx → K → K)
    (hs : ∀ n < 2, ∀ i, Function.Bijective (s n i)) {u B : ℕ}
    (hu : ∀ n < 2, ∀ i, IsDiffUniform (s n i) u) (hB : isBranchBound id (lam 0) B)
    {a : Idx → K} (ha : a ≠ 0) (b x : Idx → K) :
    diffKeyCount lam (fun n => bricklayer (s n)) 2 a b x * Fintype.card K ^ (B - 1)
      ≤ u ^ (B - 1) * Fintype.card (Idx → K) ^ 2 :=
  diffKeyCount_two_round_bound lam _ s (fun n _ => diffCount_bricklayer (s n)) hs hu hB ha b x

/-- **The two-round bound for a whole schedule.** If all of the first `R` rounds are bijective
and rounds `j` and `j + 1 ≤ R - 1` satisfy the hypotheses of `diffKeyCount_two_round_bound`, with
`lam j` of branch number at least `B`, then for `a ≠ 0`,
`diffKeyCount lam γ R a b x * |K| ^ (B - 1) ≤ u ^ (B - 1) * |Idx → K| ^ R`. The other rounds are
not charged. The same model: an additional independent uniform key per round. -/
theorem diffKeyCount_bound_of_two_rounds (lam : ℕ → (Idx → K) ≃+ (Idx → K))
    (γ : ℕ → (Idx → K) → (Idx → K)) (s : ℕ → Idx → K → K) (R j : ℕ) (hj : j + 2 ≤ R)
    (hbij : ∀ n < R, Function.Bijective (γ n))
    (hγ : ∀ n, j ≤ n → n < j + 2 → ∀ a b, diffCount (γ n) a b = ∏ i, diffCount (s n i) (a i) (b i))
    (hs : ∀ n, j ≤ n → n < j + 2 → ∀ i, Function.Bijective (s n i)) {u B : ℕ}
    (hu : ∀ n, j ≤ n → n < j + 2 → ∀ i, IsDiffUniform (s n i) u)
    (hB : isBranchBound id (lam j) B) {a : Idx → K} (ha : a ≠ 0) (b x : Idx → K) :
    diffKeyCount lam γ R a b x * Fintype.card K ^ (B - 1)
      ≤ u ^ (B - 1) * Fintype.card (Idx → K) ^ R := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h := diffKeyCount_window_bound lam γ j 2 m
    (fun n hn => (hbij n (by omega)).injective) (fun n _ hn => hbij n hn)
    (fun c hc e y => diffKeyCount_two_round_bound (fun n => lam (n + j)) (fun n => γ (n + j))
      (fun n => s (n + j)) (fun n hn => hγ (n + j) (by omega) (by omega))
      (fun n hn => hs (n + j) (by omega) (by omega))
      (fun n hn => hu (n + j) (by omega) (by omega)) (by simpa using hB) hc e y) ha b x
  calc diffKeyCount lam γ (j + 2 + m) a b x * Fintype.card K ^ (B - 1)
      ≤ u ^ (B - 1) * Fintype.card (Idx → K) ^ 2 * Fintype.card (Idx → K) ^ (j + m) := h
    _ = u ^ (B - 1) * Fintype.card (Idx → K) ^ (j + 2 + m) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega

end TwoRounds

end Scheduled
