/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.MiddleBound
import WideTrail.Hades.RelationCheck
import Mathlib.Algebra.Field.ZMod

/-!
# Window relations: middle bounds from refuted activity patterns

`Hades.MiddleBound A {i0} m μ` says that every trail (`IsTrail`) through `m` consecutive rounds
with linear map `A` and one S-box, at the coordinate `i0`, starting from a nonzero difference,
charges at least `μ` S-boxes. The window argument gives `μ = m / w`
(`MiddleBound.of_inactiveSpace`). This file proves larger middle bounds
from linear relations between the S-box differences of consecutive rounds, checked as finite
certificates.

## The relations

For a trail `T`, write `x_n = T n i0` for the S-box input difference of round `n` and
`y_n = sboxOut rounds T i0 n` for its output difference, coordinate `i0` of `lin⁻¹ (T (n + 1))`.
Under `IsTrail` with mask `{i0}`, `T (n + 1) = lin (T n with coordinate i0 replaced by y_n)`
(`IsTrail.succ_eq_update`) and `y_n = 0 ↔ x_n = 0` (`IsTrail.sboxOut_eq_zero_iff`).

A *chain* of length `D` for `A` at `i0` is a list of row vectors `ψ 0, …, ψ D` and scalars
`γ 0, …, γ (D - 1)` with `ψ 0 = 0`, `ψ D` zero off `i0`, and, for `r < D` and every `v`,
`ψ (r + 1) ⬝ᵥ A v = ψ r ⬝ᵥ (v with coordinate i0 replaced by 0) + γ r * v i0`. Then every trail
through the rounds `n, …, n + D - 1` with linear map `A` and mask `{i0}` satisfies
(`IsTrail.window_relation`)

  `∑_{r ≤ D} (α_r x_{n+r} + β_r y_{n+r}) = 0`, with `α_r = ψ r i0`, `β_r = -γ r` for `r < D`
  and `β_D = 0`.

The proof telescopes `ψ r ⬝ᵥ T (n + r)` over `r`. If `κ_j = e_{i0}ᵀ A^j` and `a_0, …, a_D` with
`a_D = 1` satisfy `∑ a_j κ_j = 0` (for instance the coefficients of the characteristic
polynomial of `A`, with `D` the size of `A`), the rows `ψ r = ∑_{i ≥ r} a_i κ_{i-r}` form a chain,
with `γ r = ψ r i0 - a_r`; this file only consumes a chain and does not construct one.

## Results

* `MiddleBound.of_relations` (generic `A`, `m`, `D`, `k`): if `inactiveSpace A {i0} m = ⊥` and
  every nonempty pattern of fewer than `k` of the rounds `0, …, m - 1` is refuted, then
  `MiddleBound A {i0} m k`. A refutation of a pattern `S` (`RelRefutation.Valid`) is a
  combination `∑_n λ_n R_n` of the `m - D` relations `R_0, …, R_{m-D-1}` whose coefficients on the
  variables `x_k, y_k` (`k ∈ S`) are `1` on one of them and `0` on the others. The variables of
  rounds outside `S` vanish, so the chosen variable would be `0`, although its round is active.
  The empty pattern is excluded by `inactiveSpace A {i0} m = ⊥`.
* `refutations_of_pairs`: for `k = 3` it suffices to refute every `{x}` and every `{x, y}` with
  `x < y`.
* `RelationCheck.checkAll_spec` and `MiddleBound.of_relationCheck`: for `A = diag d + J`
  (`Poseidon2.diagPlusOnes 1 d`) over `ZMod p`, `p` prime, a Nat-list certificate that passes the
  Boolean checker `RelationCheck.checkAll` of `WideTrail.Hades.RelationCheck` gives
  `MiddleBound (diagPlusOnes 1 d) {i0} m 3`. The checker is evaluated by `decide +kernel` in the
  certificate files; the theorems here say what a passing check means.
* `isTrail_of_updates`, `RelationCheck.checkTrail_spec` and `MiddleBound.not_of_checkTrail`: an
  explicit trail from a nonzero difference (row `0` of `Ts` nonzero), checked by
  `RelationCheck.checkTrail`, with fewer than `μ` active rounds shows that `μ` is not a middle
  bound; with `μ = k + 1`, it shows that a proved middle bound `k` is the largest one.

`WideTrail.Hades.Checks.WindowRelation` runs the whole path on the `ZMod 5` toy layer of
`WideTrail.Hades.Checks.Toy`.

## What is not claimed

The bounds are lower bounds on charged S-boxes in the `IsTrail` model, which records only
supports, the mask and the linear map; nothing is said here about probabilities, keys or actual
input pairs (those follow from a middle bound through `WideTrail.Hades.MiddleBound`). Besides the
linear maps and the masks, the argument uses only that `y_n = 0` exactly when `x_n = 0`, which
`IsTrail` records; it does not use the size of the field. Only the direction
"certificate implies bound" is proved: a pattern for which no refutation is given is not thereby
shown to occur, and the witness trails of `MiddleBound.not_of_checkTrail` are trails in the
`IsTrail` model, not claimed to be realised by any input pair or key.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Hades

/-! ### S-box outputs -/

section Relation

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- The S-box output difference of round `n` at the coordinate `i0`: coordinate `i0` of
`lin⁻¹ (T (n + 1))`, the difference between the S-box layer and the linear layer of round `n`. -/
def sboxOut (rounds : ℕ → RoundSpec Idx K) (T : ℕ → Idx → K) (i0 : Idx) (n : ℕ) : K :=
  (rounds n).lin.symm (T (n + 1)) i0

/-- In a round with mask `{i0}`, the difference after the S-box layer is the difference before
it with coordinate `i0` replaced by the S-box output difference. -/
theorem IsTrail.lin_symm_eq_update {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K} {R n : ℕ}
    {i0 : Idx} (hT : IsTrail rounds T R) (hn : n < R) (hmask : (rounds n).mask = {i0}) :
    (rounds n).lin.symm (T (n + 1)) = Function.update (T n) i0 (sboxOut rounds T i0 n) := by
  obtain ⟨b, -, hl, hout⟩ := hT n hn
  have hb : (rounds n).lin.symm (T (n + 1)) = b := by
    rw [← hl, LinearEquiv.symm_apply_apply]
  funext i
  by_cases hi : i = i0
  · subst hi
    simp [sboxOut]
  · rw [Function.update_of_ne hi, hb]
    exact hout i (by rw [hmask, Finset.mem_singleton]; exact hi)

/-- **One round with mask `{i0}`**: `T (n + 1)` is the linear map applied to `T n` with
coordinate `i0` replaced by the S-box output difference. -/
theorem IsTrail.succ_eq_update {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K} {R n : ℕ}
    {i0 : Idx} (hT : IsTrail rounds T R) (hn : n < R) (hmask : (rounds n).mask = {i0}) :
    T (n + 1) = (rounds n).lin (Function.update (T n) i0 (sboxOut rounds T i0 n)) := by
  rw [← hT.lin_symm_eq_update hn hmask, LinearEquiv.apply_symm_apply]

omit [DecidableEq Idx] in
/-- **The S-box output difference vanishes exactly when the input difference does.** -/
theorem IsTrail.sboxOut_eq_zero_iff {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K} {R n : ℕ}
    {i0 : Idx} (hT : IsTrail rounds T R) (hn : n < R) :
    sboxOut rounds T i0 n = 0 ↔ T n i0 = 0 := by
  obtain ⟨b, hb, hl, -⟩ := hT n hn
  have hb' : (rounds n).lin.symm (T (n + 1)) = b := by
    rw [← hl, LinearEquiv.symm_apply_apply]
  have h := congrArg (fun s => i0 ∈ s) hb
  simp only [mem_activePattern, eq_iff_iff] at h
  rw [sboxOut, hb']
  exact not_iff_not.mp h

omit [Fintype Idx] [DecidableEq K] in
/-- Replacing coordinate `i0` of `v` by `0` removes the term `ψ i0 * v i0` of a dot product. -/
theorem dotProduct_update_zero [Fintype Idx] (ψ v : Idx → K) (i0 : Idx) :
    ψ ⬝ᵥ Function.update v i0 0 = ψ ⬝ᵥ v - ψ i0 * v i0 := by
  have h : Function.update v i0 0 = v - Pi.single i0 (v i0) := by
    funext i
    by_cases hi : i = i0
    · subst hi
      simp
    · simp [hi]
  rw [h, dotProduct_sub, dotProduct_single]

omit [Fintype Idx] [DecidableEq K] in
/-- The dot product with `ψ` whose coordinate `i0` is replaced by `γ`. -/
theorem update_dotProduct [Fintype Idx] (ψ v : Idx → K) (i0 : Idx) (γ : K) :
    Function.update ψ i0 γ ⬝ᵥ v = ψ ⬝ᵥ Function.update v i0 0 + γ * v i0 := by
  have h : Function.update ψ i0 γ = ψ - Pi.single i0 (ψ i0) + Pi.single i0 γ := by
    funext i
    by_cases hi : i = i0
    · subst hi
      simp
    · simp [hi]
  rw [h, add_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct,
    dotProduct_update_zero]

/-! ### The window relation -/

/-- The input coefficients of the window relation of a chain `ψ`: `α_r = ψ r i0`. -/
def relAlpha (ψ : ℕ → Idx → K) (i0 : Idx) (r : ℕ) : K :=
  ψ r i0

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- The output coefficients of the window relation of a chain of length `D`: `β_r = -γ r` for
`r < D` and `β_r = 0` from `D` on. -/
def relBeta (γ : ℕ → K) (D r : ℕ) : K :=
  if r < D then -γ r else 0

/-- **The window relation.** Let `ψ 0, …, ψ D` and `γ` be a chain of length `D` for `A` at `i0`:
`ψ 0 = 0`, `ψ D` vanishes off `i0`, and
`ψ (r + 1) ⬝ᵥ A v = ψ r ⬝ᵥ (v with coordinate i0 replaced by 0) + γ r * v i0` for `r < D`. Then
for every trail whose rounds `n, …, n + D - 1` have linear map `A` and mask `{i0}`,
`∑_{r ≤ D} (α_r x_{n+r} + β_r y_{n+r}) = 0` with `x_k = T k i0`, `y_k = sboxOut rounds T i0 k`,
`α = relAlpha ψ i0` and `β = relBeta γ D`. -/
theorem IsTrail.window_relation {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K} {R : ℕ}
    (hT : IsTrail rounds T R) (A : Module.End K (Idx → K)) (i0 : Idx) (D n : ℕ) (hn : n + D ≤ R)
    (hlin : ∀ j < D, ((rounds (n + j)).lin : Module.End K (Idx → K)) = A)
    (hmask : ∀ j < D, (rounds (n + j)).mask = {i0})
    (ψ : ℕ → Idx → K) (γ : ℕ → K) (hψ0 : ψ 0 = 0)
    (hstep : ∀ r < D, ∀ v, ψ (r + 1) ⬝ᵥ A v = ψ r ⬝ᵥ Function.update v i0 0 + γ r * v i0)
    (hψD : ∀ j, j ≠ i0 → ψ D j = 0) :
    ∑ r ∈ Finset.range (D + 1), (relAlpha ψ i0 r * T (n + r) i0 +
      relBeta γ D r * sboxOut rounds T i0 (n + r)) = 0 := by
  set f : ℕ → K := fun r => ψ r ⬝ᵥ T (n + r) with hf
  have hstep' : ∀ r < D, f (r + 1) - f r =
      γ r * sboxOut rounds T i0 (n + r) - ψ r i0 * T (n + r) i0 := by
    intro r hr
    have hsucc := hT.succ_eq_update (n := n + r) (by omega) (hmask r hr)
    have hlin' : ∀ v, (rounds (n + r)).lin v = A v := fun v => by
      rw [← hlin r hr]
      rfl
    simp only [hf, show n + (r + 1) = n + r + 1 by omega, hsucc, hlin', hstep r hr,
      Function.update_self, Function.update_idem, dotProduct_update_zero]
    ring
  have htel := Finset.sum_range_sub f D
  have hf0 : f 0 = 0 := by simp [hf, hψ0]
  have hfD : f D = ψ D i0 * T (n + D) i0 := by
    simp only [hf, dotProduct]
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hψD j hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i0) h)]
  rw [Finset.sum_range_succ]
  have hsum : ∑ r ∈ Finset.range D, (relAlpha ψ i0 r * T (n + r) i0 +
      relBeta γ D r * sboxOut rounds T i0 (n + r)) =
      -∑ r ∈ Finset.range D, (f (r + 1) - f r) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [hstep' r hr, relAlpha, relBeta, if_pos hr]
    ring
  rw [hsum, htel, hf0, hfD, relAlpha, relBeta, if_neg (lt_irrefl D)]
  ring

end Relation

/-! ### Refuting activity patterns -/

section Refutation

variable {R : Type*} [CommRing R]

/-- A refutation of an activity pattern: the combination `∑_n lam n * R_n` of the window
relations `R_n`, and the variable `(pos, out)` it is claimed to equal (`out = false` for the S-box
input of round `pos`, `out = true` for its output). -/
structure RelRefutation (K : Type*) where
  /-- The round of the isolated variable. -/
  pos : ℕ
  /-- `false` for the S-box input of round `pos`, `true` for its output. -/
  out : Bool
  /-- The multiplier of relation `n`. -/
  lam : ℕ → K

/-- The coefficient of variable `(k, o)` in relation `n`, which covers the rounds `n, …, n + D`:
`α (k - n)` on the S-box input (`o = false`) and `β (k - n)` on the S-box output (`o = true`) of
round `k`, and `0` outside the window. -/
def relCoef (α β : ℕ → R) (D n k : ℕ) (o : Bool) : R :=
  if n ≤ k ∧ k ≤ n + D then (if o then β (k - n) else α (k - n)) else 0

/-- `c` refutes the pattern `S` with the relations `R_0, …, R_{m-D-1}` of coefficients `α`, `β`:
`c.pos ∈ S`, and for every round `k ∈ S` and both of its variables, the coefficient of the
combination `∑_{n < m - D} c.lam n * R_n` is `1` on the variable `(c.pos, c.out)` and `0` on the
others. -/
def RelRefutation.Valid (α β : ℕ → R) (m D : ℕ) (S : Finset ℕ) (c : RelRefutation R) : Prop :=
  c.pos ∈ S ∧ ∀ k ∈ S, ∀ o : Bool,
    ∑ n ∈ Finset.range (m - D), c.lam n * relCoef α β D n k o =
      if k = c.pos ∧ o = c.out then 1 else 0

/-- **Patterns of one or two rounds.** To refute every nonempty pattern of fewer than `3` of the
rounds `0, …, m - 1`, it suffices to refute every `{x}` with `x < m` and every `{x, y}` with
`x < y < m`. -/
theorem refutations_of_pairs {α β : ℕ → R} {m D : ℕ} (c1 : ℕ → RelRefutation R)
    (c2 : ℕ → ℕ → RelRefutation R) (h1 : ∀ x < m, (c1 x).Valid α β m D {x})
    (h2 : ∀ x y, x < y → y < m → (c2 x y).Valid α β m D {x, y}) :
    ∀ S : Finset ℕ, S ⊆ Finset.range m → S.Nonempty → S.card < 3 →
      ∃ c : RelRefutation R, c.Valid α β m D S := by
  intro S hS hne hcard
  have hpos := hne.card_pos
  rcases (show S.card = 1 ∨ S.card = 2 by omega) with h | h
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨c1 x, h1 x (Finset.mem_range.mp (hS (Finset.mem_singleton_self x)))⟩
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h
    have hx := Finset.mem_range.mp (hS (Finset.mem_insert_self x {y}))
    have hy := Finset.mem_range.mp (hS (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact ⟨c2 x y, h2 x y hlt hy⟩
    · exact ⟨c2 y x, by rw [Finset.pair_comm]; exact h2 y x hlt hx⟩

end Refutation

section Bound

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- The variable `(k, o)` of a trail: the S-box input difference `T k i0` for `o = false`, the
S-box output difference for `o = true`. -/
def relVar (rounds : ℕ → RoundSpec Idx K) (T : ℕ → Idx → K) (i0 : Idx) (k : ℕ) (o : Bool) : K :=
  if o then sboxOut rounds T i0 k else T k i0

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- A window `n, …, n + D` inside `0, …, m - 1`, written as a sum over all of `0, …, m - 1`. -/
theorem sum_range_ite_window (g : ℕ → K) {m n D : ℕ} (h : n + D < m) :
    ∑ k ∈ Finset.range m, (if n ≤ k ∧ k ≤ n + D then g k else 0) =
      ∑ r ∈ Finset.range (D + 1), g (n + r) := by
  rw [← Finset.sum_filter]
  have hfil : (Finset.range m).filter (fun k => n ≤ k ∧ k ≤ n + D) =
      Finset.Ico n (n + D + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfil, Finset.sum_Ico_eq_sum_range, show n + D + 1 - n = D + 1 by omega]

/-- With mask `{i0}` throughout, the charged weight of `m` rounds is the number of rounds whose
S-box input difference is nonzero. -/
theorem scheduledWeight_eq_card_filter {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K}
    {i0 : Idx} (m : ℕ) (hmask : ∀ j < m, (rounds j).mask = {i0}) :
    scheduledWeight rounds T 0 m = ((Finset.range m).filter (fun j => T j i0 ≠ 0)).card := by
  rw [Finset.card_filter]
  unfold scheduledWeight
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [zero_add, hmask j (Finset.mem_range.mp hj), sboxWeight_singleton]
  by_cases hz : T j i0 = 0 <;> simp [hz]

/-- **Middle bounds from refuted patterns.** Let `ψ`, `γ` be a chain of length `D` for `A` at
`i0` (as in `IsTrail.window_relation`), and suppose no nonzero difference stays inactive through
`m` consecutive rounds (`inactiveSpace A {i0} m = ⊥`). If every nonempty set `S` of fewer than `k`
of the rounds `0, …, m - 1` is refuted by the relations `R_0, …, R_{m-D-1}` with coefficients
`relAlpha ψ i0`, `relBeta γ D`, then every trail through `m` consecutive rounds with linear map
`A` and mask `{i0}`, from a nonzero difference, charges at least `k` S-boxes. -/
theorem MiddleBound.of_relations (A : Module.End K (Idx → K)) (i0 : Idx) (m D k : ℕ)
    (ψ : ℕ → Idx → K) (γ : ℕ → K) (hψ0 : ψ 0 = 0)
    (hstep : ∀ r < D, ∀ v, ψ (r + 1) ⬝ᵥ A v = ψ r ⬝ᵥ Function.update v i0 0 + γ r * v i0)
    (hψD : ∀ j, j ≠ i0 → ψ D j = 0) (hwin : inactiveSpace A {i0} m = ⊥)
    (href : ∀ S : Finset ℕ, S ⊆ Finset.range m → S.Nonempty → S.card < k →
      ∃ c : RelRefutation K, c.Valid (relAlpha ψ i0) (relBeta γ D) m D S) :
    MiddleBound A {i0} m k := by
  intro rounds T hT h0 hlin hmask
  set S := (Finset.range m).filter (fun j => T j i0 ≠ 0) with hSdef
  have hw : scheduledWeight rounds T 0 m = S.card := scheduledWeight_eq_card_filter m hmask
  rw [hw]
  by_contra hlt
  push Not at hlt
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- no active round: the window criterion
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hmem : T 0 ∈ inactiveSpace A {i0} 0 := fun j hj => absurd hj (Nat.not_lt_zero j)
      rw [hwin] at hmem
      exact h0 ((Submodule.mem_bot K).mp hmem)
    · have h1 := MiddleBound.of_inactiveSpace hwin m rounds T hT h0 hlin hmask
      rw [Nat.div_self hm, hw, hS, Finset.card_empty] at h1
      omega
  · obtain ⟨c, hcpos, hc⟩ := href S (Finset.filter_subset _ _) hS hlt
    -- every relation, spread over the rounds `0, …, m - 1`
    have hrel : ∀ n < m - D, ∑ k ∈ Finset.range m, ∑ o : Bool,
        relCoef (relAlpha ψ i0) (relBeta γ D) D n k o * relVar rounds T i0 k o = 0 := by
      intro n hn
      have hwr := hT.window_relation A i0 D n (by omega) (fun j hj => hlin (n + j) (by omega))
        (fun j hj => hmask (n + j) (by omega)) ψ γ hψ0 hstep hψD
      have hspread := sum_range_ite_window (fun j => relAlpha ψ i0 (j - n) * T j i0 +
        relBeta γ D (j - n) * sboxOut rounds T i0 j) (show n + D < m by omega)
      simp only [Nat.add_sub_cancel_left] at hspread
      rw [← hwr, ← hspread]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : n ≤ k ∧ k ≤ n + D
      · simp only [Fintype.sum_bool, relCoef, relVar, if_pos h, if_true, Bool.false_eq_true,
          if_false]
        ring
      · simp [relCoef, h]
    -- the combination `∑ λ_n R_n`
    have hcomb : ∑ k ∈ Finset.range m, ∑ o : Bool,
        (∑ n ∈ Finset.range (m - D), c.lam n * relCoef (relAlpha ψ i0) (relBeta γ D) D n k o) *
          relVar rounds T i0 k o = 0 := by
      have h0' : ∑ n ∈ Finset.range (m - D), c.lam n * ∑ k ∈ Finset.range m, ∑ o : Bool,
          relCoef (relAlpha ψ i0) (relBeta γ D) D n k o * relVar rounds T i0 k o = 0 :=
        Finset.sum_eq_zero fun n hn => by rw [hrel n (Finset.mem_range.mp hn), mul_zero]
      rw [← h0']
      simp only [Finset.mul_sum, Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun n _ => ?_
      ring
    -- the variables of inactive rounds vanish
    have hoff : ∀ j < m, j ∉ S → ∀ o, relVar rounds T i0 j o = 0 := by
      intro j hj hjS o
      have hx : T j i0 = 0 := by
        by_contra hne
        exact hjS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hne⟩)
      cases o
      · simpa [relVar] using hx
      · simpa [relVar] using (hT.sboxOut_eq_zero_iff hj).mpr hx
    rw [← Finset.sum_subset (Finset.filter_subset _ (Finset.range m)) (fun j hj hjS =>
      Finset.sum_eq_zero fun o _ => by rw [hoff j (Finset.mem_range.mp hj) hjS o, mul_zero])]
      at hcomb
    rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun o _ => by rw [hc j hj o]]
      at hcomb
    rw [Finset.sum_eq_single c.pos (fun j _ hj => Finset.sum_eq_zero fun o _ => by
        rw [if_neg (fun h => hj h.1), zero_mul]) (fun h => absurd hcpos h)] at hcomb
    rw [Fintype.sum_eq_single c.out (fun o ho => by rw [if_neg (fun h => ho h.2), zero_mul]),
      if_pos ⟨rfl, rfl⟩, one_mul] at hcomb
    -- so a variable of an active round vanishes
    have hposS := Finset.mem_filter.mp hcpos
    have hx : T c.pos i0 ≠ 0 := hposS.2
    cases hout : c.out
    · rw [hout] at hcomb
      exact hx (by simpa [relVar] using hcomb)
    · rw [hout] at hcomb
      exact hx ((hT.sboxOut_eq_zero_iff (Finset.mem_range.mp hposS.1)).mp
        (by simpa [relVar] using hcomb))

/-! ### Witness trails -/

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- Rounds that all have the linear map `L` and the mask `{i0}`, with identity S-boxes and zero
constants. `IsTrail` sees only the masks and the linear maps. -/
def constRounds (L : (Idx → K) ≃ₗ[K] (Idx → K)) (i0 : Idx) : ℕ → RoundSpec Idx K :=
  fun _ => ⟨{i0}, fun _ => Equiv.refl K, L, 0⟩

/-- **A trail from its S-box outputs.** If `L (T n with coordinate i0 replaced by y n) = T (n + 1)`
and `y n = 0 ↔ T n i0 = 0` for every `n < m`, then `T` is a trail through `m` rounds with linear map
`L` and mask `{i0}`. -/
theorem isTrail_of_updates (L : (Idx → K) ≃ₗ[K] (Idx → K)) (i0 : Idx) (T : ℕ → Idx → K)
    (y : ℕ → K) (m : ℕ) (hstep : ∀ n < m, L (Function.update (T n) i0 (y n)) = T (n + 1))
    (hy : ∀ n < m, (y n = 0 ↔ T n i0 = 0)) : IsTrail (constRounds L i0) T m := by
  intro n hn
  refine ⟨Function.update (T n) i0 (y n), ?_, hstep n hn, fun i hi => ?_⟩
  · ext i
    by_cases hi : i = i0
    · subst hi
      simp only [mem_activePattern, Function.update_self]
      exact not_congr (hy n hn)
    · simp [mem_activePattern, Function.update_of_ne hi]
  · exact Function.update_of_ne (by simpa [constRounds] using hi) _ _

end Bound

/-! ### What a passing check means -/

namespace RelationCheck

variable {p : ℕ}

/-- The list sum of the checker is the `Finset` sum over `range n`. -/
theorem lsum_eq (n : ℕ) (f : ℕ → ZMod p) : lsum p n f = ∑ i ∈ Finset.range n, f i := by
  unfold lsum
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A passing `all` over `List.range n` holds at every `i < n`. -/
theorem of_all_range {n : ℕ} {f : ℕ → Bool} (h : (List.range n).all f = true) :
    ∀ i < n, f i = true := by
  intro i hi
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

/-- The vector of `ZMod p` with `t` coordinates read from a list of naturals. -/
def vec (p t : ℕ) (v : List ℕ) : Fin t → ZMod p :=
  fun k => ent p v k

/-- The refutation encoded by `cert = [pos, out, λ_0, λ_1, …]`; `out` is `true` exactly when the
entry is `1`. -/
def certOf (p : ℕ) (cert : List ℕ) : RelRefutation (ZMod p) :=
  ⟨cert.getD 0 0, cert.getD 1 0 == 1, fun n => ent p cert (n + 2)⟩

/-- **`checkDiagJ` checks `(diag d + J) u = w`.** -/
theorem checkDiagJ_spec {t : ℕ} {d : List ℕ} {u w : ℕ → ZMod p}
    (h : checkDiagJ p t d u w = true) :
    Poseidon2.diagPlusOnes (1 : ZMod p) (vec p t d) (fun k : Fin t => u k) =
      fun k : Fin t => w k := by
  funext k
  have hk := of_all_range h k k.isLt
  simp only [decide_eq_true_eq] at hk
  rw [Poseidon2.diagPlusOnes_apply, one_mul, ← hk, lsum_eq, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- **`checkChain` checks a chain** for `diag d + J` at `i0`: row `0` is zero, `(diag d + J)`
maps row `r + 1` to row `r` with coordinate `i0` replaced by `γ_r`, and row `D` vanishes off
`i0`. -/
theorem checkChain_spec {t i0 D : ℕ} {d : List ℕ} {psi : List (List ℕ)} {gamma : List ℕ}
    (hi0 : i0 < t) (h : checkChain p t i0 D d psi gamma = true) :
    vec p t (row psi 0) = 0 ∧
    (∀ r < D, Poseidon2.diagPlusOnes (1 : ZMod p) (vec p t d) (vec p t (row psi (r + 1))) =
      Function.update (vec p t (row psi r)) ⟨i0, hi0⟩ (ent p gamma r)) ∧
    (∀ j : Fin t, j ≠ ⟨i0, hi0⟩ → vec p t (row psi D) j = 0) := by
  simp only [checkChain, Bool.and_eq_true] at h
  obtain ⟨⟨h0, hstep⟩, hD⟩ := h
  refine ⟨funext fun k => ?_, fun r hr => ?_, fun j hj => ?_⟩
  · simpa [vec] using of_all_range h0 k k.isLt
  · refine (checkDiagJ_spec (of_all_range hstep r hr)).trans ?_
    funext k
    by_cases hk : k = ⟨i0, hi0⟩
    · subst hk
      simp
    · have hk' : (k : ℕ) ≠ i0 := fun h => hk (Fin.ext h)
      simp [Function.update_of_ne hk, hk', vec]
  · have hj' : (j : ℕ) ≠ i0 := fun h => hj (Fin.ext h)
    simpa [hj', vec] using of_all_range hD j j.isLt

/-- **`checkRefutation` checks a refutation** of the pattern `S` with coefficients `α`, `β`. -/
theorem checkRefutation_spec {α β : ℕ → ZMod p} {m D : ℕ} {S cert : List ℕ}
    (h : checkRefutation p α β m D S cert = true) :
    (certOf p cert).Valid α β m D S.toFinset := by
  simp only [checkRefutation, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hpos, hall⟩ := h
  refine ⟨List.mem_toFinset.mpr hpos, fun k hk o => ?_⟩
  have hk' := hall k (List.mem_toFinset.mp hk)
  have ho := hk' o (by cases o <;> simp)
  rw [lsum_eq] at ho
  exact ho

/-- **`checkPairs` checks refutations of every pattern of one or two rounds.** -/
theorem checkPairs_spec {α β : ℕ → ZMod p} {m D : ℕ} {singles : List (List ℕ)}
    {pairs : List (List (List ℕ))} (h : checkPairs p α β m D singles pairs = true) :
    (∀ x < m, (certOf p (row singles x)).Valid α β m D {x}) ∧
    (∀ x y, x < y → y < m →
      (certOf p ((pairs.getD x []).getD (y - x - 1) [])).Valid α β m D {x, y}) := by
  simp only [checkPairs, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => ?_, fun x y hxy hy => ?_⟩
  · simpa using checkRefutation_spec (of_all_range h1 x hx)
  · have hc := checkRefutation_spec (of_all_range (of_all_range h2 x (by omega)) (y - x - 1)
      (by omega))
    rw [show x + 1 + (y - x - 1) = y by omega] at hc
    simpa using hc

/-- **A passing relation certificate is a chain and a set of refutations.** -/
theorem checkAll_spec {t i0 m D : ℕ} {d : List ℕ} {psi : List (List ℕ)} {gamma : List ℕ}
    {singles : List (List ℕ)} {pairs : List (List (List ℕ))}
    (h : checkAll p t i0 m D d psi gamma singles pairs = true) :
    checkChain p t i0 D d psi gamma = true ∧
    checkPairs p (alpha p psi i0) (beta p gamma D) m D singles pairs = true := by
  simpa [checkAll] using h

/-- **`checkTrail` checks a trail** through `m` rounds with linear map `diag d + J` and S-box
coordinate `i0`: `(diag d + J)` applied to row `n` of `Ts` with coordinate `i0` replaced by
`y_n` is row `n + 1`, and `y_n = 0` exactly when coordinate `i0` of row `n` is `0`. -/
theorem checkTrail_spec {t i0 m : ℕ} {d : List ℕ} {Ts : List (List ℕ)} {ys : List ℕ}
    (hi0 : i0 < t) (h : checkTrail p t i0 m d Ts ys = true) :
    (∀ n < m, Poseidon2.diagPlusOnes (1 : ZMod p) (vec p t d)
      (Function.update (vec p t (row Ts n)) ⟨i0, hi0⟩ (ent p ys n)) =
        vec p t (row Ts (n + 1))) ∧
    (∀ n < m, (ent p ys n = 0 ↔ vec p t (row Ts n) ⟨i0, hi0⟩ = 0)) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have hn' := of_all_range h n hn
    simp only [Bool.and_eq_true] at hn'
    have hc := checkDiagJ_spec hn'.1
    have hu : (fun k : Fin t => if (k : ℕ) = i0 then ent p ys n else ent p (row Ts n) k) =
        Function.update (vec p t (row Ts n)) ⟨i0, hi0⟩ (ent p ys n) := by
      funext k
      by_cases hk : k = ⟨i0, hi0⟩
      · subst hk
        simp
      · have hk' : (k : ℕ) ≠ i0 := fun h => hk (Fin.ext h)
        simp [Function.update_of_ne hk, hk', vec]
    rw [← hu, hc]
    rfl
  · have hn' := of_all_range h n hn
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_decide] at hn'
    exact hn'.2

end RelationCheck

/-! ### The certificate for `diag d + J` over a prime field -/

section Instance

variable {Idx K : Type*} [Fintype Idx] [Field K]

/-- For the symmetric map `diag d + J`, a chain step is an equation between vectors:
`(diag d + J) ψ' = ψ` with coordinate `i0` replaced by `γ`. -/
theorem chainStep_of_diagPlusOnes [DecidableEq Idx] {d ψ ψ' : Idx → K} {i0 : Idx} {γ : K}
    (h : Poseidon2.diagPlusOnes (1 : K) d ψ' = Function.update ψ i0 γ) (v : Idx → K) :
    ψ' ⬝ᵥ Poseidon2.diagPlusOnes (1 : K) d v = ψ ⬝ᵥ Function.update v i0 0 + γ * v i0 := by
  rw [← Poseidon2.diagPlusOnes_dotProduct, h, update_dotProduct]

/-- **A passing relation certificate gives the middle bound `3`.** Let `p` be prime, `d` a
diagonal over `ZMod p` whose entries are those of the list `dL`, and suppose no nonzero
difference stays inactive through `m` consecutive rounds with `diag d + J` and the S-box at `i0`.
If `RelationCheck.checkAll p t i0 m D dL psi gamma singles pairs = true` (the rows of `psi` and the
entries of `gamma` are a chain of length `D` for `diag d + J` at `i0`, and `singles` and `pairs`
refute every pattern of one or two of the rounds `0, …, m - 1` with its `m - D` relations), then
every trail through `m` consecutive rounds with linear map `diag d + J` and mask `{i0}`, from a
nonzero difference, charges at least `3` S-boxes. -/
theorem MiddleBound.of_relationCheck {p : ℕ} [Fact p.Prime] {t : ℕ} (d : Fin t → ZMod p)
    (i0 : Fin t) (m D : ℕ) (dL : List ℕ) (psi : List (List ℕ)) (gamma : List ℕ)
    (singles : List (List ℕ)) (pairs : List (List (List ℕ)))
    (hd : ∀ k : Fin t, d k = RelationCheck.ent p dL k)
    (hcheck : RelationCheck.checkAll p t i0 m D dL psi gamma singles pairs = true)
    (hwin : inactiveSpace (Poseidon2.diagPlusOnes (1 : ZMod p) d) {i0} m = ⊥) :
    MiddleBound (Poseidon2.diagPlusOnes (1 : ZMod p) d) {i0} m 3 := by
  obtain ⟨hchain, hpairs⟩ := RelationCheck.checkAll_spec hcheck
  obtain ⟨h0, hstep, hD⟩ := RelationCheck.checkChain_spec i0.isLt hchain
  have hdv : d = RelationCheck.vec p t dL := funext hd
  subst hdv
  obtain ⟨hs1, hs2⟩ := RelationCheck.checkPairs_spec hpairs
  refine MiddleBound.of_relations _ i0 m D 3
    (fun r => RelationCheck.vec p t (RelationCheck.row psi r))
    (fun r => RelationCheck.ent p gamma r) h0
    (fun r hr v => chainStep_of_diagPlusOnes (hstep r hr) v) hD hwin ?_
  exact refutations_of_pairs _ _ hs1 hs2

/-- **An explicit trail refutes a middle bound.** Let `L` be a linear equivalence whose linear
map is `diag d + J` over `ZMod p`, with `d` read from the list `dL`. If
`RelationCheck.checkTrail p t i0 m dL Ts ys = true`, row `0` of `Ts` is nonzero, and fewer than `μ`
of the rows `0, …, m - 1` have a nonzero coordinate `i0`, then `MiddleBound (diag d + J) {i0} m μ`
fails: the rows of `Ts` are a trail through `m` rounds that charges fewer than `μ` S-boxes. -/
theorem MiddleBound.not_of_checkTrail {p : ℕ} [Fact p.Prime] {t : ℕ} (d : Fin t → ZMod p)
    (i0 : Fin t) (m μ : ℕ) (dL : List ℕ) (Ts : List (List ℕ)) (ys : List ℕ)
    (L : (Fin t → ZMod p) ≃ₗ[ZMod p] (Fin t → ZMod p))
    (hL : (L : Module.End (ZMod p) (Fin t → ZMod p)) = Poseidon2.diagPlusOnes (1 : ZMod p) d)
    (hd : ∀ k : Fin t, d k = RelationCheck.ent p dL k)
    (hcheck : RelationCheck.checkTrail p t i0 m dL Ts ys = true)
    (h0 : RelationCheck.vec p t (RelationCheck.row Ts 0) ≠ 0)
    (hcount : ((Finset.range m).filter
      (fun n => RelationCheck.ent p (RelationCheck.row Ts n) i0 ≠ 0)).card < μ) :
    ¬ MiddleBound (Poseidon2.diagPlusOnes (1 : ZMod p) d) {i0} m μ := by
  intro hμ
  obtain ⟨hstep, hy⟩ := RelationCheck.checkTrail_spec i0.isLt hcheck
  have hdv : d = RelationCheck.vec p t dL := funext hd
  subst hdv
  have hL' : ∀ v, L v = Poseidon2.diagPlusOnes (1 : ZMod p) (RelationCheck.vec p t dL) v :=
    fun v => by rw [← hL]; rfl
  have hT := isTrail_of_updates L i0 (fun n => RelationCheck.vec p t (RelationCheck.row Ts n))
    (fun n => RelationCheck.ent p ys n) m (fun n hn => by rw [hL']; exact hstep n hn) hy
  have h := hμ (constRounds L i0) _ hT h0 (fun j _ => hL) (fun j _ => rfl)
  rw [scheduledWeight_eq_card_filter m (fun j _ => rfl)] at h
  exact absurd h (not_le.mpr hcount)

end Instance

end Hades
