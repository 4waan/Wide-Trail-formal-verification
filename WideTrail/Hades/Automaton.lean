/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.WindowRelation
import WideTrail.Hades.AutomatonCheck

/-!
# Forward-space automata: middle bounds from a finite certificate

`Hades.MiddleBound A {i0} m μ` says that every trail (`IsTrail`) through `m` consecutive rounds
with linear map `A` and one S-box, at the coordinate `i0`, starting from a nonzero difference,
charges at least `μ` S-boxes. This file proves such bounds from a finite automaton that follows the
set of differences a trail can have when it enters each round.

## The certificate

A `SpaceAutomaton` has states `0, …, N - 1`; state `q` has a set `space q` of differences, a
potential `pot q`, a depth `depth q`, and an optional successor `next q a` for an inactive
(`a = false`) and an active (`a = true`) round. It is valid for `A`, `i0` and `m`
(`SpaceAutomaton.Valid`) when the start state is a state, has depth `0` and contains every
difference, and every state `q` of depth less than `m` satisfies:

* inactive round: if `next q false = some q'`, then `q' < N`, `depth q' ≤ depth q + 1`,
  `pot q' + 1 ≤ pot q`, and `A v ∈ space q'` for every `v ∈ space q` with `v i0 = 0`; if
  `next q false = none`, the only `v ∈ space q` with `v i0 = 0` is `0`;
* active round: if `next q true = some q'`, then `q' < N`, `depth q' ≤ depth q + 1`,
  `pot q' ≤ pot q + 1`, and `A (v with coordinate i0 replaced by y) ∈ space q'` for every
  `v ∈ space q` and every `y`; if `next q true = none`, every `v ∈ space q` has `v i0 = 0`.

## Results

* `MiddleBound.of_automaton` (Theorem A): a valid automaton gives
  `MiddleBound A {i0} m ((m + 1 - pot start) / 2)`. Along a trail, the state reached after `n`
  rounds has depth at most `n` and contains the difference entering round `n`, so no transition
  to `none` is taken (it would make that difference `0`, or an active round inactive), and
  `pot + n ≤ pot start + 2 · (active rounds among the first n)`. With `n = m` and `pot ≥ 0`,
  `m ≤ pot start + 2 s` for the number `s` of active rounds.
* `AutomatonCheck.checkAll_spec`: over `ZMod p`, `p` prime, a list of states that passes the
  Boolean checker `AutomatonCheck.checkAll` of `WideTrail.Hades.AutomatonCheck` is a valid
  automaton (`AutomatonCheck.toAutomaton`) for every `A` that acts as the matrix of the checked
  table (`AutomatonCheck.mat`). State `q` stands for the differences on which every functional of
  its list vanishes; the coefficient lists of the certificate show that each set is carried into
  the next one, and the checker itself checks that successors are states, that depths grow by at
  most one, and that the start state has no functional and depth `0`.
* `MiddleBound.of_automatonCheck`: the two together.
* `isTrail_of_checkHadesTrail`, `scheduledWeight_eq_trailWeight`: an explicit trail through a
  whole schedule `hadesSchedule r m s {i0} …` whose linear maps act as two checked matrices,
  checked by `AutomatonCheck.checkHadesTrail`, satisfies `IsTrail`, and its charged weight is
  `AutomatonCheck.trailWeight`. This is used to show that a total count is attained by some trail
  in the `IsTrail` model.

## What is not claimed

The bounds are lower bounds on charged S-boxes in the `IsTrail` model, which records only
supports, the mask and the linear map; nothing is said here about probabilities, keys or actual
input pairs (those follow from a middle bound through `WideTrail.Hades.MiddleBound`). Only the
direction "certificate implies bound" is proved: a failing check, or the absence of a
certificate, says nothing about the matrix. The trails of `isTrail_of_checkHadesTrail` are trails
in the `IsTrail` model; they are not claimed to be realised by any input pair or key.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Hades

/-! ### The certificate and Theorem A -/

/-- A forward-space automaton: states `0, …, N - 1`, each with a set of differences, a potential,
a depth, and an optional successor for an inactive (`false`) and an active (`true`) round. -/
structure SpaceAutomaton (Idx K : Type*) where
  /-- The number of states. -/
  N : ℕ
  /-- The start state. -/
  start : ℕ
  /-- The differences that state `q` stands for. -/
  space : ℕ → Set (Idx → K)
  /-- The potential. -/
  pot : ℕ → ℕ
  /-- The depth: transitions are checked only for states of depth less than the window. -/
  depth : ℕ → ℕ
  /-- The successor after an inactive (`false`) or an active (`true`) round; `none` when no trail
  has such a round there. -/
  next : ℕ → Bool → Option ℕ

namespace SpaceAutomaton

variable {Idx K : Type*} [DecidableEq Idx] [Field K]

/-- The inactive transition of state `q` is valid for the linear map `A` and the S-box at `i0`.
-/
def InactiveValid (𝒜 : SpaceAutomaton Idx K) (A : Module.End K (Idx → K)) (i0 : Idx) (q : ℕ) :
    Prop :=
  (∀ q', 𝒜.next q false = some q' → q' < 𝒜.N ∧ 𝒜.depth q' ≤ 𝒜.depth q + 1 ∧
    𝒜.pot q' + 1 ≤ 𝒜.pot q ∧ ∀ v ∈ 𝒜.space q, v i0 = 0 → A v ∈ 𝒜.space q') ∧
  (𝒜.next q false = none → ∀ v ∈ 𝒜.space q, v i0 = 0 → v = 0)

/-- The active transition of state `q` is valid for the linear map `A` and the S-box at `i0`. -/
def ActiveValid (𝒜 : SpaceAutomaton Idx K) (A : Module.End K (Idx → K)) (i0 : Idx) (q : ℕ) :
    Prop :=
  (∀ q', 𝒜.next q true = some q' → q' < 𝒜.N ∧ 𝒜.depth q' ≤ 𝒜.depth q + 1 ∧
    𝒜.pot q' ≤ 𝒜.pot q + 1 ∧ ∀ v ∈ 𝒜.space q, ∀ y : K, A (Function.update v i0 y) ∈ 𝒜.space q') ∧
  (𝒜.next q true = none → ∀ v ∈ 𝒜.space q, v i0 = 0)

/-- **A valid automaton** for `m` rounds with linear map `A` and the S-box at `i0`: the start
state is a state of depth `0` that contains every difference, and every state of depth less than
`m` has valid transitions. -/
def Valid (𝒜 : SpaceAutomaton Idx K) (A : Module.End K (Idx → K)) (i0 : Idx) (m : ℕ) : Prop :=
  𝒜.start < 𝒜.N ∧ 𝒜.depth 𝒜.start = 0 ∧ (∀ v, v ∈ 𝒜.space 𝒜.start) ∧
  ∀ q < 𝒜.N, 𝒜.depth q < m → 𝒜.InactiveValid A i0 q ∧ 𝒜.ActiveValid A i0 q

end SpaceAutomaton

section TheoremA

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- **Theorem A: a valid automaton gives a middle bound.** If `𝒜` is a valid automaton for `m`
rounds with linear map `A` and the S-box at `i0`, then every trail through `m` consecutive rounds
with linear map `A` and mask `{i0}`, from a nonzero difference, charges at least
`(m + 1 - pot start) / 2` S-boxes. -/
theorem MiddleBound.of_automaton (A : Module.End K (Idx → K)) (i0 : Idx) (m : ℕ)
    (𝒜 : SpaceAutomaton Idx K) (h𝒜 : 𝒜.Valid A i0 m) :
    MiddleBound A {i0} m ((m + 1 - 𝒜.pot 𝒜.start) / 2) := by
  obtain ⟨hs, hd0, hsp0, hstep⟩ := h𝒜
  intro rounds T hT h0 hlin hmask
  rw [scheduledWeight_eq_card_filter m hmask]
  have hact : ∀ n, ((Finset.range (n + 1)).filter (fun j => T j i0 ≠ 0)).card =
      ((Finset.range n).filter (fun j => T j i0 ≠ 0)).card + if T n i0 = 0 then 0 else 1 := by
    intro n
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hx : T n i0 = 0
    · simp [hx]
    · rw [if_pos hx, Finset.card_insert_of_notMem (by simp), if_neg hx]
  have key : ∀ n ≤ m, ∃ q < 𝒜.N, 𝒜.depth q ≤ n ∧ T n ∈ 𝒜.space q ∧
      𝒜.pot q + n ≤ 𝒜.pot 𝒜.start + 2 * ((Finset.range n).filter (fun j => T j i0 ≠ 0)).card := by
    intro n hn
    induction n with
    | zero => exact ⟨𝒜.start, hs, by omega, hsp0 _, by simp⟩
    | succ n ih =>
      obtain ⟨q, hq, hdq, hTq, hpq⟩ := ih (by omega)
      obtain ⟨⟨hI, hI0⟩, ⟨hA, hA0⟩⟩ := hstep q hq (by omega)
      have hsucc := hT.succ_eq_update (n := n) (by omega) (hmask n (by omega))
      have hlin' : ∀ v, (rounds n).lin v = A v := fun v => by
        rw [← hlin n (by omega)]
        rfl
      rw [hact n]
      by_cases hx : T n i0 = 0
      · rw [if_pos hx]
        cases hnext : 𝒜.next q false with
        | none => exact absurd (hI0 hnext _ hTq hx) (hT.ne_zero h0 n (by omega))
        | some q' =>
          obtain ⟨hq', hd', hp', hmap⟩ := hI q' hnext
          refine ⟨q', hq', by omega, ?_, by omega⟩
          have hy : sboxOut rounds T i0 n = 0 := (hT.sboxOut_eq_zero_iff (by omega)).mpr hx
          rw [hsucc, hy, Function.update_eq_self_iff.mpr hx.symm, hlin']
          exact hmap _ hTq hx
      · rw [if_neg hx]
        cases hnext : 𝒜.next q true with
        | none => exact absurd (hA0 hnext _ hTq) hx
        | some q' =>
          obtain ⟨hq', hd', hp', hmap⟩ := hA q' hnext
          refine ⟨q', hq', by omega, ?_, by omega⟩
          rw [hsucc, hlin']
          exact hmap _ hTq _
  obtain ⟨q, -, -, -, hpq⟩ := key m le_rfl
  omega

end TheoremA

/-! ### What a passing check means -/

namespace AutomatonCheck

open RelationCheck (ent row lsum vec lsum_eq of_all_range)

variable {p : ℕ}

/-- The matrix of a table of rows: entry `(i, k)` is entry `k` of row `i`. -/
def mat (p t : ℕ) (M : List (List ℕ)) : Matrix (Fin t) (Fin t) (ZMod p) :=
  fun i k => ent p (row M i) k

/-- The automaton of a list of states: state `q` stands for the differences on which every
functional of its list `H` vanishes; potentials, depths and successors are read from the list. -/
def toAutomaton (p t start : ℕ) (states : List AState) : SpaceAutomaton (Fin t) (ZMod p) where
  N := states.length
  start := start
  space q := {v | ∀ j, vec p t (row (get states q).H j) ⬝ᵥ v = 0}
  pot q := (get states q).pot
  depth q := (get states q).depth
  next q a := bif a then (get states q).next1 else (get states q).next0

/-- The list sum of the checker is the `Finset` sum over `range n`. -/
theorem nsum_eq (n : ℕ) (f : ℕ → ℕ) : nsum n f = ∑ i ∈ Finset.range n, f i := by
  unfold nsum
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A row past the end of a table is `[]`. -/
theorem row_of_le {tab : List (List ℕ)} {j : ℕ} (h : tab.length ≤ j) : row tab j = [] := by
  rw [row, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-- The vector of the empty list is `0`. -/
theorem vec_nil (t : ℕ) : vec p t [] = 0 := by
  funext k
  simp [vec, ent]

/-- To lie in the set of a state, it suffices that the functionals of its list vanish: the rows
past the end are `[]`. -/
theorem forall_row_of_lt {t : ℕ} {hs : List (List ℕ)} {w : Fin t → ZMod p}
    (h : ∀ j < hs.length, vec p t (row hs j) ⬝ᵥ w = 0) (j : ℕ) : vec p t (row hs j) ⬝ᵥ w = 0 := by
  by_cases hj : j < hs.length
  · exact h j hj
  · rw [row_of_le (not_lt.mp hj), vec_nil, zero_dotProduct]

/-- `comp` is the row vector times the matrix. -/
theorem vecMul_mat (t : ℕ) (M : List (List ℕ)) (h : List ℕ) :
    Matrix.vecMul (vec p t h) (mat p t M) = fun k : Fin t => comp p t M h k := by
  funext k
  simp only [Matrix.vecMul, dotProduct, comp, lsum_eq, vec, mat]
  exact Fin.sum_univ_eq_sum_range (fun i => ent p h i * ent p (row M i) k) t

/-- The functional of `h` after the matrix is the functional of `comp`. -/
theorem dotProduct_mat_mulVec (t : ℕ) (M : List (List ℕ)) (h : List ℕ) (v : Fin t → ZMod p) :
    vec p t h ⬝ᵥ (mat p t M).mulVec v = (fun k : Fin t => comp p t M h k) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, vecMul_mat]

/-- **`checkComb` checks a combination**: if `target = ∑_j c_j hs_j + ce e_{i0}` on the first `t`
coordinates and every functional of `hs` vanishes on `v`, then `target ⬝ v = ce * v i0`. -/
theorem checkComb_spec {t : ℕ} {i0 : Fin t} {hs : List (List ℕ)} {target : ℕ → ZMod p}
    {c : List ℕ} {ce : ZMod p} (h : checkComb p t i0 hs target c ce = true)
    (v : Fin t → ZMod p) (hv : ∀ j, vec p t (row hs j) ⬝ᵥ v = 0) :
    (fun k : Fin t => target k) ⬝ᵥ v = ce * v i0 := by
  have hk : ∀ k : Fin t, target k = ∑ j ∈ Finset.range hs.length,
      ent p c j * ent p (row hs j) k + if k = i0 then ce else 0 := by
    intro k
    have hk := of_all_range h k k.isLt
    simp only [decide_eq_true_eq, lsum_eq, Fin.val_inj] at hk
    exact hk
  have hsum : ∀ j ∈ Finset.range hs.length,
      ∑ k : Fin t, ent p c j * ent p (row hs j) k * v k = 0 := by
    intro j _
    have hj := hv j
    simp only [dotProduct, vec] at hj
    simp only [mul_assoc, ← Finset.mul_sum, hj, mul_zero]
  simp only [dotProduct, hk, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_eq_zero hsum, zero_add]
  simp [ite_mul]

/-- **A passing automaton certificate is a valid automaton.** Over `ZMod p`, `p` prime, if
`checkAll p t i0 m M start states = true` and `A` acts as the matrix of `M`, then
`toAutomaton p t start states` is a valid automaton for `m` rounds with linear map `A` and the
S-box at `i0`. -/
theorem checkAll_spec [Fact p.Prime] {t m start : ℕ} {i0 : Fin t} {M : List (List ℕ)}
    {states : List AState} (A : Module.End (ZMod p) (Fin t → ZMod p))
    (hA : ∀ v, A v = (mat p t M).mulVec v) (h : checkAll p t i0 m M start states = true) :
    (toAutomaton p t start states).Valid A i0 m := by
  simp only [checkAll, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hs, hH⟩, hd⟩, hall⟩ := h
  refine ⟨hs, hd, fun v j => ?_, fun q hq hdq => ?_⟩
  · change vec p t (row (get states start).H j) ⬝ᵥ v = 0
    rw [hH, row_of_le (by simp), vec_nil, zero_dotProduct]
  have hq' := of_all_range hall q hq
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true]
    at hq'
  rcases hq' with hlt | ⟨hI, hAct⟩
  · exact absurd hdq hlt
  refine ⟨⟨fun q' hnext => ?_, fun hnext v hv hv0 => ?_⟩,
    ⟨fun q' hnext => ?_, fun hnext v hv => ?_⟩⟩
  · -- an inactive transition
    change (get states q).next0 = some q' at hnext
    simp only [checkInactive, hnext, Bool.and_eq_true, decide_eq_true_eq] at hI
    obtain ⟨⟨⟨hq'N, hdep⟩, hpot⟩, hcomb⟩ := hI
    refine ⟨hq'N, hdep, hpot, fun v hv hv0 => ?_⟩
    refine forall_row_of_lt (fun j hj => ?_)
    rw [hA, dotProduct_mat_mulVec, checkComb_spec (of_all_range hcomb j hj) v hv, hv0, mul_zero]
  · -- no inactive transition
    change (get states q).next0 = none at hnext
    simp only [checkInactive, hnext] at hI
    funext k
    have hk := checkComb_spec (of_all_range hI k k.isLt) v hv
    rw [hv0, mul_zero] at hk
    simpa [dotProduct, Fin.val_inj] using hk
  · -- an active transition
    change (get states q).next1 = some q' at hnext
    simp only [checkActive, hnext, Bool.and_eq_true, decide_eq_true_eq] at hAct
    obtain ⟨⟨⟨hq'N, hdep⟩, hpot⟩, hcomb⟩ := hAct
    refine ⟨hq'N, hdep, hpot, fun v hv y => ?_⟩
    refine forall_row_of_lt (fun j hj => ?_)
    obtain ⟨hzero, hc⟩ := Bool.and_eq_true_iff.mp (of_all_range hcomb j hj)
    rw [decide_eq_true_eq] at hzero
    have hupd : (fun k : Fin t => comp p t M (row (get states q').H j) k) ⬝ᵥ
        Function.update v i0 y =
        (fun k : Fin t => comp p t M (row (get states q').H j) k) ⬝ᵥ v := by
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = i0
      · subst hk
        simp [hzero]
      · rw [Function.update_of_ne hk]
    rw [hA, dotProduct_mat_mulVec, hupd, checkComb_spec hc v hv, zero_mul]
  · -- no active transition
    change (get states q).next1 = none at hnext
    simp only [checkActive, hnext] at hAct
    have hk := checkComb_spec hAct v hv
    rw [zero_mul] at hk
    simpa [dotProduct, Fin.val_inj] using hk

end AutomatonCheck

/-- **A passing automaton certificate gives a middle bound.** Over `ZMod p`, `p` prime, let `A`
act as the matrix of the table `M` (row `i` holds the coefficients of output coordinate `i`). If
`AutomatonCheck.checkAll p t i0 m M start states = true`, then every trail through `m`
consecutive rounds with linear map `A` and mask `{i0}`, from a nonzero difference, charges at least
`(m + 1 - pot) / 2` S-boxes, where `pot` is the potential of the start state. -/
theorem MiddleBound.of_automatonCheck {p : ℕ} [Fact p.Prime] {t : ℕ}
    (A : Module.End (ZMod p) (Fin t → ZMod p)) (i0 : Fin t) (m : ℕ) (M : List (List ℕ))
    (start : ℕ) (states : List AutomatonCheck.AState)
    (hA : ∀ v, A v = (AutomatonCheck.mat p t M).mulVec v)
    (hcheck : AutomatonCheck.checkAll p t i0 m M start states = true) :
    MiddleBound A {i0} m ((m + 1 - (AutomatonCheck.get states start).pot) / 2) :=
  MiddleBound.of_automaton A i0 m _ (AutomatonCheck.checkAll_spec A hA hcheck)

/-! ### Explicit trails through a whole schedule -/

section Schedule

open AutomatonCheck RelationCheck

variable {p : ℕ} [Fact p.Prime] {t : ℕ}

/-- **A checked trail through a whole schedule.** Let the linear maps of the rounds `n < r` and
`r + m ≤ n < r + m + s` act as the matrix of `E`, and those of the rounds `r ≤ n < r + m` as the
matrix of `M`. If `AutomatonCheck.checkHadesTrail p t i0 r m s E M Ts bs = true`, the rows of `Ts`
are a trail through the `r + m + s` rounds of `hadesSchedule r m s {i0} boxes linear values`, for
every choice of S-boxes and constants. -/
theorem isTrail_of_checkHadesTrail (i0 : Fin t) (r m s : ℕ) (E M Ts bs : List (List ℕ))
    (boxes : ℕ → Fin t → ZMod p ≃ ZMod p)
    (linear : ℕ → (Fin t → ZMod p) ≃ₗ[ZMod p] (Fin t → ZMod p)) (values : ℕ → Fin t → ZMod p)
    (hE : ∀ n < r + m + s, (n < r ∨ r + m ≤ n) → ∀ v, linear n v = (mat p t E).mulVec v)
    (hM : ∀ n, r ≤ n → n < r + m → ∀ v, linear n v = (mat p t M).mulVec v)
    (h : checkHadesTrail p t i0 r m s E M Ts bs = true) :
    IsTrail (hadesSchedule r m s {i0} boxes linear values) (fun n => vec p t (row Ts n))
      (r + m + s) := by
  intro n hn
  obtain ⟨hsupp, hmul⟩ := Bool.and_eq_true_iff.mp (of_all_range h n hn)
  refine ⟨vec p t (row bs n), ?_, ?_, ?_⟩
  · ext k
    have hk := Bool.and_eq_true_iff.mp (of_all_range hsupp k k.isLt)
    simp only [beq_iff_eq, decide_eq_decide] at hk
    simp only [mem_activePattern, vec]
    exact not_congr hk.1
  · funext i
    have hi := of_all_range hmul i i.isLt
    rw [decide_eq_true_eq, lsum_eq, ← Fin.sum_univ_eq_sum_range] at hi
    change linear n (vec p t (row bs n)) i = ent p (row Ts (n + 1)) i
    by_cases hf : n < r ∨ r + m ≤ n
    · rw [hE n hn hf, ← hi, if_pos hf]
      rfl
    · rw [hM n (by omega) (by omega), ← hi, if_neg hf]
      rfl
  · intro i hi
    have hfull : ¬ (n < r ∨ r + m ≤ n) := by
      intro hf
      apply hi
      change i ∈ hadesMask r m s {i0} n
      rcases hf with hf | hf
      · simp [hadesMask, hf]
      · simp [hadesMask, show ¬ n < r by omega, show ¬ n < r + m by omega, hn]
    have hmask : i ≠ i0 := by
      intro hii
      apply hi
      change i ∈ hadesMask r m s {i0} n
      simp [hadesMask, show ¬ n < r by omega, show n < r + m by omega, hii]
    have hk := Bool.and_eq_true_iff.mp (of_all_range hsupp i i.isLt)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
    rcases hk.2 with ((hk | hk) | hk) | hk
    · exact absurd (Or.inl hk) hfull
    · exact absurd (Or.inr hk) hfull
    · exact absurd (Fin.ext hk) hmask
    · exact hk

/-- The charged weight of the rows of `Ts` over the rounds of `hadesSchedule r m s {i0} …` is
`AutomatonCheck.trailWeight p t i0 r m s Ts`. -/
theorem scheduledWeight_eq_trailWeight (i0 : Fin t) (r m s : ℕ)
    (Ts : List (List ℕ)) (boxes : ℕ → Fin t → ZMod p ≃ ZMod p)
    (linear : ℕ → (Fin t → ZMod p) ≃ₗ[ZMod p] (Fin t → ZMod p)) (values : ℕ → Fin t → ZMod p) :
    scheduledWeight (hadesSchedule r m s {i0} boxes linear values) (fun n => vec p t (row Ts n)) 0
      (r + m + s) = trailWeight p t i0 r m s Ts := by
  unfold scheduledWeight trailWeight
  rw [nsum_eq]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  rw [zero_add]
  change sboxWeight (hadesMask r m s {i0} n) (vec p t (row Ts n)) = _
  unfold roundWeight
  by_cases hf : n < r ∨ r + m ≤ n
  · have hmask : hadesMask r m s ({i0} : Finset (Fin t)) n = Finset.univ := by
      rcases hf with hf | hf
      · simp [hadesMask, hf]
      · simp [hadesMask, show ¬ n < r by omega, show ¬ n < r + m by omega, hn]
    rw [hmask, sboxWeight_full, if_pos hf, nsum_eq, weight, activePattern, Finset.card_filter,
      ← Fin.sum_univ_eq_sum_range (fun k => if ent p (row Ts n) k = 0 then 0 else 1) t]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [vec]
    by_cases hk : ent p (row Ts n) k = 0 <;> simp [hk]
  · have hmask : hadesMask r m s ({i0} : Finset (Fin t)) n = {i0} := by
      simp [hadesMask, show ¬ n < r by omega, show n < r + m by omega]
    rw [hmask, sboxWeight_singleton, if_neg hf]
    rfl

end Schedule

end Hades
