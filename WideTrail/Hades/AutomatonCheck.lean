/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.RelationCheck

/-!
# A Boolean checker for forward-space automaton certificates

`WideTrail.Hades.Automaton` proves that a valid forward-space automaton for a partial-round
matrix gives a lower bound on the S-boxes charged in the partial rounds (`Hades.MiddleBound`).
This file holds the computational half: Boolean functions on lists of natural numbers, evaluated
in `ZMod p`, that a concrete certificate file decides by `decide +kernel`. It imports only
`WideTrail.Hades.RelationCheck`, which imports only `Mathlib.Data.ZMod.Basic`, so that the kernel
evaluation in a certificate file runs on a small import baseline.

All data are lists of natural numbers, read entry by entry with `List.getD` and cast into
`ZMod p` (`RelationCheck.ent`); an entry past the end of a list reads as `0`, and a row past the
end of a table reads as `[]`. A matrix `M` is a list of rows; row `i` holds the coefficients of
output coordinate `i`, so `M` acts on a column vector `v` by `(M v)_i = ∑_k M_{i k} v_k`.

## The automaton

An automaton is a list `states` of `AState`s, numbered from `0`. State `q` stands for the set of
differences `v` with `h ⬝ v = 0` for every functional `h` of its list `H` (each a list of `t`
entries). It carries a potential `pot`, a depth `depth`, an optional successor for an inactive
round (`next0`) and for an active round (`next1`), and coefficient lists `coef0`, `coef1` that
witness the transitions.

* `comp p t M h k`: coordinate `k` of the row vector `h` times `M`, `∑_{i < t} h_i M_{i k}`, the
  functional `v ↦ h ⬝ (M v)`.
* `checkComb p t i0 hs target c ce`: on the first `t` coordinates,
  `target = ∑_{j < |hs|} c_j hs_j + ce e_{i0}`, where `hs_j` is row `j` of `hs`.
* `checkInactive`: if `next0 = some q'`, then `q' < |states|`, `depth q' ≤ depth q + 1`,
  `pot q' + 1 ≤ pot q`, and for every functional `h'` (row `j`) of state `q'`,
  `h' ∘ M = ∑_l c_l h_l + c_e e_{i0}` with `c = coef0` row `j` and `c_e` its entry `|H q|`. If
  `next0 = none`, every unit functional `e_k` (`k < t`) is such a combination (row `k` of
  `coef0`).
* `checkActive`: if `next1 = some q'`, then `q' < |states|`, `depth q' ≤ depth q + 1`,
  `pot q' ≤ pot q + 1`, and for every functional `h'` (row `j`) of state `q'`, coordinate `i0`
  of `h' ∘ M` is `0` and `h' ∘ M = ∑_l c_l h_l` with `c = coef1` row `j`. If `next1 = none`,
  `e_{i0} = ∑_l c_l h_l` with `c = coef1` row `0`.
* `checkAll p t i0 m M start states`: `start < |states|`, the start state has no functional and
  depth `0`, and every state of depth less than `m` passes `checkInactive` and `checkActive`.

## Explicit trails through a whole schedule

* `checkHadesTrail p t i0 r m s E M Ts bs`: the rows `T_0, …, T_{r+m+s}` of `Ts` and
  `b_0, …, b_{r+m+s-1}` of `bs` form a trail through `r` full rounds with matrix `E`, `m` partial
  rounds with matrix `M` and the S-box at `i0`, and `s` full rounds with `E`: for every round `n`,
  `b_n` and `T_n` have the same zero coordinates among the first `t`, they agree off `i0` in a
  partial round, and the round's matrix maps `b_n` to `T_{n+1}`.
* `trailWeight p t i0 r m s Ts`: the number of nonzero entries among the first `t` of the rows
  of the full rounds, plus the number of partial rounds whose row has a nonzero entry `i0`.

## What is not claimed

Nothing is proved in this file. The meaning of a passing check is proved in
`WideTrail.Hades.Automaton` (`AutomatonCheck.checkAll_spec`, `Hades.MiddleBound.of_automatonCheck`
and `Hades.isTrail_of_checkHadesTrail`). A failing check proves nothing about the matrix: it only
says that the given data are not a certificate.
-/

set_option autoImplicit false

namespace Hades.AutomatonCheck

open RelationCheck (ent row lsum)

/-- One state of a forward-space automaton, as natural numbers. -/
structure AState where
  /-- The functionals that vanish on the state's set, each a list of `t` entries. -/
  H : List (List ℕ)
  /-- The potential. -/
  pot : ℕ
  /-- The depth: transitions are checked only for states of depth less than the window. -/
  depth : ℕ
  /-- The state after an inactive round; `none` when no trail has an inactive round here. -/
  next0 : Option ℕ
  /-- The state after an active round; `none` when no trail has an active round here. -/
  next1 : Option ℕ
  /-- The coefficients that witness the inactive transition. -/
  coef0 : List (List ℕ)
  /-- The coefficients that witness the active transition. -/
  coef1 : List (List ℕ)
deriving Inhabited

/-- State `q` of the list; the default state (no functional, potential and depth `0`, no
successors) past the end of the list. -/
def get (states : List AState) (q : ℕ) : AState :=
  states.getD q default

variable (p : ℕ)

/-- Coordinate `k` of the row vector `h` times the matrix `M`: `∑_{i < t} h_i M_{i k}`. -/
def comp (t : ℕ) (M : List (List ℕ)) (h : List ℕ) (k : ℕ) : ZMod p :=
  lsum p t fun i => ent p h i * ent p (row M i) k

/-- On the first `t` coordinates, `target = ∑_{j < |hs|} c_j hs_j + ce e_{i0}`. -/
def checkComb (t i0 : ℕ) (hs : List (List ℕ)) (target : ℕ → ZMod p) (c : List ℕ) (ce : ZMod p) :
    Bool :=
  (List.range t).all fun k => decide (target k =
    lsum p hs.length (fun j => ent p c j * ent p (row hs j) k) + if k = i0 then ce else 0)

/-- The inactive transition of the state `s` (see the module docstring). -/
def checkInactive (t i0 : ℕ) (M : List (List ℕ)) (states : List AState) (s : AState) : Bool :=
  match s.next0 with
  | some q' =>
    decide (q' < states.length) && decide ((get states q').depth ≤ s.depth + 1) &&
    decide ((get states q').pot + 1 ≤ s.pot) &&
    (List.range (get states q').H.length).all fun j =>
      checkComb p t i0 s.H (comp p t M (row (get states q').H j)) (row s.coef0 j)
        (ent p (row s.coef0 j) s.H.length)
  | none =>
    (List.range t).all fun k =>
      checkComb p t i0 s.H (fun i => if i = k then 1 else 0) (row s.coef0 k)
        (ent p (row s.coef0 k) s.H.length)

/-- The active transition of the state `s` (see the module docstring). -/
def checkActive (t i0 : ℕ) (M : List (List ℕ)) (states : List AState) (s : AState) : Bool :=
  match s.next1 with
  | some q' =>
    decide (q' < states.length) && decide ((get states q').depth ≤ s.depth + 1) &&
    decide ((get states q').pot ≤ s.pot + 1) &&
    (List.range (get states q').H.length).all fun j =>
      decide (comp p t M (row (get states q').H j) i0 = 0) &&
      checkComb p t i0 s.H (comp p t M (row (get states q').H j)) (row s.coef1 j) 0
  | none =>
    checkComb p t i0 s.H (fun i => if i = i0 then 1 else 0) (row s.coef1 0) 0

/-- The whole automaton certificate for a window of `m` rounds with matrix `M` and the S-box at
`i0`: the start state is a state, has no functional and depth `0`, and every state of depth less
than `m` passes both transition checks. -/
def checkAll (t i0 m : ℕ) (M : List (List ℕ)) (start : ℕ) (states : List AState) : Bool :=
  decide (start < states.length) && (get states start).H.isEmpty &&
  decide ((get states start).depth = 0) &&
  (List.range states.length).all fun q =>
    !decide ((get states q).depth < m) ||
      (checkInactive p t i0 M states (get states q) && checkActive p t i0 M states (get states q))

/-- `f 0 + f 1 + ⋯ + f (n - 1)` in `ℕ`, as a list sum. -/
def nsum (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  ((List.range n).map f).sum

/-- An explicit trail through `r` full rounds with matrix `E`, `m` partial rounds with matrix
`M` and the S-box at `i0`, and `s` full rounds with `E` (see the module docstring). -/
def checkHadesTrail (t i0 r m s : ℕ) (E M : List (List ℕ)) (Ts bs : List (List ℕ)) : Bool :=
  (List.range (r + m + s)).all fun n =>
    (List.range t).all (fun k =>
      (decide (ent p (row bs n) k = 0) == decide (ent p (row Ts n) k = 0)) &&
      (decide (n < r) || decide (r + m ≤ n) || decide (k = i0) ||
        decide (ent p (row bs n) k = ent p (row Ts n) k))) &&
    (List.range t).all fun i =>
      decide (lsum p t (fun k =>
        ent p (row (if n < r ∨ r + m ≤ n then E else M) i) k * ent p (row bs n) k) =
          ent p (row Ts (n + 1)) i)

/-- The charged weight of row `n` of `Ts` in the schedule of `checkHadesTrail`: its number of
nonzero entries among the first `t` in a full round, and `1` or `0` according to its entry `i0`
in a partial round. -/
def roundWeight (t i0 r m : ℕ) (Ts : List (List ℕ)) (n : ℕ) : ℕ :=
  if n < r ∨ r + m ≤ n then nsum t fun k => if ent p (row Ts n) k = 0 then 0 else 1
  else if ent p (row Ts n) i0 = 0 then 0 else 1

/-- The charged weight of the trail `Ts` over the `r + m + s` rounds. -/
def trailWeight (t i0 r m s : ℕ) (Ts : List (List ℕ)) : ℕ :=
  nsum (r + m + s) (roundWeight p t i0 r m Ts)

end Hades.AutomatonCheck
