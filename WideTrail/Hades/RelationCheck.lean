/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.Data.ZMod.Basic

/-!
# A Boolean checker for window-relation certificates

`WideTrail.Hades.WindowRelation` proves that a window-relation certificate for a partial-round
matrix `diag d + J` over a prime field gives a lower bound on the S-boxes charged in the partial
rounds (`Hades.MiddleBound`). This file holds the computational half: Boolean functions on lists
of natural numbers, evaluated in `ZMod p`, that a concrete certificate file decides by
`decide +kernel`. It imports only `Mathlib.Data.ZMod.Basic`, so that the kernel evaluation in a
certificate file runs on a small import baseline.

All data are lists of natural numbers, read entry by entry with `List.getD` and cast into
`ZMod p` (`ent`); an entry past the end of a list reads as `0`.

* `checkDiagJ p t d u w`: for every `k < t`, `d_k * u_k + ∑_{j < t} u_j = w_k`, that is
  `(diag d + J) u = w` on the first `t` coordinates.
* `checkChain p t i0 D d psi gamma`: the rows `ψ_0, …, ψ_D` of `psi` form a Horner chain for
  `diag d + J` at the coordinate `i0`: `ψ_0 = 0`, `(diag d + J) ψ_{r+1}` equals `ψ_r` off `i0`
  and `γ_r` at `i0` for `r < D`, and `ψ_D` vanishes off `i0`.
* `checkRefutation p α β m D S cert`: the certificate `cert = [pos, out, λ_0, λ_1, …]`
  refutes the pattern `S` (a list of round indices): for every `k ∈ S` and both variables
  `o ∈ {false, true}` (input and output of the S-box of round `k`), the combined coefficient
  `∑_{n < m - D} λ_n * coef α β D n k o` is `1` at `(pos, out)` and `0` elsewhere, and
  `pos ∈ S`. Here `out` is read as `true` exactly when the entry is `1`.
* `checkPairs p α β m D singles pairs`: every pattern `[x]` with `x < m` is refuted by row `x` of
  `singles`, and every pattern `[x, y]` with `x < y < m` by entry `y - x - 1` of row `x` of
  `pairs`.
* `checkAll`: `checkChain` and `checkPairs` with the coefficients `alpha`, `beta` of the chain.
* `checkTrail p t i0 m d Ts ys`: the rows `T_0, …, T_m` of `Ts` and the entries `y_0, …` of
  `ys` form a trail through `m` rounds with S-box coordinate `i0` and linear map `diag d + J`:
  `(diag d + J) (T_n with coordinate i0 replaced by y_n) = T_{n+1}`, and `y_n = 0` exactly when
  the coordinate `i0` of `T_n` is `0`.

## What is not claimed

Nothing is proved in this file. The meaning of a passing check, and in particular that
`checkAll … = true` gives a middle bound, is proved in `WideTrail.Hades.WindowRelation`
(`RelationCheck.checkAll_spec` and `Hades.MiddleBound.of_relationCheck`). A failing check proves
nothing about the matrix: it only says that the given data are not a certificate.
-/

set_option autoImplicit false

namespace Hades.RelationCheck

variable (p : ℕ)

/-- Entry `j` of a list of naturals, cast into `ZMod p`; `0` past the end of the list. -/
def ent (v : List ℕ) (j : ℕ) : ZMod p :=
  ((v.getD j 0 : ℕ) : ZMod p)

/-- Row `r` of a table of lists; `[]` past the end of the table. -/
def row (tab : List (List ℕ)) (r : ℕ) : List ℕ :=
  tab.getD r []

/-- `f 0 + f 1 + ⋯ + f (n - 1)`, as a list sum. -/
def lsum (n : ℕ) (f : ℕ → ZMod p) : ZMod p :=
  ((List.range n).map f).sum

/-- `(diag d + J) u = w` on the first `t` coordinates: `d_k * u_k + ∑_{j < t} u_j = w_k` for every
`k < t`. -/
def checkDiagJ (t : ℕ) (d : List ℕ) (u w : ℕ → ZMod p) : Bool :=
  (List.range t).all fun k => decide (ent p d k * u k + lsum p t u = w k)

/-- The Horner chain of a window relation of length `D` for `diag d + J` at the coordinate
`i0`: row `0` of `psi` is zero; for `r < D`, `(diag d + J)` applied to row `r + 1` equals row `r`
off `i0` and `γ_r` at `i0`; row `D` vanishes off `i0`. -/
def checkChain (t i0 D : ℕ) (d : List ℕ) (psi : List (List ℕ)) (gamma : List ℕ) : Bool :=
  (List.range t).all (fun k => decide (ent p (row psi 0) k = 0)) &&
  (List.range D).all (fun r => checkDiagJ p t d (ent p (row psi (r + 1)))
    (fun k => if k = i0 then ent p gamma r else ent p (row psi r) k)) &&
  (List.range t).all (fun k => decide (k = i0) || decide (ent p (row psi D) k = 0))

/-- The input coefficient `α_r` of the window relation: coordinate `i0` of row `r` of `psi`. -/
def alpha (psi : List (List ℕ)) (i0 r : ℕ) : ZMod p :=
  ent p (row psi r) i0

/-- The output coefficient `β_r` of the window relation: `-γ_r` for `r < D`, and `0` from `D`
on. -/
def beta (gamma : List ℕ) (D r : ℕ) : ZMod p :=
  if r < D then -ent p gamma r else 0

/-- The coefficient of variable `(k, o)` in relation `n`: relation `n` covers the rounds
`n, …, n + D`, with coefficient `α (k - n)` on the S-box input (`o = false`) and `β (k - n)` on
the S-box output (`o = true`) of round `k`. -/
def coef (α β : ℕ → ZMod p) (D n k : ℕ) (o : Bool) : ZMod p :=
  if n ≤ k ∧ k ≤ n + D then (if o then β (k - n) else α (k - n)) else 0

/-- The certificate `cert = [pos, out, λ_0, λ_1, …]` refutes the pattern `S`: the combination
`∑_{n < m - D} λ_n R_n` of the relations restricted to the variables of `S` is the single
variable `(pos, out)`, and `pos ∈ S`. -/
def checkRefutation (α β : ℕ → ZMod p) (m D : ℕ) (S cert : List ℕ) : Bool :=
  decide (cert.getD 0 0 ∈ S) &&
  S.all fun k => [false, true].all fun o =>
    decide (lsum p (m - D) (fun n => ent p cert (n + 2) * coef p α β D n k o) =
      if k = cert.getD 0 0 ∧ o = (cert.getD 1 0 == 1) then 1 else 0)

/-- Every pattern with one or two of the rounds `0, …, m - 1` is refuted: `[x]` by row `x` of
`singles`, and `[x, x + 1 + j]` by entry `j` of row `x` of `pairs`. -/
def checkPairs (α β : ℕ → ZMod p) (m D : ℕ) (singles : List (List ℕ))
    (pairs : List (List (List ℕ))) : Bool :=
  (List.range m).all (fun x => checkRefutation p α β m D [x] (row singles x)) &&
  (List.range m).all (fun x => (List.range (m - x - 1)).all fun j =>
    checkRefutation p α β m D [x, x + 1 + j] ((pairs.getD x []).getD j []))

/-- The whole relation certificate: the chain, and refutations of every pattern with one or two
active rounds, with the coefficients of the chain. -/
def checkAll (t i0 m D : ℕ) (d : List ℕ) (psi : List (List ℕ)) (gamma : List ℕ)
    (singles : List (List ℕ)) (pairs : List (List (List ℕ))) : Bool :=
  checkChain p t i0 D d psi gamma &&
  checkPairs p (alpha p psi i0) (beta p gamma D) m D singles pairs

/-- An explicit trail through `m` rounds with linear map `diag d + J` and S-box coordinate `i0`:
for every `n < m`, `(diag d + J)` applied to row `n` of `Ts` with coordinate `i0` replaced by
`y_n` is row `n + 1`, and `y_n = 0` exactly when coordinate `i0` of row `n` is `0`. -/
def checkTrail (t i0 m : ℕ) (d : List ℕ) (Ts : List (List ℕ)) (ys : List ℕ) : Bool :=
  (List.range m).all fun n =>
    checkDiagJ p t d (fun k => if k = i0 then ent p ys n else ent p (row Ts n) k)
      (ent p (row Ts (n + 1))) &&
    (decide (ent p ys n = 0) == decide (ent p (row Ts n) i0 = 0))

end Hades.RelationCheck
