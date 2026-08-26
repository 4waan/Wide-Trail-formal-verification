/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.Activity
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Finset.Sort

/-!
# MDS matrices and the branch-number bound

Mathlib has no linear-code vocabulary at all: no MDS matrices, no minimum distance, no
Singleton bound (checked directly — `Mathlib/InformationTheory/Coding/` covers only
Kraft–McMillan and prefix codes, unrelated to error-correcting codes). This file builds the
one fact this project actually needs from that theory, from first principles: an MDS matrix
gives an optimal branch number.

`IsMDS M` says every square submatrix of `M` — any order `k`, any `k` rows and `k` columns,
chosen without repetition — is nonsingular. `isMDS_branch_bound` is the classical fact that
this makes `{(x, Mx) : x}` an optimal `[2n, n, n+1]` code: any nonzero `(x, Mx)` has at least
`n+1` nonzero coordinates between the two halves. The proof needs no coding-theory framework,
just one linear-algebra argument: if the combined weight were `≤ n`, the complement of `Mx`'s
support has room for a full copy of `x`'s support, giving a square submatrix of `M` that both
kills `x`'s nonzero entries (because `Mx` vanishes there) and is injective (because it's
nonsingular) — forcing those entries to be zero, contradicting that they are, by
definition, the *support* of `x`.
-/

set_option autoImplicit false

open Finset

variable {K : Type*} [Field K] [DecidableEq K] {n : ℕ}

omit [DecidableEq K] in
/-- `M` is MDS: every square submatrix — any order `k`, any `k` rows `Row` and `k` columns
`Col`, indexed via the canonical order-embedding `Finset.orderIsoOfFin` rather than an
arbitrary injection — is nonsingular. (An arbitrary injective selection gives the same
submatrices up to row/column permutation, which changes the determinant by at most a sign, so
this is no less general — and stating it via `Finset`s directly is what makes a *finite*
choice of rows and columns finitely checkable: a concrete instance only has `Nat.choose n k`
choices per side to enumerate, not every injection `Fin k → Fin n`.) -/
def IsMDS (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ (k : ℕ) (Row Col : Finset (Fin n)) (hRow : Row.card = k) (hCol : Col.card = k),
    (M.submatrix (fun i => (Row.orderIsoOfFin hRow i : Fin n))
      (fun j => (Col.orderIsoOfFin hCol j : Fin n))).det ≠ 0

omit [DecidableEq K] in
/-- Reindex a sum over a `Finset` along the order-isomorphism it has with `Fin s.card`. The
combinatorial glue between "the support of `x` has size `s`" and "there is an injection
`Fin s → Fin n` whose range is exactly that support", used to build the submatrix that does
the real work in `isMDS_branch_bound`. -/
theorem sum_orderIsoOfFin (s : Finset (Fin n)) (f : Fin n → K) :
    ∑ j : Fin s.card, f ((s.orderIsoOfFin rfl j : s) : Fin n) = ∑ i ∈ s, f i := by
  rw [Finset.sum_bij (fun j _ => ((s.orderIsoOfFin rfl j : s) : Fin n))]
  · intro j _; exact (s.orderIsoOfFin rfl j).2
  · intro j1 _ j2 _ h; exact (s.orderIsoOfFin rfl).injective (Subtype.ext h)
  · intro i hi
    exact ⟨(s.orderIsoOfFin rfl).symm ⟨i, hi⟩, Finset.mem_univ _, by simp⟩
  · intro j _; rfl

/-- **The MDS branch-number theorem.** If every square submatrix of `M` is nonsingular, then
for any nonzero `(x, Mx)`, at least `n+1` of the `2n` coordinates of `x` and `Mx` together are
nonzero — the branch number Daemen and Rijmen's wide-trail argument needs is exactly the
Singleton-optimal minimum distance of the code an MDS matrix generates. -/
theorem isMDS_branch_bound {M : Matrix (Fin n) (Fin n) K} (hM : IsMDS M)
    (x : Fin n → K) (hx : 0 < weight x + weight (M.mulVec x)) :
    n + 1 ≤ weight x + weight (M.mulVec x) := by
  by_contra hcon
  push Not at hcon
  set y := M.mulVec x with hy_def
  set S := activePattern x with hS_def
  set T := activePattern y with hT_def
  have hcard : S.card + T.card ≤ n := by
    have := hcon; simp only [weight, ← hS_def, ← hT_def] at this; omega
  have hSpos : 0 < S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · exfalso
      have hx0 : x = 0 := activePattern_eq_empty.mp (Finset.card_eq_zero.mp h0)
      have hy0 : y = 0 := by rw [hy_def, hx0]; simp
      have hzero_pat : activePattern (0 : Fin n → K) = ∅ := activePattern_eq_empty.mpr rfl
      have : weight x + weight y = 0 := by simp [weight, hx0, hy0, hzero_pat]
      omega
    · exact hpos
  have hcompl : S.card ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hcompl
  set r : Fin S.card → Fin n := fun i => ((R.orderIsoOfFin hRcard i : R) : Fin n) with hr_def
  set c : Fin S.card → Fin n := fun j => ((S.orderIsoOfFin rfl j : S) : Fin n) with hc_def
  have hdet := hM S.card R S hRcard rfl
  have hMinj := Matrix.mulVec_injective_of_det_ne_zero hdet
  have hzero : (M.submatrix r c).mulVec (fun j => x (c j)) = (0 : Fin S.card → K) := by
    funext i
    change ∑ j : Fin S.card, M (r i) (c j) * x (c j) = 0
    rw [sum_orderIsoOfFin S (fun j' => M (r i) j' * x j')]
    have hext : ∑ j' ∈ S, M (r i) j' * x j' = ∑ j' : Fin n, M (r i) j' * x j' := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro k _ hk
      have hxk : x k = 0 := by
        by_contra hxk
        exact hk (mem_activePattern.mpr hxk)
      simp [hxk]
    rw [hext, ← Matrix.mulVec_apply_eq_sum M x (r i)]
    have hrmemR : (r i : Fin n) ∈ R := (R.orderIsoOfFin hRcard i).2
    have hrnotT : (r i : Fin n) ∉ T := fun hT => (Finset.mem_sdiff.mp (hRsub hrmemR)).2 hT
    by_contra hy0
    exact hrnotT (mem_activePattern.mpr hy0)
  have hxc0 := hMinj (a₁ := fun j => x (c j)) (a₂ := 0) (by rw [hzero]; simp)
  have hc0mem : (c ⟨0, hSpos⟩ : Fin n) ∈ S := (S.orderIsoOfFin rfl ⟨0, hSpos⟩).2
  exact (mem_activePattern.mp hc0mem) (congrFun hxc0 ⟨0, hSpos⟩)

/-- An MDS matrix acts injectively on the whole space — a direct corollary of the branch
bound: if `Mx = 0` for some `x ≠ 0`, then `weight x + weight (Mx) = weight x ≤ n`, but the
branch bound demands `n + 1 ≤ weight x + weight (Mx)`, a contradiction. -/
theorem isMDS_injective {M : Matrix (Fin n) (Fin n) K} (hM : IsMDS M) :
    Function.Injective M.mulVec := by
  have hker : ∀ x : Fin n → K, M.mulVec x = 0 → x = 0 := by
    intro x hx0
    by_contra hxne
    have hxpos : 0 < weight x := by
      rw [Nat.pos_iff_ne_zero, weight, ne_eq, Finset.card_eq_zero]
      exact fun h => hxne (activePattern_eq_empty.mp h)
    have hbound := isMDS_branch_bound hM x (by omega)
    rw [hx0] at hbound
    have hw0 : weight (0 : Fin n → K) = 0 := by
      rw [weight, activePattern_eq_empty.mpr rfl, Finset.card_empty]
    rw [hw0, add_zero] at hbound
    have hwn : weight x ≤ n := by
      have h1 : weight x ≤ Finset.univ.card := Finset.card_le_univ (activePattern x)
      rwa [Finset.card_univ, Fintype.card_fin] at h1
    omega
  intro a b hab
  have h0 : M.mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
  exact sub_eq_zero.mp (hker _ h0)
