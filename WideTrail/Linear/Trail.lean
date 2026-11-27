/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Masks
import WideTrail.Linear.Binary
import WideTrail.Differential.Hull
import WideTrail.Differential.TrailProb

/-!
# Linear trails

The keyed cipher is `Scheduled.run lam γ r k` (`Differential/Hull.lean`): round `n` maps `x` to
`lam n (γ n (x + k n))`, where `lam n` is an additive bijection, `γ n` is any map and `k n` is
the round key. Fixed round constants belong to `γ n`. A **linear trail** is a sequence of masks
`T : ℕ → X`, indexed from the input: `T 0` is the input mask of round `0`. If `lamT n` is an
adjoint of `lam n` (`IsAdjoint`), the mask at the output of `γ n` is `lamT n (T (n + 1))`, and
two quantities are attached to a trail:

* `trailCorr ψ P lamT γ r T = ∏_{n < r} walsh (γ n) (T n) (lamT n (T (n + 1)))`, the trail's
  correlation over the first `r` rounds, unnormalised (divide by `|X| ^ r`); it involves no key;
* `trailPhase ψ P r k T = ∏_{n < r} ψ ⟨T n, k n⟩`, its phase under the key vector `k`; in the
  binary case a sign `±1`.

As fixed in `Masks.lean`, masks are propagated forward through the inverse of an adjoint: a
trail with a nonzero correlation is a `WideTrailSpec.IsTrail` of the specification whose `lin`
is the forward mask map, the inverse of `lamT`.

## Results

* `walsh_keyedRound`, `walsh_run_one`, `walsh_run_succ_eq_phase`, `walsh_run_zero`,
  `walsh_run_succ`: one keyed round has Walsh value `ψ ⟨u, k⟩ · walsh γ u (lamT v)`, the twin of
  `diffCount_keyedRound`; the first key of a run contributes the phase `ψ ⟨u, k 0⟩` for every
  map; and, for a separating pairing, `|X| · walsh (run (r + 1)) u w` is the sum over the mask
  `c` after the first round of the first round's Walsh value at `(u, c)` times that of the rest
  at `(c, w)` ((W6) with (W1) and (W3)).
* `walsh_run_eq_sum_trails`: **the fixed-key expansion.** For a pairing separating for `ψ`, into
  a domain, adjoints `lamT n` of the `lam n`, and every key vector `k : Fin (r + 1) → X`,

  `|X| ^ r · walsh (run lam γ (r + 1) k) u v = ∑_d trailPhase k T_d · trailCorr T_d`,

  over the trails `T_d = Scheduled.throughTrail u d v` from `u` to `v`, one for each choice of
  the `r` intermediate masks `d`. The magnitude of each summand does not depend on the key; its
  sign does, through the linear form `∑ₙ ⟨T_d n, k n⟩`. The identity holds for every key
  vector, so for a scheduled one, and for the zero key with fixed round constants in `γ`.
* `isTrail_of_trailCorr_ne_zero`: **the bridge.** If every S-box is bijective, the bundle
  pairing is separating and each `lamT n` undoes `S.lin`, a trail with a nonzero correlation is
  an `S.IsTrail`, so the activity theorems of the propagation layer apply to it unchanged. This
  is the twin of `isTrail_of_trailKeyCount_ne_zero`. The S-boxes may change from round to round.
  Each `lamT n` with `n < r` must undo the same `S.lin`, so on a finite state it is the inverse
  of `S.lin` in every one of those rounds.
* The binary case (`ψ = sign₂`, pairings into `ZMod 2`; for bricklayer layers the state is
  `X = Idx → K` with the bundle-sum pairing `P.pi`):
  * `natAbs_trailPhase`, `natAbs_trailPhase_mul`: a phase is `±1`, so a summand of the
    expansion has the magnitude `|trailCorr|` under every key;
  * `natAbs_trailCorr_le_card_pow`: `|trailCorr| ≤ |X| ^ r`;
  * `natAbs_trailCorr_le`: with linearity bound `c` for every S-box of the first `r` rounds,
    `|trailCorr| ≤ c ^ W · |K| ^ (r · |Idx| - W)`, where `W = patternWeight T r` is the number
    of active S-boxes; the twin of `trailKeyCount_bricklayer_le`;
  * `natAbs_trailCorr_mul_card_pow_le`: the exact ratio `|trailCorr| · |K| ^ W ≤ c ^ W · |X| ^ r`;
  * `natAbs_trailCorr_mul_card_pow_le_of_le`: the same with `W` replaced by any `A ≤ W`. No
    relation between `c` and `|K|` is assumed: when `c ≤ |K|` the surplus active S-boxes are
    dropped at a factor `c / |K| ≤ 1` each, and otherwise the bound follows from
    `|trailCorr| ≤ |X| ^ r`;
  * `natAbs_trailCorr_mul_pow_le`: if `c · 2 ^ d ≤ |K|`, then `|trailCorr| · 2 ^ (d · W) ≤ |X| ^ r`.
* `trailCorr_le_of_spec`, `trailCorr_ratio_le_of_spec`: **the wide-trail linear trail bounds.**
  For a bricklayer of bijective S-boxes with linearity bound `c` under a separating bundle
  pairing, and `lamT` undoing `S.lin`, every `r`-round trail with a nonzero input mask satisfies
  `|trailCorr| · 2 ^ (d · A) ≤ |Idx → K| ^ r` when `c · 2 ^ d ≤ |K|`, and
  `|trailCorr| · |K| ^ A ≤ c ^ A · |Idx → K| ^ r` in any case, where
  `A = r / 4 · B² + (if 2 ≤ r % 4 then B else 0)` is the activity lower bound of
  `IsTrail.bound_rounds`. These are the twins of `trailKeyCount_le_of_spec`.

## What is not claimed

* A trail bound bounds one trail: one summand of the fixed-key expansion, the same in magnitude
  for every key. It is not a bound on the cipher's correlation for a fixed key, a scheduled key
  or fixed round constants, which is a signed sum over all trails from `u` to `v` whose summands
  can reinforce or cancel (`Checks/Toy.lean` exhibits both).
* The activity `A` is a lower bound on the number of active S-boxes, from `IsTrail.bound_rounds`;
  it is not claimed to be attained.
* No S-box is shown to satisfy a linearity bound here, and no concrete cipher is considered. The
  specification theorems take the same S-box layer and the same linear layer in every round, as
  `trailKeyCount_le_of_spec` does.
-/

set_option autoImplicit false

namespace Linear

variable {X G R : Type*} [AddCommGroup X] [AddCommGroup G] [CommRing R]

/-! ### Trails: correlation and phase -/

section Defs

variable (ψ : AddChar G R) (P : Pairing X G)

/-- The **correlation of a linear trail**, unnormalised and key-free: the product over the
first `r` rounds of the Walsh value of the nonlinear map `γ n` at the input mask `T n` and the
output mask `lamT n (T (n + 1))`. With `lamT n` an adjoint of round `n`'s linear layer, that is
the mask at the output of `γ n`. Divided by `|X| ^ r` it is the product of the rounds'
correlations. -/
def trailCorr [Fintype X] (lamT : ℕ → X → X) (γ : ℕ → X → X) (r : ℕ) (T : ℕ → X) : R :=
  ∏ n ∈ Finset.range r, walsh ψ P P (γ n) (T n) (lamT n (T (n + 1)))

/-- The **phase of a linear trail** under the key vector `k`: `∏ₙ ψ ⟨T n, k n⟩`. In the binary
case it is `±1` (`natAbs_trailPhase`). -/
def trailPhase (r : ℕ) (k : Fin r → X) (T : ℕ → X) : R :=
  ∏ n : Fin r, ψ (P.dot (T n) (k n))

/-- A trail over zero rounds has correlation `1`. -/
@[simp] theorem trailCorr_zero [Fintype X] (lamT : ℕ → X → X) (γ : ℕ → X → X) (T : ℕ → X) :
    trailCorr ψ P lamT γ 0 T = 1 :=
  Finset.prod_range_zero _

/-- Peeling off the first round of a trail. -/
theorem trailCorr_succ [Fintype X] (lamT : ℕ → X → X) (γ : ℕ → X → X) (r : ℕ) (T : ℕ → X) :
    trailCorr ψ P lamT γ (r + 1) T
      = walsh ψ P P (γ 0) (T 0) (lamT 0 (T 1))
        * trailCorr ψ P (fun n => lamT (n + 1)) (fun n => γ (n + 1)) r (fun n => T (n + 1)) := by
  rw [trailCorr, Finset.prod_range_succ', mul_comm]
  rfl

/-- A trail over zero rounds has phase `1`. -/
@[simp] theorem trailPhase_zero (k : Fin 0 → X) (T : ℕ → X) : trailPhase ψ P 0 k T = 1 :=
  Finset.prod_empty

/-- Peeling off the first round of a phase. -/
theorem trailPhase_succ (r : ℕ) (k : Fin (r + 1) → X) (T : ℕ → X) :
    trailPhase ψ P (r + 1) k T
      = ψ (P.dot (T 0) (k 0)) * trailPhase ψ P r (Fin.tail k) (fun n => T (n + 1)) := by
  rw [trailPhase, Fin.prod_univ_succ]
  rfl

/-- The trail through `Fin.cons c d` starts with `u`, then `c`, then the trail through `d`. Its
correlation is the first round's Walsh value at `(u, lamT 0 c)` times the correlation of the
trail through `d` from `c`, in the remaining rounds. -/
theorem trailCorr_throughTrail_cons [Fintype X] (lamT : ℕ → X → X) (γ : ℕ → X → X) {r : ℕ}
    (u c : X) (d : Fin r → X) (v : X) :
    trailCorr ψ P lamT γ (r + 1 + 1) (Scheduled.throughTrail u (Fin.cons c d) v)
      = walsh ψ P P (γ 0) u (lamT 0 c) * trailCorr ψ P (fun n => lamT (n + 1))
          (fun n => γ (n + 1)) (r + 1) (Scheduled.throughTrail c d v) := by
  have h1 := Scheduled.throughTrail_succ u (Fin.cons c d : Fin (r + 1) → X) v 0
  rw [Nat.zero_add, Fin.cons_zero, Fin.tail_cons] at h1
  have h0 : Scheduled.throughTrail u (Fin.cons c d : Fin (r + 1) → X) v 0 = u := by
    simp [Scheduled.throughTrail]
  have hc0 : Scheduled.throughTrail c d v 0 = c := by simp [Scheduled.throughTrail]
  rw [trailCorr_succ ψ P lamT γ (r + 1), h0, h1, hc0]
  simp only [Scheduled.throughTrail_succ, Fin.cons_zero, Fin.tail_cons]

end Defs

/-! ### One keyed round, and the run of the scheduled cipher -/

section Rounds

variable [Fintype X] (ψ : AddChar G R) (P : Pairing X G)

/-- **One keyed round.** For `x ↦ L (F (x + k))` with `Lt` an adjoint of `L`, the Walsh value is
`ψ ⟨u, k⟩ · walsh F u (Lt v)`: the key contributes a phase, and the output mask of `L` is read
through its adjoint. This is the linear twin of `diffCount_keyedRound`. -/
theorem walsh_keyedRound {L Lt : X → X} (h : IsAdjoint P P L Lt) (F : X → X) (k u v : X) :
    walsh ψ P P (fun x => L (F (x + k))) u v = ψ (P.dot u k) * walsh ψ P P F u (Lt v) :=
  (walsh_comp_adjoint ψ P P P h (fun x => F (x + k)) u v).trans (walsh_addKey ψ P P F k u (Lt v))

/-- One round of `Scheduled.run`:
`walsh (run lam γ 1 k) u v = ψ ⟨u, k 0⟩ · walsh (γ 0) u (lamT 0 v)`. -/
theorem walsh_run_one (lam : ℕ → X ≃+ X) (lamT : ℕ → X → X)
    (hadj : ∀ n, IsAdjoint P P (lam n) (lamT n)) (γ : ℕ → X → X) (k : Fin 1 → X) (u v : X) :
    walsh ψ P P (Scheduled.run lam γ 1 k) u v
      = ψ (P.dot u (k 0)) * walsh ψ P P (γ 0) u (lamT 0 v) :=
  walsh_keyedRound ψ P (hadj 0) (γ 0) (k 0) u v

/-- The first round key of `Scheduled.run` contributes the phase `ψ ⟨u, k 0⟩`, for every map:
`walsh (run lam γ (r + 1) k) u w = ψ ⟨u, k 0⟩ · walsh H u w`, where `H` is the run with the first
key removed. -/
theorem walsh_run_succ_eq_phase (lam : ℕ → X ≃+ X) (γ : ℕ → X → X) (r : ℕ)
    (k : Fin (r + 1) → X) (u w : X) :
    walsh ψ P P (Scheduled.run lam γ (r + 1) k) u w
      = ψ (P.dot u (k 0)) * walsh ψ P P (fun x => Scheduled.run (fun n => lam (n + 1))
          (fun n => γ (n + 1)) r (Fin.tail k) (lam 0 (γ 0 x))) u w :=
  walsh_addKey ψ P P (fun x => Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
    (Fin.tail k) (lam 0 (γ 0 x))) (k 0) u w

variable {ψ P} [IsDomain R]

/-- After zero rounds the Walsh value is that of the identity: `|X|` if `u = v`, else `0`. -/
theorem walsh_run_zero [DecidableEq X] (hP : P.Separating ψ) (lam : ℕ → X ≃+ X)
    (γ : ℕ → X → X) (k : Fin 0 → X) (u v : X) :
    walsh ψ P P (Scheduled.run lam γ 0 k) u v = if u = v then (Fintype.card X : R) else 0 :=
  walsh_of_adjoint (L := fun x => x) (Lt := fun x => x) hP (fun _ _ => rfl) u v

/-- **The first round, then the rest.** For a separating pairing,
`|X| · walsh (run lam γ (r + 1) k) u w
  = ψ ⟨u, k 0⟩ · ∑_c walsh (γ 0) u (lamT 0 c) · walsh (run of the last r rounds) c w`,
where `c` is the mask between the first round and the rest. This is (W6) at the first round,
with (W1) and (W3) inside it. -/
theorem walsh_run_succ (hP : P.Separating ψ) (lam : ℕ → X ≃+ X) (lamT : ℕ → X → X)
    (hadj : ∀ n, IsAdjoint P P (lam n) (lamT n)) (γ : ℕ → X → X) (r : ℕ) (k : Fin (r + 1) → X)
    (u w : X) :
    (Fintype.card X : R) * walsh ψ P P (Scheduled.run lam γ (r + 1) k) u w
      = ψ (P.dot u (k 0)) * ∑ c, walsh ψ P P (γ 0) u (lamT 0 c)
          * walsh ψ P P (Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r
              (Fin.tail k)) c w := by
  have h := walsh_comp (P := P) P hP (fun x => lam 0 (γ 0 (x + k 0)))
    (Scheduled.run (fun n => lam (n + 1)) (fun n => γ (n + 1)) r (Fin.tail k)) u w
  refine h.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [walsh_keyedRound ψ P (hadj 0) (γ 0) (k 0) u c, mul_assoc]

/-! ### The fixed-key expansion -/

/-- **Correlation as a signed sum over trails, for every key vector.** For a separating pairing
and adjoints `lamT n` of the linear layers `lam n`, the Walsh value of `r + 1` keyed rounds under
the key vector `k` satisfies

`|X| ^ r · walsh (run lam γ (r + 1) k) u v = ∑_d trailPhase k T_d · trailCorr T_d`,

where `T_d = throughTrail u d v` runs over the trails from `u` to `v`, one for each choice of the
`r` intermediate masks `d`. The magnitude `trailCorr T_d` of each summand does not depend on the
key; only its sign `trailPhase k T_d` does, through `∑ₙ ⟨T_d n, k n⟩`. The identity holds for
every key vector, so for a scheduled one, and for the zero key with fixed round constants placed
in `γ`. -/
theorem walsh_run_eq_sum_trails (hP : P.Separating ψ) (lam : ℕ → X ≃+ X)
    (lamT : ℕ → X → X) (hadj : ∀ n, IsAdjoint P P (lam n) (lamT n)) (γ : ℕ → X → X) (r : ℕ)
    (k : Fin (r + 1) → X) (u v : X) :
    (Fintype.card X : R) ^ r * walsh ψ P P (Scheduled.run lam γ (r + 1) k) u v
      = ∑ d : Fin r → X, trailPhase ψ P (r + 1) k (Scheduled.throughTrail u d v)
          * trailCorr ψ P lamT γ (r + 1) (Scheduled.throughTrail u d v) := by
  induction r generalizing lam lamT γ u with
  | zero =>
    rw [pow_zero, one_mul, walsh_run_one ψ P lam lamT hadj γ k u v, Fintype.sum_unique,
      trailPhase_succ, trailCorr_succ]
    simp [Scheduled.throughTrail]
  | succ r ih =>
    rw [pow_succ, mul_assoc, walsh_run_succ hP lam lamT hadj γ (r + 1) k u v,
      ← (Fin.consEquiv (fun _ : Fin (r + 1) => X)).sum_comp, Fintype.sum_prod_type,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hrest := ih (fun n => lam (n + 1)) (fun n => lamT (n + 1)) (fun n => hadj (n + 1))
      (fun n => γ (n + 1)) (Fin.tail k) c
    rw [show ∀ a b e f : R, a * (b * (e * f)) = b * e * (a * f) from fun _ _ _ _ => by ring,
      hrest, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    set e := (Fin.consEquiv fun _ : Fin (r + 1) => X) (c, d) with he
    have hd : Fin.tail e = d := rfl
    have hc : e 0 = c := rfl
    have h1 := Scheduled.throughTrail_succ u e v 0
    rw [Nat.zero_add, hc, hd] at h1
    have h0 : Scheduled.throughTrail u e v 0 = u := by simp [Scheduled.throughTrail]
    have hc0 : Scheduled.throughTrail c d v 0 = c := by simp [Scheduled.throughTrail]
    rw [trailPhase_succ ψ P (r + 1) k, trailCorr_succ ψ P lamT γ (r + 1), h0, h1, hc0]
    simp only [Scheduled.throughTrail_succ, hd, hc]
    ring

end Rounds

/-! ### The bridge to the activity count -/

section Bridge

variable {Idx Col K : Type*} [Fintype Idx] [DecidableEq Idx] [DecidableEq Col] [Fintype Col]
  [AddCommGroup K] [Fintype K] [DecidableEq K] [IsDomain R]

/-- **A linear trail with a nonzero correlation is a wide-trail pattern sequence.** Let every
S-box of the first `r` rounds be bijective and the bundle pairing separating, and let each
`lamT n` undo the forward mask map `S.lin`. If the trail correlation of `T` is nonzero, then
`S.IsTrail T r`. At round `n` the mask `b = lamT n (T (n + 1))` at the output of the S-box layer
has the support of `T n` (`activePattern_eq_of_walsh_ne_zero`), and `T (n + 1) = S.lin b`
because `lamT n` is a bijection of a finite type. This is the linear twin of
`isTrail_of_trailKeyCount_ne_zero`; the specification's `lin` is the forward mask map, the
inverse of the adjoint. The S-boxes may depend on the round; the maps `lamT n`, `n < r`, all
invert the same `S.lin`, so they agree. -/
theorem isTrail_of_trailCorr_ne_zero {ψ : AddChar G R} {P : Pairing K G} (hP : P.Separating ψ)
    (S : WideTrailSpec Idx Col K) {s : ℕ → Idx → K → K} {lamT : ℕ → (Idx → K) → (Idx → K)}
    {r : ℕ} (hs : ∀ n < r, ∀ i, Function.Bijective (s n i))
    (hlam : ∀ n < r, ∀ b, lamT n (S.lin b) = b) {T : ℕ → Idx → K}
    (h : trailCorr ψ P.pi lamT (fun n => bricklayer (s n)) r T ≠ 0) : S.IsTrail T r := by
  intro n hn
  have hn' : walsh ψ P.pi P.pi (bricklayer (s n)) (T n) (lamT n (T (n + 1))) ≠ 0 :=
    fun hz => h (Finset.prod_eq_zero (Finset.mem_range.mpr hn) hz)
  refine ⟨lamT n (T (n + 1)), activePattern_eq_of_walsh_ne_zero hP (hs n hn) hn', ?_⟩
  have hinj : Function.Injective (lamT n) :=
    Finite.injective_iff_surjective.mpr fun b => ⟨S.lin b, hlam n hn b⟩
  exact hinj (hlam n hn _).symm

end Bridge

/-! ### The binary case: bounds -/

section Binary

variable {Idx Col K : Type*} [Fintype Idx] [DecidableEq Idx] [DecidableEq Col] [Fintype Col]
  [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- The absolute value of a product of integers over `Finset.range r`. -/
theorem natAbs_prod_range (r : ℕ) (f : ℕ → ℤ) :
    (∏ n ∈ Finset.range r, f n).natAbs = ∏ n ∈ Finset.range r, (f n).natAbs :=
  map_prod Int.natAbsHom f _

/-- In the binary case a phase is `±1`. -/
theorem natAbs_trailPhase (P : Pairing X (ZMod 2)) (r : ℕ) (k : Fin r → X)
    (T : ℕ → X) : (trailPhase sign₂ P r k T).natAbs = 1 := by
  rw [trailPhase, show ∀ f : Fin r → ℤ, (∏ n, f n).natAbs = ∏ n, (f n).natAbs from
    fun f => map_prod Int.natAbsHom f _]
  simp

/-- In the binary case a summand of the fixed-key expansion has the magnitude of the trail
correlation, whatever the key. -/
theorem natAbs_trailPhase_mul (P : Pairing X (ZMod 2)) (r : ℕ) (k : Fin r → X)
    (T : ℕ → X) (z : ℤ) : (trailPhase sign₂ P r k T * z).natAbs = z.natAbs := by
  rw [Int.natAbs_mul, natAbs_trailPhase, one_mul]

/-- A trail correlation is at most `|X| ^ r` in absolute value. -/
theorem natAbs_trailCorr_le_card_pow [Fintype X] (P : Pairing X (ZMod 2)) (lamT : ℕ → X → X)
    (γ : ℕ → X → X) (r : ℕ) (T : ℕ → X) :
    (trailCorr sign₂ P lamT γ r T).natAbs ≤ Fintype.card X ^ r := by
  rw [trailCorr, natAbs_prod_range]
  calc ∏ n ∈ Finset.range r, (walsh sign₂ P P (γ n) (T n) (lamT n (T (n + 1)))).natAbs
      ≤ ∏ _n ∈ Finset.range r, Fintype.card X :=
        Finset.prod_le_prod' fun n _ => natAbs_walsh_le_card P P _ _ _
    _ = Fintype.card X ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- **Every active S-box costs a factor `c`.** If every S-box of the first `r` rounds has
linearity bound `c`, a trail through bricklayer layers has
`|trailCorr| ≤ c ^ W · |K| ^ (r · |Idx| - W)` with `W = patternWeight T r`, its number of active
S-boxes. The linear layers `lamT n` are arbitrary. This is the linear twin of the count in
`trailKeyCount_bricklayer_le`. -/
theorem natAbs_trailCorr_le {P : Pairing K (ZMod 2)} {s : ℕ → Idx → K → K} {c r : ℕ}
    (hc : ∀ n < r, ∀ i, IsLinearityBound P (s n i) c) (lamT : ℕ → (Idx → K) → (Idx → K))
    (T : ℕ → Idx → K) :
    (trailCorr sign₂ P.pi lamT (fun n => bricklayer (s n)) r T).natAbs
      ≤ c ^ patternWeight T r * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r) := by
  have hwle : ∀ n, weight (T n) ≤ Fintype.card Idx := fun n => Finset.card_le_univ _
  rw [trailCorr, natAbs_prod_range]
  calc ∏ n ∈ Finset.range r,
        (walsh sign₂ P.pi P.pi (bricklayer (s n)) (T n) (lamT n (T (n + 1)))).natAbs
      ≤ ∏ n ∈ Finset.range r,
          (c ^ weight (T n) * Fintype.card K ^ (Fintype.card Idx - weight (T n))) :=
        Finset.prod_le_prod' fun n hn =>
          natAbs_walsh_bricklayer_le (hc n (Finset.mem_range.mp hn)) _ _
    _ = c ^ (∑ n ∈ Finset.range r, weight (T n))
          * Fintype.card K ^ (∑ n ∈ Finset.range r, (Fintype.card Idx - weight (T n))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
    _ = _ := by rw [sum_sub_of_le (fun n => weight (T n)) hwle r]; rfl

/-- **The exact ratio.** With the hypotheses of `natAbs_trailCorr_le`,
`|trailCorr| · |K| ^ W ≤ c ^ W · |Idx → K| ^ r` for `W = patternWeight T r`: divided by
`|Idx → K| ^ r`, the trail's correlation is at most `(c / |K|) ^ W` in absolute value. -/
theorem natAbs_trailCorr_mul_card_pow_le {P : Pairing K (ZMod 2)} {s : ℕ → Idx → K → K}
    {c r : ℕ} (hc : ∀ n < r, ∀ i, IsLinearityBound P (s n i) c)
    (lamT : ℕ → (Idx → K) → (Idx → K)) (T : ℕ → Idx → K) :
    (trailCorr sign₂ P.pi lamT (fun n => bricklayer (s n)) r T).natAbs
        * Fintype.card K ^ patternWeight T r
      ≤ c ^ patternWeight T r * Fintype.card (Idx → K) ^ r := by
  have hWle : patternWeight T r ≤ r * Fintype.card Idx := by
    calc patternWeight T r ≤ ∑ _n ∈ Finset.range r, Fintype.card Idx :=
          Finset.sum_le_sum fun n _ => Finset.card_le_univ _
      _ = r * Fintype.card Idx := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (trailCorr sign₂ P.pi lamT (fun n => bricklayer (s n)) r T).natAbs
        * Fintype.card K ^ patternWeight T r
      ≤ (c ^ patternWeight T r * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r))
          * Fintype.card K ^ patternWeight T r :=
        Nat.mul_le_mul_right _ (natAbs_trailCorr_le hc lamT T)
    _ = c ^ patternWeight T r * Fintype.card K ^ (r * Fintype.card Idx) := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hWle]
    _ = c ^ patternWeight T r * Fintype.card (Idx → K) ^ r := by
        rw [Fintype.card_fun, ← pow_mul, mul_comm (Fintype.card Idx) r]

/-- **The exact ratio for a lower bound on the active S-boxes.** As
`natAbs_trailCorr_mul_card_pow_le`, with `W = patternWeight T r` replaced by any `A ≤ W`:
`|trailCorr| · |K| ^ A ≤ c ^ A · |Idx → K| ^ r`. No relation between `c` and `|K|` is assumed:
if `c ≤ |K|` the surplus active S-boxes are dropped from the exact ratio, each at a factor
`c / |K| ≤ 1`; otherwise the bound follows from `|trailCorr| ≤ |Idx → K| ^ r`. -/
theorem natAbs_trailCorr_mul_card_pow_le_of_le {P : Pairing K (ZMod 2)} {s : ℕ → Idx → K → K}
    {c r A : ℕ} (hc : ∀ n < r, ∀ i, IsLinearityBound P (s n i) c)
    (lamT : ℕ → (Idx → K) → (Idx → K)) (T : ℕ → Idx → K) (hA : A ≤ patternWeight T r) :
    (trailCorr sign₂ P.pi lamT (fun n => bricklayer (s n)) r T).natAbs * Fintype.card K ^ A
      ≤ c ^ A * Fintype.card (Idx → K) ^ r := by
  set t := (trailCorr sign₂ P.pi lamT (fun n => bricklayer (s n)) r T).natAbs
  rcases le_total c (Fintype.card K) with hcq | hqc
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hA
    have h := natAbs_trailCorr_mul_card_pow_le hc lamT T
    rw [he, pow_add, pow_add] at h
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (Fintype.card_pos (α := K)) e)
    calc t * Fintype.card K ^ A * Fintype.card K ^ e
        = t * (Fintype.card K ^ A * Fintype.card K ^ e) := mul_assoc _ _ _
      _ ≤ c ^ A * c ^ e * Fintype.card (Idx → K) ^ r := h
      _ ≤ c ^ A * Fintype.card K ^ e * Fintype.card (Idx → K) ^ r :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcq e))
      _ = c ^ A * Fintype.card (Idx → K) ^ r * Fintype.card K ^ e := by ring
  · calc t * Fintype.card K ^ A ≤ Fintype.card (Idx → K) ^ r * c ^ A :=
          Nat.mul_le_mul (natAbs_trailCorr_le_card_pow _ _ _ r T) (Nat.pow_le_pow_left hqc A)
      _ = c ^ A * Fintype.card (Idx → K) ^ r := mul_comm _ _

/-- **Every active S-box costs `2 ^ d`.** If the linearity bound clears a factor `2 ^ d`,
`c · 2 ^ d ≤ |K|`, then `|trailCorr| · 2 ^ (d · W) ≤ |Idx → K| ^ r` for `W = patternWeight T r`:
the trail's correlation is at most `2 ^ (-d · W)` in absolute value. -/
theorem natAbs_trailCorr_mul_pow_le {P : Pairing K (ZMod 2)} {s : ℕ → Idx → K → K}
    {c d r : ℕ} (hc : ∀ n < r, ∀ i, IsLinearityBound P (s n i) c)
    (hd : c * 2 ^ d ≤ Fintype.card K) (lamT : ℕ → (Idx → K) → (Idx → K)) (T : ℕ → Idx → K) :
    (trailCorr sign₂ P.pi lamT (fun n => bricklayer (s n)) r T).natAbs
        * 2 ^ (d * patternWeight T r)
      ≤ Fintype.card (Idx → K) ^ r := by
  have hWle : patternWeight T r ≤ r * Fintype.card Idx := by
    calc patternWeight T r ≤ ∑ _n ∈ Finset.range r, Fintype.card Idx :=
          Finset.sum_le_sum fun n _ => Finset.card_le_univ _
      _ = r * Fintype.card Idx := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (trailCorr sign₂ P.pi lamT (fun n => bricklayer (s n)) r T).natAbs
        * 2 ^ (d * patternWeight T r)
      ≤ (c ^ patternWeight T r * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r))
          * 2 ^ (d * patternWeight T r) := Nat.mul_le_mul_right _ (natAbs_trailCorr_le hc lamT T)
    _ = (c * 2 ^ d) ^ patternWeight T r
          * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r) := by
        rw [mul_pow, pow_mul]; ring
    _ ≤ Fintype.card K ^ patternWeight T r
          * Fintype.card K ^ (r * Fintype.card Idx - patternWeight T r) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd _)
    _ = Fintype.card K ^ (r * Fintype.card Idx) := by rw [← pow_add]; congr 1; omega
    _ = Fintype.card (Idx → K) ^ r := by rw [Fintype.card_fun, ← pow_mul]; congr 1; ring

/-- **The wide-trail linear trail bound.** For a cipher whose S-box layer is a bricklayer of
bijective S-boxes with linearity bound `c` clearing `2 ^ d`, `c · 2 ^ d ≤ |K|`, under a
separating bundle pairing, and whose linear layer has an adjoint `lamT` undoing the forward mask
map `S.lin`: every `r`-round linear trail with a nonzero input mask has
`|trailCorr| · 2 ^ (d · A) ≤ |Idx → K| ^ r`, where
`A = r / 4 · B² + (if 2 ≤ r % 4 then B else 0)` is the activity lower bound of
`IsTrail.bound_rounds`. Divided by `|Idx → K| ^ r`, the trail's correlation is at most
`2 ^ (-d · A)` in absolute value.

This bounds one trail: one summand of the fixed-key expansion `walsh_run_eq_sum_trails`, whose
magnitude is the same for every key. It is not a bound on the cipher's correlation for a fixed
key, which is a signed sum over all trails. -/
theorem trailCorr_le_of_spec {P : Pairing K (ZMod 2)} (hP : P.Separating sign₂)
    (S : WideTrailSpec Idx Col K) {s : Idx → K → K} (hs : ∀ i, Function.Bijective (s i))
    {c d : ℕ} (hc : ∀ i, IsLinearityBound P (s i) c) (hd : c * 2 ^ d ≤ Fintype.card K)
    {lamT : (Idx → K) → (Idx → K)} (hlam : ∀ b, lamT (S.lin b) = b) {r : ℕ}
    {T : ℕ → Idx → K} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ P.pi (fun _ => lamT) (fun _ => bricklayer s) r T).natAbs
        * 2 ^ (d * (r / 4 * S.fourRoundBound + (if 2 ≤ r % 4 then S.branch else 0)))
      ≤ Fintype.card (Idx → K) ^ r := by
  by_cases hz : trailCorr sign₂ P.pi (fun _ => lamT) (fun _ => bricklayer s) r T = 0
  · simp [hz]
  · have hW := (isTrail_of_trailCorr_ne_zero (s := fun _ => s) hP S (fun _ _ => hs)
      (fun _ _ => hlam) hz).bound_rounds h0
    exact le_trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left d hW)))
      (natAbs_trailCorr_mul_pow_le (s := fun _ => s) (fun _ _ => hc) hd (fun _ => lamT) T)

/-- **The wide-trail linear trail bound, as an exact ratio.** With the hypotheses of
`trailCorr_le_of_spec` but no relation between `c` and `|K|`, every `r`-round linear trail with
a nonzero input mask has `|trailCorr| · |K| ^ A ≤ c ^ A · |Idx → K| ^ r` for the same activity
lower bound `A`: its correlation is at most `(c / |K|) ^ A` in absolute value. One trail, as in
`trailCorr_le_of_spec`. -/
theorem trailCorr_ratio_le_of_spec {P : Pairing K (ZMod 2)} (hP : P.Separating sign₂)
    (S : WideTrailSpec Idx Col K) {s : Idx → K → K} (hs : ∀ i, Function.Bijective (s i))
    {c : ℕ} (hc : ∀ i, IsLinearityBound P (s i) c)
    {lamT : (Idx → K) → (Idx → K)} (hlam : ∀ b, lamT (S.lin b) = b) {r : ℕ}
    {T : ℕ → Idx → K} (h0 : T 0 ≠ 0) :
    (trailCorr sign₂ P.pi (fun _ => lamT) (fun _ => bricklayer s) r T).natAbs
        * Fintype.card K ^ (r / 4 * S.fourRoundBound + (if 2 ≤ r % 4 then S.branch else 0))
      ≤ c ^ (r / 4 * S.fourRoundBound + (if 2 ≤ r % 4 then S.branch else 0))
          * Fintype.card (Idx → K) ^ r := by
  by_cases hz : trailCorr sign₂ P.pi (fun _ => lamT) (fun _ => bricklayer s) r T = 0
  · simp [hz]
  · exact natAbs_trailCorr_mul_card_pow_le_of_le (s := fun _ => s) (fun _ _ => hc)
      (fun _ => lamT) T ((isTrail_of_trailCorr_ne_zero (s := fun _ => s) hP S (fun _ _ => hs)
        (fun _ _ => hlam) hz).bound_rounds h0)

end Binary

end Linear
