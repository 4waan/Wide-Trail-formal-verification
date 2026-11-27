/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.Plonky3

/-!
# A materialised runner for the width-sixteen Plonky3 Poseidon2 permutation

`WideTrail.Poseidon2.Plonky3` defines the permutation through `Hades.execute`, linear
equivalences and finite sums over `Fin 16`. That form suits the proofs there. This file gives a
second implementation of the same function in which every coordinate is a named field and every
layer is written out coordinate by coordinate, with no `LinearEquiv`, `Matrix` or `Finset` inside
the computation. The runner is defined over any commutative ring and takes the internal diagonal
as sixteen ring elements (`Diag.internalDense`). Over a field it computes the specification state
of `Plonky3.Diag.permutation` for every diagonal `d` and scale `c` with
`Diag.Conditions d.toState c`, every S-box `sbox : K ≃ K`, every round-constant table, every
number `rP` of partial rounds, every input and every number of rounds. The SP1 runner is the case
`d = sp1DiagDense`, by definition. `Checks/Plonky3KAT.lean` evaluates the SP1 runner by `decide`,
and `Checks/Plonky3.lean` the runner with another diagonal.

## The runner

* `Dense R`: sixteen coordinates `x0, …, x15`; `xi` is the Rust `state[i]`. `toState` and
  `ofState` convert to and from the specification's `Fin 16 → R` (`toState_ofState`,
  `ofState_toState`). Equality is decided coordinate by coordinate (derived `DecidableEq`).
* `externalDense = addSums ∘ mat4Dense`. `mat4` is Plonky3's `apply_mat4` (`p3-poseidon2`
  `0.4.3-succinct` `src/matrix.rs:43-57`; the `0.2.3-succinct` file is byte-identical) with its
  additions in the code's order, `mat4Dense` applies it to the four blocks `state[4b..4b+4]`
  (`:113-123`), and `addSums` adds `sums[i % 4]` to coordinate `i` (`:127-138`).
* `Diag.internalDense d c`: coordinate `i` becomes `c (d_i x_i + s)`, `s = x0 + ⋯ + x15`, for
  a diagonal `d : Dense R` given as sixteen ring elements. This is the field-level layer
  `Plonky3.Diag.internal` with scale `c`.
* `Diag.roundDense d c rP sbox values n`: round `n` of `Plonky3.Diag.rounds`. It adds the row
  `values n` to every coordinate; then, for `n < 4` and `4 + rP ≤ n < 8 + rP`, applies `sbox` to
  every coordinate and the external layer; for `4 ≤ n < 4 + rP`, applies `sbox` to coordinate `0`
  and the internal layer; for `n ≥ 8 + rP`, where `Hades.hadesMask` is empty, applies the external
  layer alone.
* `Diag.executeDense d c rP sbox values x n`: the first `n` rounds from `x`.
  `Diag.permutationDense`: the initial external layer, then `8 + rP` rounds.
* The SP1 runner: `sp1DiagDense` is the diagonal `(-2, 1, 2, 4, …, 2^13, 2^15)` of
  `Plonky3.sp1Diag` written as numerals (`sp1DiagDense_toState`), and `internalDense c`,
  `roundDense c`, `executeDense c` and `permutationDense c` are the `Diag` functions at
  `d = sp1DiagDense`. The scale `c` is intended to be `R^{-1}`, `R = 2^32`.

## Results

* `mat4_eq`: the addition chain of `apply_mat4` computes the rows of `circ(2, 3, 1, 1)`.
* `externalDense_toState`: `externalDense` is `Plonky3.mdsLight`, the transcription of
  `mds_light_permutation`; `externalDense_toState_external`: it is `Plonky3.external`.
* For every diagonal `d : Dense K` and every `hD : Plonky3.Diag.Conditions d.toState c`:
  `Diag.internalDense_toState` (`Diag.internalDense d c` is `Plonky3.Diag.internal d.toState c`);
  `Diag.roundDense_toState` (each round is the specification's round
  `(Plonky3.Diag.rounds hD rP sbox values n).apply`); `Diag.executeDense_toState` (for every `n`,
  the runner's state after `n` rounds is
  `Hades.execute (Plonky3.Diag.rounds hD rP sbox values) x n`); `Diag.permutationDense_toState`
  and `Diag.permutation_eq_permutationDense` (the runner's permutation is
  `Plonky3.Diag.permutation hD rP sbox values`); and the transfers
  `Diag.permutation_eq_of_dense`, `Diag.permutation_ne_of_dense`, `Diag.execute_eq_of_dense`,
  `Diag.execute_ne_of_dense`: an equality or inequality of runner states, checked by `decide`,
  gives the same statement for the specification.
* The same results for the SP1 runner with `hK : Plonky3.Conditions c`, under the same names
  without `Diag.`: `internalDense_toState` (`internalDense c` is `Plonky3.internal c`),
  `roundDense_toState`, `executeDense_toState`, `execute_eq_executeDense`,
  `permutationDense_toState`, `permutation_eq_permutationDense` (the runner's permutation is
  `Plonky3.permutation hK rP sbox values`), `permutation_eq_of_dense`, `permutation_ne_of_dense`,
  `execute_eq_of_dense`, `execute_ne_of_dense`. Each is the `Diag` result at `d = sp1DiagDense`,
  with `hK.toDiagDense : Plonky3.Diag.Conditions sp1DiagDense.toState c` obtained from
  `hK.toDiag` and `sp1DiagDense_toState`.

The runner adds the whole row `values n` in every round, as a HADES round does, so it agrees
with the specification for every table. For tables with `PartialRowsAtZero`, such as
`roundValues`, the partial rounds are then the code's rounds, which add the constant to
`state[0]` only (`Plonky3.rounds_apply_middle`).

## What is not claimed

This file is a second implementation of the model of `WideTrail.Poseidon2.Plonky3`, proved equal
to it. It adds no claim about the Rust code beyond the transcriptions cited: `mat4` follows the
additions of `apply_mat4`, while the internal layer is the field-level reading of the Montgomery
code described in the generic model, not a transcription of that code. The only diagonal
identified with source code is `sp1DiagDense`. No security statement is made here. The activity
counts of the generic model are lower bounds on charged S-boxes for actual input pairs; its
trail-probability statements concern one trail, and its differential statements the
key-averaged differential, both in the model with an additional independent uniform key per
round; none concerns the permutation with its fixed constants. Nothing is said about
subspace-trail resistance, algebraic attacks, sponge or duplex constructions, or equivalence
with the Rust code or the AIR.
-/

set_option autoImplicit false

namespace Poseidon2.Plonky3

/-! ### Materialised states -/

/-- Four coordinates: one block `state[4b..4b+4]` of `mds_light_permutation`. -/
structure Quad (R : Type*) where
  q0 : R
  q1 : R
  q2 : R
  q3 : R

/-- A width-sixteen state with one field per coordinate; `xi` is the Rust `state[i]`. -/
structure Dense (R : Type*) where
  x0 : R
  x1 : R
  x2 : R
  x3 : R
  x4 : R
  x5 : R
  x6 : R
  x7 : R
  x8 : R
  x9 : R
  x10 : R
  x11 : R
  x12 : R
  x13 : R
  x14 : R
  x15 : R
  deriving DecidableEq

namespace Dense

variable {R : Type*}

/-- The specification's state `Fin 16 → R`. -/
def toState (x : Dense R) : Fin 16 → R :=
  ![x.x0, x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8, x.x9, x.x10, x.x11, x.x12, x.x13,
    x.x14, x.x15]

/-- The sixteen coordinates of a specification state. -/
def ofState (x : Fin 16 → R) : Dense R :=
  ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15⟩

theorem toState_ofState (x : Fin 16 → R) : (ofState x).toState = x := by
  funext i
  fin_cases i <;> rfl

theorem ofState_toState (x : Dense R) : ofState x.toState = x := by
  cases x
  rfl

theorem toState_injective : Function.Injective (toState : Dense R → Fin 16 → R) := by
  intro x y h
  rw [← ofState_toState x, h, ofState_toState]

theorem sum_toState [AddCommMonoid R] (x : Dense R) :
    ∑ j, x.toState j = x.x0 + x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 + x.x9 +
      x.x10 + x.x11 + x.x12 + x.x13 + x.x14 + x.x15 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, toState, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero, add_assoc]

end Dense

/-! ### The runner -/

section Runner

variable {R : Type*}

/-- Add a row of round constants to every coordinate. -/
def addRow [Add R] (x : Dense R) (v : Fin 16 → R) : Dense R :=
  ⟨x.x0 + v 0, x.x1 + v 1, x.x2 + v 2, x.x3 + v 3, x.x4 + v 4, x.x5 + v 5, x.x6 + v 6,
    x.x7 + v 7, x.x8 + v 8, x.x9 + v 9, x.x10 + v 10, x.x11 + v 11, x.x12 + v 12,
    x.x13 + v 13, x.x14 + v 14, x.x15 + v 15⟩

/-- The S-box on every coordinate. -/
def sboxAll (s : R → R) (x : Dense R) : Dense R :=
  ⟨s x.x0, s x.x1, s x.x2, s x.x3, s x.x4, s x.x5, s x.x6, s x.x7, s x.x8, s x.x9, s x.x10,
    s x.x11, s x.x12, s x.x13, s x.x14, s x.x15⟩

/-- The S-box on coordinate `0` only. -/
def sboxFirst (s : R → R) (x : Dense R) : Dense R :=
  ⟨s x.x0, x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8, x.x9, x.x10, x.x11, x.x12, x.x13,
    x.x14, x.x15⟩

variable [CommRing R]

/-- Plonky3's `apply_mat4` (`p3-poseidon2` `0.4.3-succinct` `src/matrix.rs:43-57`), with its
additions in the code's order; `x.double()` is `x + x`. -/
def mat4 (x0 x1 x2 x3 : R) : Quad R :=
  let t01 := x0 + x1
  let t23 := x2 + x3
  let t0123 := t01 + t23
  let t01123 := t0123 + x1
  let t01233 := t0123 + x3
  ⟨t01123 + t01, t01123 + (x2 + x2), t01233 + t23, t01233 + (x0 + x0)⟩

/-- `M4` on each block `state[4b..4b+4]` (`src/matrix.rs:113-123`). -/
def mat4Dense (x : Dense R) : Dense R :=
  let b0 := mat4 x.x0 x.x1 x.x2 x.x3
  let b1 := mat4 x.x4 x.x5 x.x6 x.x7
  let b2 := mat4 x.x8 x.x9 x.x10 x.x11
  let b3 := mat4 x.x12 x.x13 x.x14 x.x15
  ⟨b0.q0, b0.q1, b0.q2, b0.q3, b1.q0, b1.q1, b1.q2, b1.q3,
    b2.q0, b2.q1, b2.q2, b2.q3, b3.q0, b3.q1, b3.q2, b3.q3⟩

/-- The position sums `sums[k]`, added to every coordinate `i` with `i % 4 = k`
(`src/matrix.rs:127-138`). -/
def addSums (y : Dense R) : Dense R :=
  let s0 := y.x0 + y.x4 + y.x8 + y.x12
  let s1 := y.x1 + y.x5 + y.x9 + y.x13
  let s2 := y.x2 + y.x6 + y.x10 + y.x14
  let s3 := y.x3 + y.x7 + y.x11 + y.x15
  ⟨y.x0 + s0, y.x1 + s1, y.x2 + s2, y.x3 + s3, y.x4 + s0, y.x5 + s1, y.x6 + s2, y.x7 + s3,
    y.x8 + s0, y.x9 + s1, y.x10 + s2, y.x11 + s3, y.x12 + s0, y.x13 + s1, y.x14 + s2,
    y.x15 + s3⟩

/-- The external layer, `mds_light_permutation::<_, MDSMat4, 16>` (`src/matrix.rs:110-139`). -/
def externalDense (x : Dense R) : Dense R := addSums (mat4Dense x)

namespace Diag

/-- The internal layer for a diagonal `d` given as sixteen ring elements: coordinate `i`
becomes `c (d_i x_i + s)` with `s = x0 + ⋯ + x15` (`Diag.internalDense_toState_apply`). -/
def internalDense (d : Dense R) (c : R) (x : Dense R) : Dense R :=
  let s := x.x0 + x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 + x.x9 + x.x10 +
    x.x11 + x.x12 + x.x13 + x.x14 + x.x15
  ⟨c * (d.x0 * x.x0 + s), c * (d.x1 * x.x1 + s), c * (d.x2 * x.x2 + s), c * (d.x3 * x.x3 + s),
    c * (d.x4 * x.x4 + s), c * (d.x5 * x.x5 + s), c * (d.x6 * x.x6 + s), c * (d.x7 * x.x7 + s),
    c * (d.x8 * x.x8 + s), c * (d.x9 * x.x9 + s), c * (d.x10 * x.x10 + s),
    c * (d.x11 * x.x11 + s), c * (d.x12 * x.x12 + s), c * (d.x13 * x.x13 + s),
    c * (d.x14 * x.x14 + s), c * (d.x15 * x.x15 + s)⟩

/-- Round `n` of `Plonky3.Diag.rounds`: add the row `values n`, then the S-box layer of
`Hades.hadesMask 4 rP 4 {0} n` and the linear layer of `Plonky3.Diag.linear`. -/
def roundDense (d : Dense R) (c : R) (rP : ℕ) (sbox : R → R) (values : ℕ → Fin 16 → R) (n : ℕ)
    (x : Dense R) : Dense R :=
  if n < 4 then externalDense (sboxAll sbox (addRow x (values n)))
  else if n < 4 + rP then internalDense d c (sboxFirst sbox (addRow x (values n)))
  else if n < 4 + rP + 4 then externalDense (sboxAll sbox (addRow x (values n)))
  else externalDense (addRow x (values n))

/-- The first `n` rounds, from `x`. -/
def executeDense (d : Dense R) (c : R) (rP : ℕ) (sbox : R → R) (values : ℕ → Fin 16 → R)
    (x : Dense R) : ℕ → Dense R
  | 0 => x
  | n + 1 => roundDense d c rP sbox values n (executeDense d c rP sbox values x n)

/-- The initial external layer (`p3-poseidon2` `src/lib.rs:179`), then the `8 + rP` rounds
(`src/lib.rs:182-201`). -/
def permutationDense (d : Dense R) (c : R) (rP : ℕ) (sbox : R → R) (values : ℕ → Fin 16 → R)
    (x : Dense R) : Dense R :=
  executeDense d c rP sbox values (externalDense x) (8 + rP)

end Diag

/-- The SP1 diagonal `d = (-2, 1, 2, 4, …, 2^13, 2^15)` as sixteen numerals (`p3-koala-bear`
`0.4.3-succinct` `src/poseidon2.rs:37-58`, `p3-baby-bear` `0.2.3-succinct`
`src/poseidon2.rs:29-49`); over a field it is `Plonky3.sp1Diag` (`sp1DiagDense_toState`). -/
def sp1DiagDense : Dense R :=
  ⟨-2, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 32768⟩

/-- The SP1 internal layer: coordinate `i` becomes `c (d_i x_i + s)` with `s = x0 + ⋯ + x15` and
`d = sp1DiagDense`; equal to `Plonky3.internal` by `internalDense_toState`. -/
def internalDense (c : R) (x : Dense R) : Dense R := Diag.internalDense sp1DiagDense c x

/-- Round `n` of `Plonky3.rounds`: `Diag.roundDense` at `d = sp1DiagDense`. -/
def roundDense (c : R) (rP : ℕ) (sbox : R → R) (values : ℕ → Fin 16 → R) (n : ℕ)
    (x : Dense R) : Dense R :=
  Diag.roundDense sp1DiagDense c rP sbox values n x

/-- The first `n` rounds of the SP1 runner, from `x`. -/
def executeDense (c : R) (rP : ℕ) (sbox : R → R) (values : ℕ → Fin 16 → R) (x : Dense R) :
    ℕ → Dense R :=
  Diag.executeDense sp1DiagDense c rP sbox values x

/-- The SP1 runner's permutation: the initial external layer (`p3-poseidon2` `src/lib.rs:179`),
then the `8 + rP` rounds (`src/lib.rs:182-201`). -/
def permutationDense (c : R) (rP : ℕ) (sbox : R → R) (values : ℕ → Fin 16 → R)
    (x : Dense R) : Dense R :=
  Diag.permutationDense sp1DiagDense c rP sbox values x

end Runner

/-! ### The layers against the specification -/

section Layers

variable {R : Type*}

theorem addRow_toState [Add R] (x : Dense R) (v : Fin 16 → R) :
    (addRow x v).toState = x.toState + v := by
  funext i
  fin_cases i <;> rfl

theorem sboxAll_toState (s : R → R) (x : Dense R) :
    (sboxAll s x).toState = fun i => s (x.toState i) := by
  funext i
  fin_cases i <;> rfl

theorem sboxFirst_toState (s : R → R) (x : Dense R) :
    (sboxFirst s x).toState = Function.update x.toState 0 (s (x.toState 0)) := by
  funext i
  fin_cases i <;> rfl

theorem maskedEquiv_univ (sbox : R ≃ R) (y : Fin 16 → R) :
    Hades.maskedEquiv Finset.univ (fun _ => sbox) y = fun i => sbox (y i) := by
  funext i
  simp

theorem maskedEquiv_zero (sbox : R ≃ R) (y : Fin 16 → R) :
    Hades.maskedEquiv ({0} : Finset (Fin 16)) (fun _ => sbox) y =
      Function.update y 0 (sbox (y 0)) := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hi]

theorem maskedEquiv_empty (sbox : R ≃ R) (y : Fin 16 → R) :
    Hades.maskedEquiv (∅ : Finset (Fin 16)) (fun _ => sbox) y = y := by
  funext i
  simp

variable [CommRing R]

/-- **`apply_mat4` computes `circ(2, 3, 1, 1)`**: the code's chain of additions gives the rows
`(2, 3, 1, 1)`, `(1, 2, 3, 1)`, `(1, 1, 2, 3)`, `(3, 1, 1, 2)`. -/
theorem mat4_eq (x0 x1 x2 x3 : R) :
    mat4 x0 x1 x2 x3 = ⟨2 * x0 + 3 * x1 + x2 + x3, x0 + 2 * x1 + 3 * x2 + x3,
      x0 + x1 + 2 * x2 + 3 * x3, 3 * x0 + x1 + x2 + 2 * x3⟩ := by
  simp only [mat4, Quad.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

theorem mat4Dense_toState (x : Dense R) : (mat4Dense x).toState = mat4Blocks x.toState := by
  funext i
  fin_cases i <;>
    simp [mat4Dense, mat4_eq, mat4Blocks, m4_mulVec, Dense.toState]

theorem addSums_toState (y : Dense R) :
    (addSums y).toState =
      fun i => y.toState i + positionSums y.toState ⟨i.val % 4, by omega⟩ := by
  funext i
  fin_cases i <;>
    simp [addSums, positionSums, Fin.sum_univ_four, Dense.toState, add_assoc]

/-- **The external layer is the transcription of `mds_light_permutation`.** -/
theorem externalDense_toState (x : Dense R) :
    (externalDense x).toState = mdsLight x.toState := by
  rw [externalDense, addSums_toState, mat4Dense_toState]
  rfl

end Layers

section Field

variable {K : Type*} [Field K]

/-- **The external layer is `Plonky3.external`.** -/
theorem externalDense_toState_external (h35 : (35 : K) ≠ 0) (x : Dense K) :
    (externalDense x).toState = external h35 x.toState := by
  rw [externalDense_toState, external_eq_mdsLight]

namespace Diag

/-- **The internal layer is `Plonky3.Diag.internal`**, coordinate by coordinate, for every
diagonal. -/
theorem internalDense_toState_apply (d : Dense K) (c : K) (x : Dense K) (i : Fin 16) :
    (internalDense d c x).toState i = c * (d.toState i * x.toState i + ∑ j, x.toState j) := by
  rw [Dense.sum_toState]
  fin_cases i <;> rfl

theorem internalDense_toState (d : Dense K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d.toState i ≠ 0)
    (hs : 1 + ∑ i, (d.toState i)⁻¹ ≠ 0) (x : Dense K) :
    (internalDense d c x).toState = internal d.toState c hc hd hs x.toState := by
  funext i
  rw [internalDense_toState_apply, internal_apply]

variable {d : Dense K} {c : K}

/-- **Each round of the runner is the specification's round**, for every diagonal and every round
index `n`, including the indices `n ≥ 8 + rP` past the schedule, where the mask is empty. -/
theorem roundDense_toState (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (n : ℕ) (x : Dense K) :
    (roundDense d c rP sbox values n x).toState = (rounds hD rP sbox values n).apply x.toState := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, linear, Hades.hadesMask,
    roundDense]
  by_cases h1 : n < 4
  · simp only [h1, if_true, true_or]
    rw [externalDense_toState_external hD.thirtyFive, maskedEquiv_univ, sboxAll_toState,
      addRow_toState]
  by_cases h2 : n < 4 + rP
  · simp only [h1, h2, if_true, if_false, false_or, show ¬(4 + rP ≤ n) by omega]
    rw [internalDense_toState d c hD.scale hD.diag hD.shermanMorrison, maskedEquiv_zero,
      sboxFirst_toState, addRow_toState]
  by_cases h3 : n < 4 + rP + 4
  · simp only [h1, h2, h3, if_true, if_false, show 4 + rP ≤ n by omega, or_true]
    rw [externalDense_toState_external hD.thirtyFive, maskedEquiv_univ, sboxAll_toState,
      addRow_toState]
  · simp only [h1, h2, h3, if_true, if_false, show 4 + rP ≤ n by omega, or_true]
    rw [externalDense_toState_external hD.thirtyFive, maskedEquiv_empty, addRow_toState]

/-- **The runner computes the specification state, for every diagonal.** For every input, every
round-constant table and every number `n` of rounds, the runner's state after `n` rounds is
`Hades.execute (Plonky3.Diag.rounds hD rP sbox values) x n`. -/
theorem executeDense_toState (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Dense K) (n : ℕ) :
    (executeDense d c rP sbox values x n).toState =
      Hades.execute (rounds hD rP sbox values) x.toState n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [executeDense, roundDense_toState hD, ih, Hades.execute_succ]

/-- The same, starting from a specification state. -/
theorem execute_eq_executeDense (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Fin 16 → K) (n : ℕ) :
    Hades.execute (rounds hD rP sbox values) x n =
      (executeDense d c rP sbox values (Dense.ofState x) n).toState := by
  rw [executeDense_toState hD, Dense.toState_ofState]

/-- **The runner's permutation is the specification's permutation, for every diagonal.** -/
theorem permutationDense_toState (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Dense K) :
    (permutationDense d c rP sbox values x).toState =
      permutation hD rP sbox values x.toState := by
  rw [permutationDense, executeDense_toState hD, externalDense_toState_external hD.thirtyFive]
  rfl

/-- The same, starting from a specification state. -/
theorem permutation_eq_permutationDense (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Fin 16 → K) :
    permutation hD rP sbox values x =
      (permutationDense d c rP sbox values (Dense.ofState x)).toState := by
  rw [permutationDense_toState hD, Dense.toState_ofState]

/-- **Transfer of a computed value, for every diagonal.** If the runner sends `Dense.ofState x`
to `Dense.ofState y`, then the specification's permutation sends `x` to `y`. -/
theorem permutation_eq_of_dense (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K}
    (h : permutationDense d c rP sbox values (Dense.ofState x) = Dense.ofState y) :
    permutation hD rP sbox values x = y := by
  rw [permutation_eq_permutationDense hD, h, Dense.toState_ofState]

/-- **Transfer of a computed inequality, for every diagonal.** If the runner does not send
`Dense.ofState x` to `Dense.ofState y`, neither does the specification's permutation. -/
theorem permutation_ne_of_dense (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K}
    (h : permutationDense d c rP sbox values (Dense.ofState x) ≠ Dense.ofState y) :
    permutation hD rP sbox values x ≠ y := by
  intro h'
  apply h
  apply Dense.toState_injective
  rw [← permutation_eq_permutationDense hD, h', Dense.toState_ofState]

/-- The transfer for a prefix of `n` rounds. -/
theorem execute_eq_of_dense (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K} {n : ℕ}
    (h : executeDense d c rP sbox values (Dense.ofState x) n = Dense.ofState y) :
    Hades.execute (rounds hD rP sbox values) x n = y := by
  rw [execute_eq_executeDense hD, h, Dense.toState_ofState]

/-- The transfer of an inequality for a prefix of `n` rounds. -/
theorem execute_ne_of_dense (hD : Conditions d.toState c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K} {n : ℕ}
    (h : executeDense d c rP sbox values (Dense.ofState x) n ≠ Dense.ofState y) :
    Hades.execute (rounds hD rP sbox values) x n ≠ y := by
  intro h'
  apply h
  apply Dense.toState_injective
  rw [← execute_eq_executeDense hD, h', Dense.toState_ofState]

end Diag

/-! ### The SP1 runner against the specification -/

/-- `sp1DiagDense` is the SP1 diagonal `Plonky3.sp1Diag`. -/
theorem sp1DiagDense_toState : (sp1DiagDense : Dense K).toState = sp1Diag K := by
  funext i
  fin_cases i <;> rfl

/-- **The internal layer is `Plonky3.internal c`**, coordinate by coordinate
(`Diag.internalDense_toState_apply` at `d = sp1DiagDense`). -/
theorem internalDense_toState_apply (c : K) (x : Dense K) (i : Fin 16) :
    (internalDense c x).toState i = c * (sp1Diag K i * x.toState i + ∑ j, x.toState j) := by
  rw [← sp1DiagDense_toState]
  exact Diag.internalDense_toState_apply sp1DiagDense c x i

theorem internalDense_toState (c : K) (hc : c ≠ 0) (h2 : (2 : K) ≠ 0) (hs : (81917 : K) ≠ 0)
    (x : Dense K) : (internalDense c x).toState = internal c hc h2 hs x.toState := by
  funext i
  rw [internalDense_toState_apply, internal_apply]

variable {c : K}

/-- The SP1 conditions, as the conditions of the generic runner at `d = sp1DiagDense`. -/
theorem Conditions.toDiagDense (hK : Conditions c) :
    Diag.Conditions (sp1DiagDense : Dense K).toState c := by
  rw [sp1DiagDense_toState]
  exact hK.toDiag

/-- **Each round of the runner is the specification's round**, for every round index `n`,
including the indices `n ≥ 8 + rP` past the schedule, where the mask is empty. -/
theorem roundDense_toState (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (n : ℕ) (x : Dense K) :
    (roundDense c rP sbox values n x).toState = (rounds hK rP sbox values n).apply x.toState :=
  Diag.roundDense_toState hK.toDiagDense rP sbox values n x

/-- **The runner computes the specification state.** For every input, every round-constant
table and every number `n` of rounds, the runner's state after `n` rounds is
`Hades.execute (rounds hK rP sbox values) x n`. -/
theorem executeDense_toState (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Dense K) (n : ℕ) :
    (executeDense c rP sbox values x n).toState =
      Hades.execute (rounds hK rP sbox values) x.toState n :=
  Diag.executeDense_toState hK.toDiagDense rP sbox values x n

/-- The same, starting from a specification state. -/
theorem execute_eq_executeDense (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Fin 16 → K) (n : ℕ) :
    Hades.execute (rounds hK rP sbox values) x n =
      (executeDense c rP sbox values (Dense.ofState x) n).toState :=
  Diag.execute_eq_executeDense hK.toDiagDense rP sbox values x n

/-- **The runner's permutation is the specification's permutation.** -/
theorem permutationDense_toState (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Dense K) :
    (permutationDense c rP sbox values x).toState = permutation hK rP sbox values x.toState :=
  Diag.permutationDense_toState hK.toDiagDense rP sbox values x

/-- The same, starting from a specification state. -/
theorem permutation_eq_permutationDense (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) (x : Fin 16 → K) :
    permutation hK rP sbox values x =
      (permutationDense c rP sbox values (Dense.ofState x)).toState :=
  Diag.permutation_eq_permutationDense hK.toDiagDense rP sbox values x

/-- **Transfer of a computed value.** If the runner sends `Dense.ofState x` to `Dense.ofState y`,
then the specification's permutation sends `x` to `y`. This is how `decide` on the runner yields
statements about `Plonky3.permutation`. -/
theorem permutation_eq_of_dense (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K}
    (h : permutationDense c rP sbox values (Dense.ofState x) = Dense.ofState y) :
    permutation hK rP sbox values x = y :=
  Diag.permutation_eq_of_dense hK.toDiagDense rP sbox values h

/-- **Transfer of a computed inequality.** If the runner does not send `Dense.ofState x` to
`Dense.ofState y`, neither does the specification's permutation. -/
theorem permutation_ne_of_dense (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K}
    (h : permutationDense c rP sbox values (Dense.ofState x) ≠ Dense.ofState y) :
    permutation hK rP sbox values x ≠ y :=
  Diag.permutation_ne_of_dense hK.toDiagDense rP sbox values h

/-- The transfer for a prefix of `n` rounds. -/
theorem execute_eq_of_dense (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K} {n : ℕ}
    (h : executeDense c rP sbox values (Dense.ofState x) n = Dense.ofState y) :
    Hades.execute (rounds hK rP sbox values) x n = y :=
  Diag.execute_eq_of_dense hK.toDiagDense rP sbox values h

/-- The transfer of an inequality for a prefix of `n` rounds. -/
theorem execute_ne_of_dense (hK : Conditions c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {x y : Fin 16 → K} {n : ℕ}
    (h : executeDense c rP sbox values (Dense.ofState x) n ≠ Dense.ofState y) :
    Hades.execute (rounds hK rP sbox values) x n ≠ y :=
  Diag.execute_ne_of_dense hK.toDiagDense rP sbox values h

end Field

end Poseidon2.Plonky3
