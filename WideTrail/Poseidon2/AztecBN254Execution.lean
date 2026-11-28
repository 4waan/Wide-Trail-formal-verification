/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.AztecBN254

/-!
# A materialised runner for the Aztec and Noir BN254 width-four permutation

`WideTrail.Poseidon2.AztecBN254` defines the permutation through `Hades.execute`, linear
equivalences and finite sums over `Fin 4`. This file gives a second implementation, written
after the code's loop, in which every coordinate is a named field and every step is written out
coordinate by coordinate, with no `LinearEquiv`, `Matrix` or `Finset` inside the computation. It
proves that the runner computes the specification, so that `decide` on the runner gives
statements about the specification (`Checks/AztecBN254.lean`).

`P2/` abbreviates `barretenberg/cpp/src/barretenberg/crypto/poseidon2/` of aztec-packages tag
`v1.0.0` (commit `79e9bd1698f4bba6deade8f76c676f9bbb12ff74`), and `NS/` abbreviates
`acvm-repo/bn254_blackbox_solver/src/` of noir tag `v1.0.0` (commit
`275d3ab1a5c916c6ea73e8d6b943f685f574500c`).

## The runner

* `Dense`: four coordinates `x0, …, x3`; `xi` is the code's `state[i]`. `toState` and `ofState`
  convert to and from `State = Fin 4 → F`.
* `sboxDense`: `xx = x * x`, `xxxx = xx * xx`, `x * xxxx` (`P2/poseidon2_permutation.hpp:115-121`).
* `mat4`: the addition chain of `matrix_multiplication_4x4` (`P2/poseidon2_permutation.hpp:65-82`;
  the same chain in `NS/poseidon2.rs:50-67`), in the code's order, with outputs
  `(t6, t5, t7, t4)`.
* `internalDense d`: `sum = x0 + x1 + x2 + x3`, then `state[i] * d_i + sum`
  (`P2/poseidon2_permutation.hpp:92-103`; `NS/poseidon2.rs:70-79`), for a diagonal `d : Dense`.
* `roundDense ext int table n`: a full round for `n < 4` and `60 ≤ n < 64` (all four constants,
  the S-box on every coordinate, then `ext`; `P2/poseidon2_permutation.hpp:147-151`, `:162-166`);
  a partial round for `4 ≤ n < 60` that adds only `table n 0` to `state[0]`, applies the S-box to
  `state[0]` and then `int` (`:155-159`). For `n ≥ 64`, where the specification's mask is empty,
  it adds the row and applies `ext`.
* `executeDense`, `permutationDense ext int table x = executeDense ext int table (ext x) 64`
  (the initial layer at `P2/poseidon2_permutation.hpp:143`).

## Results

* `sboxDense_eq`, `mat4_toState`, `internalDense_toState_apply`: the three steps compute `x^5`,
  `external` (the rows of `hlMat4`) and `d_i x_i + ∑ x_j`.
* For layers `ext`, `int` that compute linear equivalences `E`, `I`
  (`hE : ∀ x, (ext x).toState = E x.toState`, likewise `hI`), and every table that is zero off
  coordinate `0` in rows `4` to `59` (`PartialRowsAtZero`): `roundDense_toState` (each round is
  the round of `roundsWith E I table`), `executeDense_toState`, `permutationDense_toState`, and
  the transfers `permutationWith_eq_of_dense`, `permutationWith_ne_of_dense`,
  `execute_ne_of_dense`.
* `roundsWith external internal values = rounds` and
  `permutationWith external internal values = permutation` (`rounds_eq_roundsWith`,
  `permutation_eq_permutationWith`), and the transfers for the pinned permutation,
  `permutation_eq_of_dense`, `permutation_ne_of_dense`.

The partial-round step of the runner adds the constant to `state[0]` only, as the code does; it
equals the specification's round, which adds the whole row, because the table is zero off
coordinate `0` in those rows (`values_partialRowsAtZero`).

## What is not claimed

This file is a second implementation of the model, proved equal to it. It adds no claim about
the C++ or Rust code beyond the transcriptions cited above; it is not compiled from that code,
and nothing here concerns Montgomery representations, the circuit gadgets or the relations. No
security statement is made here.
-/

set_option autoImplicit false

namespace Poseidon2.AztecBN254

open Poseidon2.BN254 (F sbox sbox_toFun)

/-! ### Materialised states -/

/-- A width-four state with one field per coordinate; `xi` is the code's `state[i]`. -/
structure Dense where
  x0 : F
  x1 : F
  x2 : F
  x3 : F
  deriving DecidableEq

namespace Dense

/-- The specification's state `Fin 4 → F`. -/
def toState (x : Dense) : State := ![x.x0, x.x1, x.x2, x.x3]

/-- The four coordinates of a specification state. -/
def ofState (x : State) : Dense := ⟨x 0, x 1, x 2, x 3⟩

theorem toState_ofState (x : State) : (ofState x).toState = x := by
  funext i
  fin_cases i <;> rfl

theorem ofState_toState (x : Dense) : ofState x.toState = x := by
  cases x
  rfl

theorem toState_injective : Function.Injective toState := by
  intro x y h
  rw [← ofState_toState x, h, ofState_toState]

theorem sum_toState (x : Dense) : ∑ j, x.toState j = x.x0 + x.x1 + x.x2 + x.x3 := by
  rw [Fin.sum_univ_four]
  rfl

end Dense

/-! ### The runner -/

/-- The S-box as `apply_single_sbox` computes it (`P2/poseidon2_permutation.hpp:115-121`):
`xx = x * x`, `xxxx = xx * xx`, then `x * xxxx`. -/
def sboxDense (x : F) : F :=
  let xx := x * x
  let xxxx := xx * xx
  x * xxxx

/-- Add a row of round constants to every coordinate (`add_round_constants`,
`P2/poseidon2_permutation.hpp:85-90`). -/
def addRow (x : Dense) (v : State) : Dense :=
  ⟨x.x0 + v 0, x.x1 + v 1, x.x2 + v 2, x.x3 + v 3⟩

/-- Add a constant to coordinate `0` only (`P2/poseidon2_permutation.hpp:156`). -/
def addFirst (x : Dense) (c : F) : Dense :=
  ⟨x.x0 + c, x.x1, x.x2, x.x3⟩

/-- The S-box on every coordinate (`apply_sbox`, `P2/poseidon2_permutation.hpp:123-128`). -/
def sboxAll (x : Dense) : Dense :=
  ⟨sboxDense x.x0, sboxDense x.x1, sboxDense x.x2, sboxDense x.x3⟩

/-- The S-box on coordinate `0` only (`P2/poseidon2_permutation.hpp:157`). -/
def sboxFirst (x : Dense) : Dense :=
  ⟨sboxDense x.x0, x.x1, x.x2, x.x3⟩

/-- **The addition chain of `matrix_multiplication_4x4`** (`P2/poseidon2_permutation.hpp:65-82`;
`NS/poseidon2.rs:50-67`), step by step: `input[0..3] = (t6, t5, t7, t4)`. -/
def mat4 (x : Dense) : Dense :=
  let t0 := x.x0 + x.x1
  let t1 := x.x2 + x.x3
  let t2a := x.x1 + x.x1
  let t2 := t2a + t1
  let t3a := x.x3 + x.x3
  let t3 := t3a + t0
  let t4a := t1 + t1
  let t4b := t4a + t4a
  let t4 := t4b + t3
  let t5a := t0 + t0
  let t5b := t5a + t5a
  let t5 := t5b + t2
  let t6 := t3 + t5
  let t7 := t2 + t4
  ⟨t6, t5, t7, t4⟩

/-- **`matrix_multiplication_internal`** (`P2/poseidon2_permutation.hpp:92-103`) for a diagonal
`d`: `sum = x0 + x1 + x2 + x3`, then coordinate `i` becomes `x_i * d_i + sum`. -/
def internalDense (d : Dense) (x : Dense) : Dense :=
  let sum := x.x0 + x.x1 + x.x2 + x.x3
  ⟨x.x0 * d.x0 + sum, x.x1 * d.x1 + sum, x.x2 * d.x2 + sum, x.x3 * d.x3 + sum⟩

/-- The pinned diagonal `internalDiag` as a runner state (`diagDense_toState`). -/
def diagDense : Dense :=
  ⟨0x10dc6e9c006ea38b04b1e03b4bd9490c0d03f98929ca1d7fb56821fd19d3b6e7,
    0x0c28145b6a44df3e0149b3d0a30b3bb599df9756d4dd9b84a86b38cfb45a740b,
    0x00544b8338791518b2c7645a50392798b21f75bb60e3596170067d00141cac15,
    0x222c01175718386f2e2e82eb122789e352e105a3b8fa852613bc534433ee428b⟩

/-- Round `n` of the code's loop with external step `ext` and internal step `int`: full rounds
for `n < 4` and `60 ≤ n < 64` (`P2/poseidon2_permutation.hpp:147-151`, `:162-166`), partial
rounds adding `table n 0` to `state[0]` only for `4 ≤ n < 60` (`:155-159`). For `n ≥ 64` the row
is added and `ext` applied, as the specification's round with an empty mask does. -/
def roundDense (ext int : Dense → Dense) (table : ℕ → State) (n : ℕ) (x : Dense) : Dense :=
  if n < 4 then ext (sboxAll (addRow x (table n)))
  else if n < 60 then int (sboxFirst (addFirst x (table n 0)))
  else if n < 64 then ext (sboxAll (addRow x (table n)))
  else ext (addRow x (table n))

/-- The first `n` rounds, from `x`. -/
def executeDense (ext int : Dense → Dense) (table : ℕ → State) (x : Dense) : ℕ → Dense
  | 0 => x
  | n + 1 => roundDense ext int table n (executeDense ext int table x n)

/-- The initial external step (`P2/poseidon2_permutation.hpp:143`), then the `64` rounds. -/
def permutationDense (ext int : Dense → Dense) (table : ℕ → State) (x : Dense) : Dense :=
  executeDense ext int table (ext x) 64

/-! ### The steps against the specification -/

/-- The code's S-box is `x^5`, the S-box `sbox`. -/
theorem sboxDense_eq (x : F) : sboxDense x = sbox x := by
  rw [sbox_toFun]
  simp only [sboxDense]
  ring

theorem addRow_toState (x : Dense) (v : State) : (addRow x v).toState = x.toState + v := by
  funext i
  fin_cases i <;> rfl

theorem sboxAll_toState (x : Dense) : (sboxAll x).toState = fun i => sbox (x.toState i) := by
  funext i
  fin_cases i <;> simp [sboxAll, Dense.toState, sboxDense_eq]

/-- **The addition chain computes `hlMat4`**: `mat4` is the external layer `external`. -/
theorem mat4_toState (x : Dense) : (mat4 x).toState = external x.toState := by
  rw [external_apply]
  funext i
  fin_cases i <;> simp [mat4, Dense.toState] <;> ring

/-- Coordinate `i` of `internalDense d x` is `d_i x_i + ∑_j x_j`. -/
theorem internalDense_toState_apply (d x : Dense) (i : Fin 4) :
    (internalDense d x).toState i = d.toState i * x.toState i + ∑ j, x.toState j := by
  rw [Dense.sum_toState]
  fin_cases i <;> simp [internalDense, Dense.toState] <;> ring

theorem diagDense_toState : diagDense.toState = internalDiag := by
  funext i
  fin_cases i <;> rfl

/-- **The code's internal step with the pinned diagonal is `internal`.** -/
theorem internalDense_toState (x : Dense) :
    (internalDense diagDense x).toState = internal x.toState := by
  funext i
  rw [internalDense_toState_apply, internal_apply, diagDense_toState]

/-! ### Rounds against the specification -/

/-- The linear layers of the HADES schedule with external layer `E` and internal layer `I`. -/
def linearWith (E I : State ≃ₗ[F] State) (n : ℕ) : State ≃ₗ[F] State :=
  if n < 4 ∨ 60 ≤ n then E else I

/-- The `64` rounds with external layer `E`, internal layer `I` and round constants `table`. -/
def roundsWith (E I : State ≃ₗ[F] State) (table : ℕ → State) : ℕ → Hades.RoundSpec (Fin 4) F :=
  Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) (linearWith E I) table

/-- The permutation with initial layer `E`, then the `64` rounds of `roundsWith E I table`. -/
def permutationWith (E I : State ≃ₗ[F] State) (table : ℕ → State) (x : State) : State :=
  Hades.execute (roundsWith E I table) (E x) 64

theorem rounds_eq_roundsWith : rounds = roundsWith external internal values :=
  rfl

theorem permutation_eq_permutationWith :
    permutation = permutationWith external internal values :=
  rfl

/-- A table whose rows `4` to `59` are zero off coordinate `0`. -/
def PartialRowsAtZero (table : ℕ → State) : Prop :=
  ∀ j < 56, ∀ i : Fin 4, i ≠ 0 → table (4 + j) i = 0

theorem values_partialRowsAtZero : PartialRowsAtZero values :=
  fun j hj i hi => partial_constants_zero ⟨j, hj⟩ i hi

theorem maskedEquiv_univ (y : State) :
    Hades.maskedEquiv Finset.univ (fun _ => sbox) y = fun i => sbox (y i) := by
  funext i
  simp

theorem maskedEquiv_empty (y : State) :
    Hades.maskedEquiv (∅ : Finset (Fin 4)) (fun _ => sbox) y = y := by
  funext i
  simp

/-- The partial-round step: adding `c` at coordinate `0` and the S-box there is the masked
layer on `x + v`, when `v` is `c` at coordinate `0` and zero elsewhere. -/
theorem sboxFirst_addFirst_toState (x : Dense) (v : State) (hv : ∀ i : Fin 4, i ≠ 0 → v i = 0) :
    (sboxFirst (addFirst x (v 0))).toState =
      Hades.maskedEquiv ({0} : Finset (Fin 4)) (fun _ => sbox) (x.toState + v) := by
  funext i
  rw [Hades.maskedEquiv_apply, Hades.maskedBricklayer_apply, Pi.add_apply]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos (Finset.mem_singleton_self 0)]
    exact sboxDense_eq _
  · rw [if_neg (by simpa using hi), hv i hi, add_zero]
    fin_cases i
    · exact absurd rfl hi
    · rfl
    · rfl
    · rfl

section Transfer

variable {ext int : Dense → Dense} {E I : State ≃ₗ[F] State}

/-- **Each round of the runner is the specification's round**, for every round index `n`, when
`ext` and `int` compute `E` and `I` and the table is zero off coordinate `0` in the partial
rows. -/
theorem roundDense_toState (hE : ∀ x, (ext x).toState = E x.toState)
    (hI : ∀ x, (int x).toState = I x.toState) {table : ℕ → State}
    (ht : PartialRowsAtZero table) (n : ℕ) (x : Dense) :
    (roundDense ext int table n x).toState = (roundsWith E I table n).apply x.toState := by
  simp only [roundsWith, Hades.hadesSchedule, Hades.RoundSpec.apply, linearWith,
    Hades.hadesMask, roundDense]
  by_cases h1 : n < 4
  · simp only [h1, if_true, true_or]
    rw [hE, sboxAll_toState, addRow_toState, maskedEquiv_univ]
  by_cases h2 : n < 60
  · simp only [h1, h2, if_true, if_false, false_or, show ¬(60 ≤ n) by omega]
    rw [hI]
    congr 1
    obtain ⟨j, rfl⟩ : ∃ j, n = 4 + j := ⟨n - 4, by omega⟩
    exact sboxFirst_addFirst_toState x _ (ht j (by omega))
  by_cases h3 : n < 64
  · simp only [h1, h2, h3, if_true, if_false, show 60 ≤ n by omega, or_true]
    rw [hE, sboxAll_toState, addRow_toState, maskedEquiv_univ]
  · simp only [h1, h2, h3, if_false, show 60 ≤ n by omega, or_true, if_true]
    rw [hE, addRow_toState, maskedEquiv_empty]

/-- **The runner computes the specification state.** For every input and every number `n` of
rounds, the runner's state after `n` rounds is `Hades.execute (roundsWith E I table) x n`. -/
theorem executeDense_toState (hE : ∀ x, (ext x).toState = E x.toState)
    (hI : ∀ x, (int x).toState = I x.toState) {table : ℕ → State}
    (ht : PartialRowsAtZero table) (x : Dense) (n : ℕ) :
    (executeDense ext int table x n).toState =
      Hades.execute (roundsWith E I table) x.toState n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [executeDense, roundDense_toState hE hI ht, ih, Hades.execute_succ]

/-- **The runner's permutation is the specification's permutation.** -/
theorem permutationDense_toState (hE : ∀ x, (ext x).toState = E x.toState)
    (hI : ∀ x, (int x).toState = I x.toState) {table : ℕ → State}
    (ht : PartialRowsAtZero table) (x : Dense) :
    (permutationDense ext int table x).toState = permutationWith E I table x.toState := by
  rw [permutationDense, executeDense_toState hE hI ht, hE]
  rfl

/-- **Transfer of a computed value.** If the runner sends `Dense.ofState x` to `Dense.ofState y`,
then the specification's permutation sends `x` to `y`. -/
theorem permutationWith_eq_of_dense (hE : ∀ x, (ext x).toState = E x.toState)
    (hI : ∀ x, (int x).toState = I x.toState) {table : ℕ → State}
    (ht : PartialRowsAtZero table) {x y : State}
    (h : permutationDense ext int table (Dense.ofState x) = Dense.ofState y) :
    permutationWith E I table x = y := by
  rw [← Dense.toState_ofState x, ← permutationDense_toState hE hI ht, h, Dense.toState_ofState]

/-- **Transfer of a computed inequality.** If the runner does not send `Dense.ofState x` to
`Dense.ofState y`, neither does the specification's permutation. -/
theorem permutationWith_ne_of_dense (hE : ∀ x, (ext x).toState = E x.toState)
    (hI : ∀ x, (int x).toState = I x.toState) {table : ℕ → State}
    (ht : PartialRowsAtZero table) {x y : State}
    (h : permutationDense ext int table (Dense.ofState x) ≠ Dense.ofState y) :
    permutationWith E I table x ≠ y := by
  intro h'
  apply h
  apply Dense.toState_injective
  rw [permutationDense_toState hE hI ht, Dense.toState_ofState, h', Dense.toState_ofState]

/-- The transfer of an inequality for the `64` rounds without the initial layer. -/
theorem execute_ne_of_dense (hE : ∀ x, (ext x).toState = E x.toState)
    (hI : ∀ x, (int x).toState = I x.toState) {table : ℕ → State}
    (ht : PartialRowsAtZero table) {x y : State}
    (h : executeDense ext int table (Dense.ofState x) 64 ≠ Dense.ofState y) :
    Hades.execute (roundsWith E I table) x 64 ≠ y := by
  intro h'
  apply h
  apply Dense.toState_injective
  rw [executeDense_toState hE hI ht, Dense.toState_ofState, h', Dense.toState_ofState]

end Transfer

/-! ### The pinned permutation -/

/-- **Transfer for the pinned permutation.** If the runner with the code's chain `mat4`, the
pinned diagonal and the pinned table sends `Dense.ofState x` to `Dense.ofState y`, then
`permutation x = y`. -/
theorem permutation_eq_of_dense {x y : State}
    (h : permutationDense mat4 (internalDense diagDense) values (Dense.ofState x) =
      Dense.ofState y) :
    permutation x = y :=
  permutationWith_eq_of_dense mat4_toState internalDense_toState values_partialRowsAtZero h

/-- **Transfer of an inequality for the pinned permutation.** -/
theorem permutation_ne_of_dense {x y : State}
    (h : permutationDense mat4 (internalDense diagDense) values (Dense.ofState x) ≠
      Dense.ofState y) :
    permutation x ≠ y :=
  permutationWith_ne_of_dense mat4_toState internalDense_toState values_partialRowsAtZero h

end Poseidon2.AztecBN254
