/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon.Starknet

/-!
# A materialised runner for Starknet's Poseidon permutation

`WideTrail.Poseidon.Starknet` defines the permutation through `Hades.execute`, a linear
equivalence and the masked S-box layer. This file gives a second implementation, written after
the loop of starkware-libs/cairo-lang tag `v0.14.0.1` (commit
`66355d7d99f1962ff9ccba8d0dbacbce3bd79bf8`), `src/starkware/cairo/common/poseidon_utils.py`
(`CL/` below), in which every coordinate is a named field and every step is written out
coordinate by coordinate, with no `LinearEquiv`, `Matrix` or `Finset` inside the computation.
It proves that the runner computes the specification, so that `decide` on the runner gives
statements about the specification (`Checks/Starknet.lean`).

## The runner

* `Dense`: three coordinates `x0, x1, x2`; `xj` is the code's `values[j]`. `toState` and
  `ofState` convert to and from `State = Fin 3 → F`.
* `cube x = x * x * x`, the code's `pow(val, 3, p)` (`CL/poseidon_utils.py:127`, `:129`).
* `addRow`: Add-Round Key, all three constants of the row (`:124`).
* `cubeAll`: SubWords of a full round (`:127`); `cubeLast`: SubWords of a partial round, on
  `values[-1]`, coordinate `2`, only (`:129`).
* `dotMod`: `SmallMds.dot_mod`, `(3 r0 + r1 + r2, r0 - r1 + r2, r0 + r1 - 2 r2)` (`:61-65`).
  `mixT` is the `mix` of the Rust code, `t = s0 + s1 + s2`, then `(t + 2 s0, t - 2 s1, t - 3 s2)`
  (lambdaworks-crypto `0.13.0` `src/hash/poseidon/starknet/parameters.rs:23-30`; eqlabs/pathfinder
  commit `00a1a74a90a7b8a7f1d07ac3e616be1cb39cf8f1` `crates/stark_poseidon/src/poseidon.rs:12-17`);
  `mixT_eq_dotMod` shows that the two compute the same map.
* `roundDense lin part table n`: a full round for `n < 4` and `87 ≤ n < 91`, a partial round
  with the step `part` for `4 ≤ n < 87` (`CL/poseidon_utils.py:122-153`), each ending with `lin`.
  For `n ≥ 91`, where the specification's mask is empty, it adds the row and applies `lin`.
* `executeDense`, `permutationDense lin part table x = executeDense lin part table x 91`, with
  no initial linear layer.

## Results

* `cube_eq_sbox`, `cubeAll_toState`, `cubeLast_toState`, `cubeFirst_toState`, `dotMod_toState`:
  the steps compute `x^3`, the full and partial masked S-box layers (masks `univ`, `{2}` and, for
  a control, `{0}`), and `mds`.
* For a step `lin` that computes a linear equivalence `L` and a step `part` that computes the
  masked layer with mask `mask`: `roundDense_toState` (each round is the round of
  `Hades.hadesSchedule 4 83 4 mask (fun _ _ => sbox) (fun _ => L) table`, for every table),
  `executeDense_toState`, `permutationDense_toState`, and the transfers
  `permutationWith_eq_of_dense`, `permutationWith_ne_of_dense`.
* `permutation_eq_permutationWith`, and the transfers for the pinned permutation,
  `permutation_eq_of_dense`, `permutation_ne_of_dense`, and `permutation_mds_ne_of_dense` for a
  control with an extra linear layer in front.

## What is not claimed

This file is a second implementation of the model, proved equal to it. It adds no claim about
the Python, Rust or Cairo code beyond the transcriptions cited above; it is not compiled from
that code, and nothing here concerns Montgomery representations or the AIR. No security
statement is made here.
-/

set_option autoImplicit false

namespace Poseidon.Starknet

/-! ### Materialised states -/

/-- A width-three state with one field per coordinate; `xj` is the code's `values[j]`. -/
structure Dense where
  x0 : F
  x1 : F
  x2 : F
  deriving DecidableEq

namespace Dense

/-- The specification's state `Fin 3 → F`. -/
def toState (x : Dense) : State := ![x.x0, x.x1, x.x2]

/-- The three coordinates of a specification state. -/
def ofState (x : State) : Dense := ⟨x 0, x 1, x 2⟩

theorem toState_ofState (x : State) : (ofState x).toState = x := by
  funext i
  fin_cases i <;> rfl

theorem ofState_toState (x : Dense) : ofState x.toState = x := by
  cases x
  rfl

theorem toState_injective : Function.Injective toState := by
  intro x y h
  rw [← ofState_toState x, h, ofState_toState]

end Dense

/-! ### The runner -/

/-- The cube `pow(val, 3, p)` (cairo-lang `v0.14.0.1`
`src/starkware/cairo/common/poseidon_utils.py:127`, `:129`), computed as `x * x * x`. -/
def cube (x : F) : F := x * x * x

/-- Add-Round Key: all three constants of the row (`poseidon_utils.py:124`). -/
def addRow (x : Dense) (v : State) : Dense :=
  ⟨x.x0 + v 0, x.x1 + v 1, x.x2 + v 2⟩

/-- SubWords of a full round: every coordinate is cubed (`poseidon_utils.py:127`). -/
def cubeAll (x : Dense) : Dense :=
  ⟨cube x.x0, cube x.x1, cube x.x2⟩

/-- SubWords of a partial round: only `values[-1]`, coordinate `2`, is cubed
(`poseidon_utils.py:129`). -/
def cubeLast (x : Dense) : Dense :=
  ⟨x.x0, x.x1, cube x.x2⟩

/-- A partial step on coordinate `0` instead, for a negative control only. -/
def cubeFirst (x : Dense) : Dense :=
  ⟨cube x.x0, x.x1, x.x2⟩

/-- **`SmallMds.dot_mod`** (`poseidon_utils.py:61-65`):
`(3 r0 + r1 + r2, r0 - r1 + r2, r0 + r1 - 2 r2)`. -/
def dotMod (x : Dense) : Dense :=
  ⟨3 * x.x0 + x.x1 + x.x2, x.x0 - x.x1 + x.x2, x.x0 + x.x1 - 2 * x.x2⟩

/-- **The Rust `mix`**: `t = s0 + s1 + s2`, then `(t + 2 s0, t - 2 s1, t - 3 s2)`
(lambdaworks-crypto `0.13.0` `src/hash/poseidon/starknet/parameters.rs:23-30`; pathfinder
`00a1a74` `crates/stark_poseidon/src/poseidon.rs:12-17`). -/
def mixT (x : Dense) : Dense :=
  let t := x.x0 + x.x1 + x.x2
  ⟨t + 2 * x.x0, t - 2 * x.x1, t - 3 * x.x2⟩

/-- **The Rust `mix` is `SmallMds.dot_mod`.** In particular its last row is `(1, 1, -2)`, not the
`(1, 1, 2)` of the comments at starknet-crypto `0.6.2` `src/poseidon_hash.rs:117` and pathfinder
`00a1a74` `crates/stark_poseidon/src/poseidon.rs:9`. -/
theorem mixT_eq_dotMod (x : Dense) : mixT x = dotMod x := by
  simp only [mixT, dotMod, Dense.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- Round `n` with linear step `lin` and partial step `part`: a full round for `n < 4` and
`87 ≤ n < 91`, a partial round for `4 ≤ n < 87` (cairo-lang `v0.14.0.1`
`src/starkware/cairo/common/poseidon_utils.py:122-153`). For `n ≥ 91` the row is added and `lin`
applied, as the specification's round with an empty mask does. -/
def roundDense (lin part : Dense → Dense) (table : ℕ → State) (n : ℕ) (x : Dense) : Dense :=
  if n < 4 then lin (cubeAll (addRow x (table n)))
  else if n < 87 then lin (part (addRow x (table n)))
  else if n < 91 then lin (cubeAll (addRow x (table n)))
  else lin (addRow x (table n))

/-- The first `n` rounds, from `x`. -/
def executeDense (lin part : Dense → Dense) (table : ℕ → State) (x : Dense) : ℕ → Dense
  | 0 => x
  | n + 1 => roundDense lin part table n (executeDense lin part table x n)

/-- The `91` rounds, with no initial linear layer (`poseidon_utils.py:136-153`). -/
def permutationDense (lin part : Dense → Dense) (table : ℕ → State) (x : Dense) : Dense :=
  executeDense lin part table x 91

/-! ### The steps against the specification -/

/-- The code's cube is the S-box `sbox`. -/
theorem cube_eq_sbox (x : F) : cube x = sbox x := by
  rw [sbox_apply, cube]
  ring

theorem addRow_toState (x : Dense) (v : State) : (addRow x v).toState = x.toState + v := by
  funext i
  fin_cases i <;> rfl

theorem cubeAll_toState (x : Dense) :
    (cubeAll x).toState = Hades.maskedEquiv Finset.univ (fun _ => sbox) x.toState := by
  funext i
  fin_cases i <;> simp [cubeAll, Dense.toState, cube_eq_sbox]

theorem cubeLast_toState (x : Dense) :
    (cubeLast x).toState = Hades.maskedEquiv ({2} : Finset (Fin 3)) (fun _ => sbox) x.toState := by
  funext i
  fin_cases i <;> simp [cubeLast, Dense.toState, cube_eq_sbox]

theorem cubeFirst_toState (x : Dense) :
    (cubeFirst x).toState = Hades.maskedEquiv ({0} : Finset (Fin 3)) (fun _ => sbox) x.toState := by
  funext i
  fin_cases i <;> simp [cubeFirst, Dense.toState, cube_eq_sbox]

/-- **`SmallMds.dot_mod` computes `mds`.** -/
theorem dotMod_toState (x : Dense) : (dotMod x).toState = mds x.toState := by
  rw [mds_apply]
  funext i
  fin_cases i <;> rfl

theorem maskedEquiv_empty (y : State) :
    Hades.maskedEquiv (∅ : Finset (Fin 3)) (fun _ => sbox) y = y := by
  funext i
  simp

/-! ### Rounds against the specification -/

/-- The `91` rounds with linear layer `L` in every round, partial mask `mask` and round
constants `table`, with no initial layer. -/
def permutationWith (L : State ≃ₗ[F] State) (mask : Finset (Fin 3)) (table : ℕ → State)
    (x : State) : State :=
  Hades.execute (Hades.hadesSchedule 4 83 4 mask (fun _ _ => sbox) (fun _ => L) table) x 91

theorem permutation_eq_permutationWith : permutation = permutationWith mds {2} values :=
  rfl

section Transfer

variable {lin part : Dense → Dense} {L : State ≃ₗ[F] State} {mask : Finset (Fin 3)}

/-- **Each round of the runner is the specification's round**, for every table and every
round index `n`, when `lin` computes `L` and `part` computes the masked layer with mask
`mask`. -/
theorem roundDense_toState (hL : ∀ x, (lin x).toState = L x.toState)
    (hP : ∀ x, (part x).toState = Hades.maskedEquiv mask (fun _ => sbox) x.toState)
    (table : ℕ → State) (n : ℕ) (x : Dense) :
    (roundDense lin part table n x).toState =
      (Hades.hadesSchedule 4 83 4 mask (fun _ _ => sbox) (fun _ => L) table n).apply
        x.toState := by
  simp only [Hades.hadesSchedule, Hades.RoundSpec.apply, Hades.hadesMask, roundDense]
  by_cases h1 : n < 4
  · simp only [h1, if_true]
    rw [hL, cubeAll_toState, addRow_toState]
  by_cases h2 : n < 87
  · simp only [h1, h2, if_true, if_false]
    rw [hL, hP, addRow_toState]
  by_cases h3 : n < 91
  · simp only [h1, h2, h3, if_true, if_false]
    rw [hL, cubeAll_toState, addRow_toState]
  · simp only [h1, h2, h3, if_false]
    rw [hL, addRow_toState, maskedEquiv_empty]

/-- **The runner computes the specification state.** For every input and every number `n` of
rounds, the runner's state after `n` rounds is the specification's. -/
theorem executeDense_toState (hL : ∀ x, (lin x).toState = L x.toState)
    (hP : ∀ x, (part x).toState = Hades.maskedEquiv mask (fun _ => sbox) x.toState)
    (table : ℕ → State) (x : Dense) (n : ℕ) :
    (executeDense lin part table x n).toState =
      Hades.execute (Hades.hadesSchedule 4 83 4 mask (fun _ _ => sbox) (fun _ => L) table)
        x.toState n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [executeDense, roundDense_toState hL hP, ih, Hades.execute_succ]

/-- **The runner's permutation is the specification's permutation.** -/
theorem permutationDense_toState (hL : ∀ x, (lin x).toState = L x.toState)
    (hP : ∀ x, (part x).toState = Hades.maskedEquiv mask (fun _ => sbox) x.toState)
    (table : ℕ → State) (x : Dense) :
    (permutationDense lin part table x).toState = permutationWith L mask table x.toState :=
  executeDense_toState hL hP table x 91

/-- **Transfer of a computed value.** If the runner sends `Dense.ofState x` to `Dense.ofState y`,
then the specification's permutation sends `x` to `y`. -/
theorem permutationWith_eq_of_dense (hL : ∀ x, (lin x).toState = L x.toState)
    (hP : ∀ x, (part x).toState = Hades.maskedEquiv mask (fun _ => sbox) x.toState)
    {table : ℕ → State} {x y : State}
    (h : permutationDense lin part table (Dense.ofState x) = Dense.ofState y) :
    permutationWith L mask table x = y := by
  rw [← Dense.toState_ofState x, ← permutationDense_toState hL hP, h, Dense.toState_ofState]

/-- **Transfer of a computed inequality.** If the runner does not send `Dense.ofState x` to
`Dense.ofState y`, neither does the specification's permutation. -/
theorem permutationWith_ne_of_dense (hL : ∀ x, (lin x).toState = L x.toState)
    (hP : ∀ x, (part x).toState = Hades.maskedEquiv mask (fun _ => sbox) x.toState)
    {table : ℕ → State} {x y : State}
    (h : permutationDense lin part table (Dense.ofState x) ≠ Dense.ofState y) :
    permutationWith L mask table x ≠ y := by
  intro h'
  apply h
  apply Dense.toState_injective
  rw [permutationDense_toState hL hP, Dense.toState_ofState, h', Dense.toState_ofState]

end Transfer

/-! ### The pinned permutation -/

/-- **Transfer for the pinned permutation.** If the runner with `SmallMds.dot_mod`, the partial
step on coordinate `2` and the pinned table sends `Dense.ofState x` to `Dense.ofState y`, then
`permutation x = y`. -/
theorem permutation_eq_of_dense {x y : State}
    (h : permutationDense dotMod cubeLast values (Dense.ofState x) = Dense.ofState y) :
    permutation x = y :=
  permutationWith_eq_of_dense dotMod_toState cubeLast_toState h

/-- **Transfer of an inequality for the pinned permutation.** -/
theorem permutation_ne_of_dense {x y : State}
    (h : permutationDense dotMod cubeLast values (Dense.ofState x) ≠ Dense.ofState y) :
    permutation x ≠ y :=
  permutationWith_ne_of_dense dotMod_toState cubeLast_toState h

/-- **Transfer of an inequality with an extra linear layer in front**, for a control: if the
runner, started from `dotMod (Dense.ofState x)`, does not reach `Dense.ofState y`, then
`permutation (mds x) ≠ y`. -/
theorem permutation_mds_ne_of_dense {x y : State}
    (h : permutationDense dotMod cubeLast values (dotMod (Dense.ofState x)) ≠ Dense.ofState y) :
    permutation (mds x) ≠ y := by
  intro h'
  apply h
  apply Dense.toState_injective
  rw [permutationDense_toState dotMod_toState cubeLast_toState, dotMod_toState,
    Dense.toState_ofState, Dense.toState_ofState, ← permutation_eq_permutationWith, h']

end Poseidon.Starknet
