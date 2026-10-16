import WideTrail.Poseidon2.BN254

/-! Materialized execution, proved equal to the function-valued specification. -/

set_option autoImplicit false

namespace Poseidon2.BN254

/-- A data carrier forces every round's coordinates to be evaluated once. -/
structure DenseState where
  a : F
  b : F
  c : F

def materialize (x : State) : DenseState := ⟨x 0, x 1, x 2⟩

def DenseState.toState (x : DenseState) : State := ![x.a, x.b, x.c]

theorem materialize_toState (x : State) : (materialize x).toState = x := by
  funext i
  fin_cases i <;> rfl

def executeDense (x : DenseState) : Nat → DenseState
  | 0 => x
  | n + 1 => materialize ((rounds n).apply ((executeDense x n).toState))

theorem executeDense_eq (x : DenseState) (n : Nat) :
    (executeDense x n).toState = Hades.execute rounds x.toState n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [executeDense, materialize_toState, ih, Hades.execute_succ]

def executeCached (x : State) (n : Nat) : State := (executeDense (materialize x) n).toState

/-- Every cached intermediate state equals its specification state. -/
theorem executeCached_eq (x : State) (n : Nat) :
    executeCached x n = Hades.execute rounds x n := by
  rw [executeCached, executeDense_eq, materialize_toState]

def permutationCached (x : State) : State := executeCached (external x) 64

theorem permutationCached_eq (x : State) : permutationCached x = permutation x := by
  unfold permutationCached permutation
  exact executeCached_eq (external x) 64

end Poseidon2.BN254
