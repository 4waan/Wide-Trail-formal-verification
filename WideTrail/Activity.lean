import Mathlib.Data.Fintype.Card

/-
- mathlib's matrix is a state (a function)
- Matrix m → n → α is defined at Matrix/Defs.lean:57 as m → n → α.
- its just a function type.. not a struct or array or anything
- Matrix.of is Equiv.refl, a definitional no-op that exists only so
- instance resolution can tell "matrix multiplication" apart from
- "elementwise Pi multiplication" on the same underlying type.
- So indexing a state by position and indexing a matrix by (row, col)
- are the same operation.
- Start flat with ι → K; column/bundle structure enters later,
- only where the dispersion property needs it.
-/

variable {Idx K : Type*} [Zero K] [DecidableEq K] [Fintype Idx]

def activePattern (s : Idx -> K) : Finset Idx := Finset.univ.filter (fun i => Ne (s i) 0)
def weight (s : Idx -> K) : Nat := (activePattern s).card
def colWeight (col : Idx -> Col) (s : Idx -> K) : N := ((activePattern s).image col).Card
def isBranchBound (col : Idx -> Col) (psi : (Idx -> K) -> (Idx -> K)) (B: N) : Prop :=
  forall a ≠ 0, B ≤ colWeight col a + colWeight col (psi a)

@[simp]
theorem mem_activePattern {s : Idx -> K} {i : Idx} :
    Iff (Membership.mem (activePattern s) i) (Ne (s i) 0) := by
  simp [activePattern]

@[simp]
theorem colWeight_id : colWeight id s = weight s
