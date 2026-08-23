import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
# Wide Trail: states active patterns and branch numbers

difference pattern is a state `Idx -> K`. Only the *support*
matters.. the S box layer costs probability at position `i` exactly
when the pattern there is not 0. so 'K' needs no arithmetic beyond distinct `0`
-/

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Col]

/-- The set of active positions (pattern is nonzero)-/
def activePattern (s : Idx -> K) : Finset Idx := Finset.univ.filter (fun i => Ne (s i) ≠ 0)

/-- bundle weight `w_b` (numbr of active S boxes in this pattern)-/
def weight (s : Idx -> K) : Nat := (activePattern s).card

/-- weight relative to a partition, `w_α` (partition is encoded by a quotient map column `col`.. `Finset.image` dedups so 2 active positions in the same α set count once)-/
def colWeight (col : Idx -> Col) (s : Idx -> K) : Nat := ((activePattern s).image col).card

/-- branch no. as a lower bound -/
def isBranchBound (col : Idx -> Col) (psi : (Idx -> K) -> (Idx -> K)) (B: Nat) : Prop :=
  ∀ a ≠ 0, B ≤ colWeight col a + colWeight col (psi a)

/-- only property of S box layer the argument uses (invertible bricklayer map cant move activity between positions because it sends zero diff to zero and nonzero to nonzero)-/
def PreserveSupport (gamma : (Idx -> K) -> (Idx -> K)) : Prop :=
  ∀ a, activePattern (gamma a) = activePattern a

@[simp] theorem mem_activePattern {s : Idx -> K} {i : Idx} :
    i ∈ activePattern s <-> s i ≠ 0 :=

@[simp]
theorem colWeight_id : colWeight id s = weight s
