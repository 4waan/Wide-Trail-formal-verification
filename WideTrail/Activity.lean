import Mathlib.Data.Fintype.Card
set_option autoImplicit false

/-!
# Wide Trail: states active patterns and branch numbers

difference pattern is a state `Idx -> K`. Only the *support*
matters.. the S box layer costs probability at position `i` exactly
when the pattern there is not 0. so 'K' needs no arithmetic beyond distinct `0`
-/

variable {Idx Col K : Type*} [Zero K] [DecidableEq K] [Fintype Idx] [DecidableEq Col]

/-- The set of active positions (pattern is nonzero) -/
def activePattern (s : Idx -> K) : Finset Idx := Finset.univ.filter (fun i => s i ≠ 0)

/-- bundle weight `w_b` (numbr of active S boxes in this pattern) -/
def weight (s : Idx -> K) : Nat := (activePattern s).card

/-- weight relative to a partition, `w_α` (partition is encoded by a quotient map column `col`..
 `Finset.image` dedups so 2 active positions in the same α set count once) -/
def colWeight (col : Idx -> Col) (s : Idx -> K) : Nat := ((activePattern s).image col).card

/-- branch no. as a lower bound -/
def isBranchBound (col : Idx -> Col) (psi : (Idx -> K) -> (Idx -> K)) (B: Nat) : Prop :=
  ∀ a ≠ 0, B ≤ colWeight col a + colWeight col (psi a)

/-- only property of S box layer the argument uses (invertible bricklayer map cant move activity
 between positions because it sends zero diff to zero and nonzero to nonzero)-/
def PreserveSupport (γ : (Idx -> K) -> (Idx -> K)) : Prop :=
  ∀ a, activePattern (γ a) = activePattern a

@[simp] theorem mem_activePattern {s : Idx -> K} {i : Idx} :
    i ∈ activePattern s <-> s i ≠ 0 := by
  simp [activePattern]

@[simp] theorem activePattern_eq_empty {s : Idx -> K} :
    activePattern s = ∅ <-> s = 0 := by  /- ø, U+00F8, Latin small letter o with stroke. Lean's empty set is ∅, U+2205-/
  simp [Finset.eq_empty_iff_forall_notMem, funext_iff]

@[simp] theorem colWeight_id [DecidableEq Idx] {s : Idx -> K} :
    colWeight id s = weight s := by
  simp [colWeight, weight]

theorem weight_eq_of_preservesSupport {γ : (Idx -> K) -> (Idx -> K)}
    (h : PreserveSupport γ) (a : Idx -> K) : weight (γ a) = weight a := by
  simp [weight, h a]

theorem ne_zero_of_preservesSupport {γ : (Idx -> K) -> (Idx -> K)}
    (h : PreserveSupport γ) {a : Idx -> K} (ha : a≠ 0) : γ a ≠0 := by
  sorry

/-- **Theorem 1 (Two-Round Propagation)** in a γλ round the s boc layer and key addition
cant change the active pattern so the active count over two rounds is governed entirely
by λ and is bounded and is bounded by its branch number..-/
theorem two_round [DecidableEq Idx] {γ lam : (Idx -> K) -> (Idx -> K)} {B : Nat}
    (hγ : PreserveSupport γ) (hlam : isBranchBound id lam B)
    {a : Idx -> K} (ha : a ≠ 0) :
    B ≤ weight a + weight (lam (γ a)) := by
  sorry
