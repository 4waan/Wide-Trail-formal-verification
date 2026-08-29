/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.Activity
import WideTrail.Layer3.Differential
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The S-box layer, counted

This is the join between Layer 1's combinatorics and Layer 3's probabilities, and it is
one theorem: for a bricklayer map, the differential count **factors over bundles**,

`diffCount (bricklayer s) a b = ∏ i, diffCount (s i) (a i) (b i)`,

and each factor is bounded by the differential uniformity `u` where `a i ≠ 0` and by
`|K|` where `a i = 0`. The number of factors of the first kind is `weight a`, Layer 1's
bundle weight, so

`diffCount (bricklayer s) a b ≤ u ^ weight a * |K| ^ (|Idx| - weight a)`.

Layer 1's counting quantity appears in a probability bound without any translation step:
`weight` was defined as the size of the support, and the support is exactly the set of
factors that are not `1`.

The second theorem here discharges a hypothesis instead of using one.
`WideTrailSpec.sbox_preserves` asks that the S-box layer move no activity. For a real
cipher that is not a statement about a function of the difference, since the S-box layer
does not determine its output difference; it is a statement about which output differences
are *possible*. `activePattern_eq_of_diffCount_ne_zero` proves it in that form, from
injectivity of the S-boxes and nothing else, and it is what `Markov.lean` feeds into
`WideTrailSpec.IsTrail`.
-/

set_option autoImplicit false

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx]
  [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- A bricklayer map: the S-box `s i` applied independently in bundle `i`. -/
def bricklayer (s : Idx → K → K) : (Idx → K) → (Idx → K) := fun x i => s i (x i)

/-- The inputs realising a bricklayer differential are exactly the tuples realising each
bundle's differential independently. -/
theorem diffSet_bricklayer (s : Idx → K → K) (a b : Idx → K) :
    diffSet (bricklayer s) a b = Fintype.piFinset (fun i => diffSet (s i) (a i) (b i)) := by
  ext x
  simp [diffSet, bricklayer, Fintype.mem_piFinset, funext_iff]

/-- **A bricklayer's differential count factors over bundles.** -/
theorem diffCount_bricklayer (s : Idx → K → K) (a b : Idx → K) :
    diffCount (bricklayer s) a b = ∏ i, diffCount (s i) (a i) (b i) := by
  rw [diffCount, diffSet_bricklayer, Fintype.card_piFinset]
  rfl

/-- **`PreserveSupport`, proved rather than assumed.** If every S-box is injective then
every output difference an S-box layer can actually produce has the same support as the
input difference: a zero bundle difference stays zero, and a nonzero one cannot be
flattened. This is the only property of `γ` that any wide-trail theorem uses, and here it
is a consequence of invertibility rather than a hypothesis about a fictitious function on
differences. -/
theorem activePattern_eq_of_diffCount_ne_zero {s : Idx → K → K}
    (hs : ∀ i, Function.Injective (s i)) {a b : Idx → K}
    (h : diffCount (bricklayer s) a b ≠ 0) : activePattern b = activePattern a := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [mem_diffSet] at hx
  have hcoord : ∀ i, s i (x i + a i) - s i (x i) = b i := by
    intro i
    simpa [bricklayer] using congrFun hx i
  ext i
  simp only [mem_activePattern]
  constructor
  · intro hb hai
    exact hb (by have := hcoord i; rw [hai, add_zero, sub_self] at this; exact this.symm)
  · intro ha hb
    have hz := hcoord i
    rw [hb, sub_eq_zero] at hz
    exact ha (by simpa using hs i hz)

/-- **The active-S-box count is the exponent.** Every active bundle costs a factor of at
most `u`; every inactive bundle is free, costing the whole of `|K|`. -/
theorem diffCount_bricklayer_le {s : Idx → K → K} {u : Nat}
    (hu : ∀ i, IsDiffUniform (s i) u) (a b : Idx → K) :
    diffCount (bricklayer s) a b
      ≤ u ^ weight a * Fintype.card K ^ (Fintype.card Idx - weight a) := by
  rw [diffCount_bricklayer, ← Finset.prod_mul_prod_compl (activePattern a)]
  refine Nat.mul_le_mul ?_ ?_
  · calc ∏ i ∈ activePattern a, diffCount (s i) (a i) (b i)
        ≤ ∏ _i ∈ activePattern a, u :=
          Finset.prod_le_prod' (fun i hi => hu i (a i) (mem_activePattern.mp hi) (b i))
      _ = u ^ weight a := by rw [Finset.prod_const, weight]
  · calc ∏ i ∈ (activePattern a)ᶜ, diffCount (s i) (a i) (b i)
        ≤ ∏ _i ∈ (activePattern a)ᶜ, Fintype.card K :=
          Finset.prod_le_prod' (fun i _ => diffCount_le_card _ _ _)
      _ = Fintype.card K ^ (Fintype.card Idx - weight a) := by
          rw [Finset.prod_const, Finset.card_compl, weight, Fintype.card]
