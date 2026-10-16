import WideTrail.Differential.Counts
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Differential bounds from polynomial root counts, without enumerating a field. -/

set_option autoImplicit false

namespace Sbox

open Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] in
theorem card_roots_le (p : K[X]) : p.roots.toFinset.card ≤ p.natDegree :=
  (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p)

/-- A nonzero polynomial containing every differential solution bounds the count. -/
theorem diffCount_le_polynomial {f : K → K} {a b : K} (p : K[X]) (hp : p ≠ 0)
    (hroot : ∀ x, f (x + a) - f x = b → p.eval x = 0) :
    diffCount f a b ≤ p.natDegree := by
  apply le_trans (Finset.card_le_card (t := p.roots.toFinset) ?_) (card_roots_le p)
  intro x hx
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hroot x (mem_diffSet.mp hx)))

/-- Inversion has differential uniformity at most four over every finite field.
The two exceptional inputs are zero and minus the input difference; all other
solutions are roots of a nonzero quadratic. -/
theorem inv_uniform : IsDiffUniform (fun x : K => x⁻¹) 4 := by
  intro a ha b
  let p : K[X] := C b * X ^ 2 + C (a * b) * X + C a
  have hp : p ≠ 0 := by
    intro h
    have h0 := congrArg (fun q : K[X] => q.coeff 0) h
    exact ha (by simpa [p] using h0)
  have hdeg : p.natDegree ≤ 2 := by dsimp [p]; compute_degree!
  have hsub : diffSet (fun x : K => x⁻¹) a b ⊆ p.roots.toFinset ∪ {0, -a} := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hxa : x = -a
    · simp [hxa]
    apply Finset.mem_union_left
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    have hne : x + a ≠ 0 := by intro h; exact hxa (eq_neg_iff_add_eq_zero.mpr h)
    have h := mem_diffSet.mp hx
    have he : x * (x + a) * b + a = 0 := by
      rw [← h]
      field_simp [hx0, hne]
      ring
    change p.eval x = 0
    simp only [p, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination he
  have hcard : ({0, -a} : Finset K).card ≤ 2 := by
    calc _ ≤ ({-a} : Finset K).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  calc diffCount (fun x : K => x⁻¹) a b
      ≤ (p.roots.toFinset ∪ {0, -a}).card := Finset.card_le_card hsub
    _ ≤ p.roots.toFinset.card + ({0, -a} : Finset K).card := Finset.card_union_le _ _
    _ ≤ 2 + 2 := Nat.add_le_add ((card_roots_le p).trans hdeg) hcard
    _ = 4 := rfl

/-- The fifth-power S-box has differential uniformity at most four when five
is nonzero in the field. Its difference polynomial is quartic. -/
theorem pow_five_uniform (hfive : (5 : K) ≠ 0) : IsDiffUniform (fun x : K => x ^ 5) 4 := by
  intro a ha b
  let p : K[X] := C (5 * a) * X ^ 4 + C (10 * a ^ 2) * X ^ 3
    + C (10 * a ^ 3) * X ^ 2 + C (5 * a ^ 4) * X + C (a ^ 5 - b)
  have hp : p ≠ 0 := by
    intro h
    have hc := congrArg (fun q : K[X] => q.coeff 4) h
    have hcoeff : p.coeff 4 = 5 * a := by dsimp [p]; compute_degree!
    rw [hcoeff, coeff_zero] at hc
    exact (mul_ne_zero hfive ha) hc
  have hdeg : p.natDegree ≤ 4 := by dsimp [p]; compute_degree!
  apply le_trans (diffCount_le_polynomial p hp ?_) hdeg
  intro x hx
  simp only [p, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  calc 5 * a * x ^ 4 + 10 * a ^ 2 * x ^ 3 + 10 * a ^ 3 * x ^ 2
        + 5 * a ^ 4 * x + (a ^ 5 - b) = (x + a) ^ 5 - x ^ 5 - b := by ring
    _ = 0 := sub_eq_zero.mpr hx

end Sbox
