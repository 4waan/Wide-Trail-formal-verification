import WideTrail.Hades.Masked
import WideTrail.Differential.TrailProb

/-! Exact masked differential counts. Identity coordinates are never charged. -/

set_option autoImplicit false

namespace Hades

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx]
  [AddCommGroup K] [Fintype K] [DecidableEq K]

theorem diffCount_identity (a b : K) :
    diffCount (id : K → K) a b = if a = b then Fintype.card K else 0 := by
  by_cases h : a = b <;> simp [diffCount, diffSet, h]

/-- Exact coordinate factorization, including the identity constraints. -/
theorem diffCount_masked (mask : Finset Idx) (s : Idx → K → K) (a b : Idx → K) :
    diffCount (maskedBricklayer mask s) a b =
      ∏ i, if i ∈ mask then diffCount (s i) (a i) (b i)
        else if a i = b i then Fintype.card K else 0 := by
  rw [maskedBricklayer, diffCount_bricklayer]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ mask <;> simp [hi, diffCount_identity]

/-- Only active coordinates inside the mask cost a uniformity factor. -/
theorem diffCount_masked_le (mask : Finset Idx) {s : Idx → K → K} {u : Nat}
    (hu : ∀ i ∈ mask, IsDiffUniform (s i) u) (a b : Idx → K) :
    diffCount (maskedBricklayer mask s) a b ≤
      u ^ sboxWeight mask a * Fintype.card K ^ (Fintype.card Idx - sboxWeight mask a) := by
  rw [maskedBricklayer, diffCount_bricklayer,
    ← Finset.prod_mul_prod_compl (activeSboxes mask a)]
  apply Nat.mul_le_mul
  · calc ∏ i ∈ activeSboxes mask a, diffCount (if i ∈ mask then s i else id) (a i) (b i)
        ≤ ∏ _i ∈ activeSboxes mask a, u := by
          apply Finset.prod_le_prod'
          intro i hi
          obtain ⟨hm, ha⟩ := Finset.mem_inter.mp hi
          simpa [hm] using hu i hm (a i) (mem_activePattern.mp ha) (b i)
      _ = u ^ sboxWeight mask a := by rw [Finset.prod_const, sboxWeight]
  · calc ∏ i ∈ (activeSboxes mask a)ᶜ,
          diffCount (if i ∈ mask then s i else id) (a i) (b i)
        ≤ ∏ _i ∈ (activeSboxes mask a)ᶜ, Fintype.card K :=
          Finset.prod_le_prod' (fun i _ => diffCount_le_card _ _ _)
      _ = Fintype.card K ^ (Fintype.card Idx - sboxWeight mask a) := by
          rw [Finset.prod_const, Finset.card_compl, sboxWeight, Fintype.card]

/-- A nonzero count enforces exact difference equality outside the mask. -/
theorem outside_eq_of_diffCount_ne_zero (mask : Finset Idx) (s : Idx → K → K)
    {a b : Idx → K} (h : diffCount (maskedBricklayer mask s) a b ≠ 0)
    {i : Idx} (hi : i ∉ mask) : b i = a i := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  have hcoord := congrFun (mem_diffSet.mp hx) i
  simpa [maskedBricklayer_apply, hi] using hcoord.symm

end Hades
