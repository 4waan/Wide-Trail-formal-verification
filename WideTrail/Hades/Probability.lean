import WideTrail.Hades.Bounds
import WideTrail.Hades.Counting
import WideTrail.Differential.Scheduled

/-! Masked activity bounds connected to actual independent-key trail counts.
Fixed round additions are parameters. Averaging is over an additional independent
uniform state-sized key per round, not over the inputs of the fixed permutation. -/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Hades

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- A realizable difference step preserves support, respects identity coordinates,
and propagates through the actual round's linear map. -/
def IsTrail (rounds : Nat → RoundSpec Idx K) (T : Nat → Idx → K) (R : Nat) : Prop :=
  ∀ n < R, ∃ b, activePattern b = activePattern (T n) ∧ (rounds n).lin b = T (n + 1)
    ∧ ∀ i ∉ (rounds n).mask, b i = T n i

/-- Actual executions satisfy the same relation used by the counting bridge. -/
theorem differenceTrace_isTrail (rounds : Nat → RoundSpec Idx K) (x y : Idx → K) (R : Nat) :
    IsTrail rounds (differenceTrace rounds x y) R := by
  intro n _
  exact ⟨nonlinearDifference rounds x y n, nonlinearDifference_support rounds x y n,
    (differenceTrace_succ rounds x y n).symm,
    fun i hi => nonlinearDifference_outside rounds x y n hi⟩

omit [DecidableEq Idx] in
theorem IsTrail.ne_zero {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K} {R : Nat}
    (hT : IsTrail rounds T R) (h0 : T 0 ≠ 0) : ∀ n ≤ R, T n ≠ 0 := by
  intro n hn
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨b, hb, hl, _⟩ := hT n (by omega)
    have hb0 := ne_zero_congr hb (ih (by omega))
    intro hz
    have : (rounds n).lin b = (rounds n).lin 0 := by simpa [hz] using hl
    exact hb0 ((rounds n).lin.injective this)

theorem IsTrail.window_bound {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K} {R : Nat}
    (hT : IsTrail rounds T R) (h0 : T 0 ≠ 0) (start length B : Nat) (hend : start + length ≤ R)
    (hfull : ∀ j < length, (rounds (start + j)).mask = Finset.univ)
    (hbranch : ∀ j, j + 1 < length → isBranchBound id (rounds (start + j)).lin B) :
    length / 2 * B + length % 2 ≤ scheduledWeight rounds T start length := by
  apply pair_sum_bound
  · intro j hj
    simpa [hfull j hj] using one_le_weight (hT.ne_zero h0 (start + j) (by omega))
  · intro j hj
    obtain ⟨b, hb, hl, _⟩ := hT (start + j) (by omega)
    have h := hbranch j hj b (ne_zero_congr hb (hT.ne_zero h0 (start + j) (by omega)))
    rw [colWeight_id, colWeight_id, weight_congr hb, hl] at h
    simpa [hfull j (by omega), hfull (j + 1) hj, Nat.add_assoc] using h

theorem IsTrail.outer_bound {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K}
    (r m s B : Nat) (hT : IsTrail rounds T (r + m + s)) (h0 : T 0 ≠ 0)
    (hp : ∀ j < r, (rounds j).mask = Finset.univ)
    (hs : ∀ j < s, (rounds (r + m + j)).mask = Finset.univ)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (rounds j).lin B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (rounds (r + m + j)).lin B) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 ≤ scheduledWeight rounds T 0 (r + m + s) := by
  have hp' := hT.window_bound h0 0 r B (by omega) (by simpa using hp) (by simpa using hbp)
  have hs' := hT.window_bound h0 (r + m) s B (by omega) hs hbs
  have hsplit := scheduledWeight_add rounds T 0 (r + m) s
  have hsplit' := scheduledWeight_add rounds T 0 r m
  simp only [zero_add] at hsplit hsplit'
  rw [Nat.add_mul]
  omega

variable [Fintype K]

def roundGamma (R : RoundSpec Idx K) (x : Idx → K) : Idx → K :=
  maskedBricklayer R.mask (fun i => R.sbox i) (x + R.constant)

def keyCount (rounds : Nat → RoundSpec Idx K) (R : Nat)
    (T : Nat → Idx → K) (x : Idx → K) : Nat :=
  Scheduled.trailKeyCount (fun n => (rounds n).lin.toAddEquiv)
    (fun n => roundGamma (rounds n)) R T x

theorem keyCount_eq_prod (rounds : Nat → RoundSpec Idx K) (R : Nat)
    (T : Nat → Idx → K)
    (x : Idx → K) : keyCount rounds R T x =
      ∏ n ∈ Finset.range R,
        diffCount (maskedBricklayer (rounds n).mask (fun i => (rounds n).sbox i))
        (T n) ((rounds n).lin.symm (T (n + 1))) := by
  rw [keyCount, Scheduled.trailKeyCount_eq_prod]
  apply Finset.prod_congr rfl
  intro n _
  exact diffCount_addKey _ _ _ _

theorem isTrail_of_keyCount_ne_zero {rounds : Nat → RoundSpec Idx K} {R : Nat}
    {T : Nat → Idx → K} {x : Idx → K} (h : keyCount rounds R T x ≠ 0) : IsTrail rounds T R := by
  rw [keyCount_eq_prod] at h
  intro n hn
  have hc : diffCount (maskedBricklayer (rounds n).mask (fun i => (rounds n).sbox i))
      (T n) ((rounds n).lin.symm (T (n + 1))) ≠ 0 :=
    fun hz => h (Finset.prod_eq_zero (Finset.mem_range.mpr hn) hz)
  refine ⟨(rounds n).lin.symm (T (n + 1)), ?_, (rounds n).lin.apply_symm_apply _, ?_⟩
  · apply activePattern_eq_of_diffCount_ne_zero (s := fun i =>
        if i ∈ (rounds n).mask then (rounds n).sbox i else id) _ hc
    intro i
    by_cases hi : i ∈ (rounds n).mask
    · simpa [hi] using (rounds n).sbox i |>.injective
    · simpa only [if_neg hi] using (Function.injective_id : Function.Injective (id : K → K))
  · exact fun i hi => outside_eq_of_diffCount_ne_zero _ _ hc hi

/-- Every charged S-box costs `2^d` in the independent-key sample space. -/
theorem keyCount_weight_bound (rounds : Nat → RoundSpec Idx K) (R : Nat)
    {u d : Nat} (hu : ∀ n < R, ∀ i ∈ (rounds n).mask, IsDiffUniform ((rounds n).sbox i) u)
    (hd : u * 2 ^ d ≤ Fintype.card K) (T : Nat → Idx → K) (x : Idx → K) :
    keyCount rounds R T x * 2 ^ (d * scheduledWeight rounds T 0 R)
      ≤ Fintype.card (Idx → K) ^ R := by
  let w := fun n => sboxWeight (rounds n).mask (T n)
  have hw : ∀ n, w n ≤ Fintype.card Idx := fun n =>
    (sboxWeight_le_weight _ _).trans (Finset.card_le_univ _)
  have hW : scheduledWeight rounds T 0 R = ∑ n ∈ Finset.range R, w n := by
    simp [scheduledWeight, w]
  have hWle : scheduledWeight rounds T 0 R ≤ R * Fintype.card Idx := by
    rw [hW]
    calc _ ≤ ∑ _n ∈ Finset.range R, Fintype.card Idx := Finset.sum_le_sum (fun n _ => hw n)
      _ = _ := by simp
  have hc : keyCount rounds R T x ≤ u ^ scheduledWeight rounds T 0 R
      * Fintype.card K ^ (R * Fintype.card Idx - scheduledWeight rounds T 0 R) := by
    rw [keyCount_eq_prod]
    calc _ ≤ ∏ n ∈ Finset.range R, (u ^ w n * Fintype.card K ^ (Fintype.card Idx - w n)) := by
          apply Finset.prod_le_prod'
          intro n hn
          exact diffCount_masked_le _ (hu n (Finset.mem_range.mp hn)) _ _
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
            sum_sub_of_le w hw R, ← hW]
  calc keyCount rounds R T x * 2 ^ (d * scheduledWeight rounds T 0 R)
      ≤ (u ^ scheduledWeight rounds T 0 R * Fintype.card K ^
          (R * Fintype.card Idx - scheduledWeight rounds T 0 R))
          * 2 ^ (d * scheduledWeight rounds T 0 R) := Nat.mul_le_mul_right _ hc
    _ = (u * 2 ^ d) ^ scheduledWeight rounds T 0 R * Fintype.card K ^
        (R * Fintype.card Idx - scheduledWeight rounds T 0 R) := by rw [mul_pow, pow_mul]; ring
    _ ≤ Fintype.card K ^ scheduledWeight rounds T 0 R * Fintype.card K ^
        (R * Fintype.card Idx - scheduledWeight rounds T 0 R) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd _)
    _ = Fintype.card K ^ (R * Fintype.card Idx) := by rw [← pow_add]; congr 1; omega
    _ = Fintype.card (Idx → K) ^ R := by rw [Fintype.card_fun, ← pow_mul]; congr 1; ring

/-- The missing connection: HADES outer-round activity bounds an actual trail count. -/
theorem hades_probability (r m s B : Nat) (mask : Finset Idx)
    (boxes : Nat → Idx → K ≃ K) (linear : Nat → (Idx → K) ≃ₗ[K] (Idx → K))
    (values : Nat → Idx → K) {u d : Nat}
    (hu : ∀ n < r + m + s, ∀ i, IsDiffUniform (boxes n i) u)
    (hd : u * 2 ^ d ≤ Fintype.card K)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (linear j) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (linear (r + m + j)) B)
    {T : Nat → Idx → K} (h0 : T 0 ≠ 0) (x : Idx → K) :
    keyCount (hadesSchedule r m s mask boxes linear values) (r + m + s) T x
      * 2 ^ (d * ((r / 2 + s / 2) * B + r % 2 + s % 2))
      ≤ Fintype.card (Idx → K) ^ (r + m + s) := by
  let rounds := hadesSchedule r m s mask boxes linear values
  by_cases hz : keyCount rounds (r + m + s) T x = 0
  · change keyCount rounds _ _ _ * _ ≤ _
    simp [hz]
  · have hactivity := (isTrail_of_keyCount_ne_zero hz).outer_bound r m s B h0
      (fun j hj => hadesMask_prefix r m s mask hj)
      (fun j hj => hadesMask_suffix r m s mask hj) hbp hbs
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left d hactivity)))
      (keyCount_weight_bound rounds _ (fun n hn i _ => hu n hn i) hd T x)

end Hades
