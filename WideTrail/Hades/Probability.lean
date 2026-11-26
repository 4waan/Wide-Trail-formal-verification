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

/-! ### Exact ratios

`keyCount_weight_bound` charges a whole number `d` of bits per charged S-box, where
`u * 2 ^ d ≤ card K`. The results below keep the ratio `card K / u` per charged S-box exact: for
`A` charged S-boxes, `keyCount * card K ^ A ≤ u ^ A * card (Idx → K) ^ R`. The sample space is
the same as above: one trail, an additional independent uniform key per round. -/

namespace Hades

/-- From an exact ratio to a whole power: if `n * q ≤ v * N`, `e * v ≤ q` and `0 < v`, then
`n * e ≤ N`. With `n` a trail count, `q = card K ^ A`, `v = u ^ A` and `e = 2 ^ E`, this turns
`keyCount * card K ^ A ≤ u ^ A * N` into `keyCount * 2 ^ E ≤ N`. -/
theorem mul_le_of_ratio {n q v N e : Nat} (h : n * q ≤ v * N) (he : e * v ≤ q) (hv : 0 < v) :
    n * e ≤ N := by
  refine Nat.le_of_mul_le_mul_right ?_ hv
  calc n * e * v = n * (e * v) := mul_assoc _ _ _
    _ ≤ n * q := Nat.mul_le_mul_left _ he
    _ ≤ v * N := h
    _ = N * v := mul_comm _ _

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K] [Fintype K]

/-- A trail count is at most the number of key sequences, `card (Idx → K) ^ R`: each factor of
`keyCount_eq_prod` counts a set of states. -/
theorem keyCount_le_card_pow (rounds : Nat → RoundSpec Idx K) (R : Nat) (T : Nat → Idx → K)
    (x : Idx → K) : keyCount rounds R T x ≤ Fintype.card (Idx → K) ^ R := by
  rw [keyCount_eq_prod]
  calc _ ≤ ∏ _n ∈ Finset.range R, Fintype.card (Idx → K) :=
        Finset.prod_le_prod' (fun n _ => diffCount_le_card _ _ _)
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

/-- **The exact ratio.** If every S-box that the mask charges in the first `R` rounds has
differential uniformity at most `u`, then with `W = scheduledWeight rounds T 0 R`,
`keyCount * card K ^ W ≤ u ^ W * card (Idx → K) ^ R`. No relation between `u` and `card K` is
assumed. This concerns one trail in the model with an additional independent uniform key per
round. -/
theorem keyCount_weight_bound_exact (rounds : Nat → RoundSpec Idx K) (R : Nat) {u : Nat}
    (hu : ∀ n < R, ∀ i ∈ (rounds n).mask, IsDiffUniform ((rounds n).sbox i) u)
    (T : Nat → Idx → K) (x : Idx → K) :
    keyCount rounds R T x * Fintype.card K ^ scheduledWeight rounds T 0 R
      ≤ u ^ scheduledWeight rounds T 0 R * Fintype.card (Idx → K) ^ R := by
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
  calc keyCount rounds R T x * Fintype.card K ^ scheduledWeight rounds T 0 R
      ≤ (u ^ scheduledWeight rounds T 0 R * Fintype.card K ^
          (R * Fintype.card Idx - scheduledWeight rounds T 0 R))
          * Fintype.card K ^ scheduledWeight rounds T 0 R := Nat.mul_le_mul_right _ hc
    _ = u ^ scheduledWeight rounds T 0 R * Fintype.card K ^ (R * Fintype.card Idx) := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hWle]
    _ = u ^ scheduledWeight rounds T 0 R * Fintype.card (Idx → K) ^ R := by
        rw [Fintype.card_fun, ← pow_mul, mul_comm (Fintype.card Idx) R]

/-- **The exact ratio for a lower bound on the charged S-boxes.** As
`keyCount_weight_bound_exact`, with `scheduledWeight rounds T 0 R` replaced by any `A` at most
that weight: `keyCount * card K ^ A ≤ u ^ A * card (Idx → K) ^ R`. No relation between `u` and
`card K` is assumed: if `u ≤ card K`, the surplus charged S-boxes are dropped from the exact
ratio, and otherwise the bound follows from `keyCount_le_card_pow`. -/
theorem keyCount_weight_bound_exact_of_le (rounds : Nat → RoundSpec Idx K) (R : Nat)
    {u A : Nat} (hu : ∀ n < R, ∀ i ∈ (rounds n).mask, IsDiffUniform ((rounds n).sbox i) u)
    (T : Nat → Idx → K) (x : Idx → K) (hA : A ≤ scheduledWeight rounds T 0 R) :
    keyCount rounds R T x * Fintype.card K ^ A ≤ u ^ A * Fintype.card (Idx → K) ^ R := by
  rcases le_total u (Fintype.card K) with huq | hqu
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hA
    have h := keyCount_weight_bound_exact rounds R hu T x
    rw [hk, pow_add, pow_add] at h
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (Fintype.card_pos (α := K)) k)
    calc keyCount rounds R T x * Fintype.card K ^ A * Fintype.card K ^ k
        = keyCount rounds R T x * (Fintype.card K ^ A * Fintype.card K ^ k) := mul_assoc _ _ _
      _ ≤ u ^ A * u ^ k * Fintype.card (Idx → K) ^ R := h
      _ ≤ u ^ A * Fintype.card K ^ k * Fintype.card (Idx → K) ^ R :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left huq k))
      _ = u ^ A * Fintype.card (Idx → K) ^ R * Fintype.card K ^ k := by ring
  · calc keyCount rounds R T x * Fintype.card K ^ A
        ≤ Fintype.card (Idx → K) ^ R * u ^ A :=
          Nat.mul_le_mul (keyCount_le_card_pow rounds R T x) (Nat.pow_le_pow_left hqu A)
      _ = u ^ A * Fintype.card (Idx → K) ^ R := mul_comm _ _

/-- **`hades_probability` as an exact ratio.** Under the hypotheses of `hades_probability`
without `u * 2 ^ d ≤ card K`, and with `A = (r / 2 + s / 2) * B + r % 2 + s % 2` charged
S-boxes in the outer rounds, `keyCount * card K ^ A ≤ u ^ A * card (Idx → K) ^ (r + m + s)`.
This concerns one trail in the model with an additional independent uniform key per round: it
is not a statement about the fixed round constants alone, and not about a differential. -/
theorem hades_probability_exact (r m s B : Nat) (mask : Finset Idx)
    (boxes : Nat → Idx → K ≃ K) (linear : Nat → (Idx → K) ≃ₗ[K] (Idx → K))
    (values : Nat → Idx → K) {u : Nat}
    (hu : ∀ n < r + m + s, ∀ i, IsDiffUniform (boxes n i) u)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (linear j) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (linear (r + m + j)) B)
    {T : Nat → Idx → K} (h0 : T 0 ≠ 0) (x : Idx → K) :
    keyCount (hadesSchedule r m s mask boxes linear values) (r + m + s) T x
      * Fintype.card K ^ ((r / 2 + s / 2) * B + r % 2 + s % 2)
      ≤ u ^ ((r / 2 + s / 2) * B + r % 2 + s % 2) * Fintype.card (Idx → K) ^ (r + m + s) := by
  let rounds := hadesSchedule r m s mask boxes linear values
  by_cases hz : keyCount rounds (r + m + s) T x = 0
  · change keyCount rounds _ _ _ * _ ≤ _
    simp [hz]
  · exact keyCount_weight_bound_exact_of_le rounds _ (fun n hn i _ => hu n hn i) T x
      ((isTrail_of_keyCount_ne_zero hz).outer_bound r m s B h0
        (fun j hj => hadesMask_prefix r m s mask hj)
        (fun j hj => hadesMask_suffix r m s mask hj) hbp hbs)

end Hades
