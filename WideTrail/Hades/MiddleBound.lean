/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Hades.Krylov

/-!
# Middle bounds: a lower bound on the partial rounds as a hypothesis

`Subspace.lean` charges the partial rounds through windows: when no nonzero difference stays
inactive through `w` consecutive partial rounds, every window of `w` of them charges at least one
S-box, so `m` of them charge at least `m / w` (`IsTrail.middle_bound`). This file separates the
count for the partial rounds from the way it is proved. `MiddleBound A mask m μ` says:

  every trail (`IsTrail`) through `m` consecutive rounds whose linear map is `A` and whose mask
  is `mask`, starting from a nonzero difference, charges at least `μ` S-boxes.

`IsTrail` records only supports, the mask and the linear map, so the property does not depend on
the S-boxes or on the round constants, and a bound proved once for `A` holds for every
round-constant table.

## Results

* `IsTrail.shift`: a trail restricted to the rounds `s, …, s + m - 1` is a trail.
* `MiddleBound.apply`: a middle bound applies to any `m` consecutive rounds of a longer trail
  with that linear map and mask.
* `MiddleBound.zero`, `MiddleBound.mono`, `MiddleBound.add`, `MiddleBound.length_mono`: the
  bound `0` always holds; a smaller `μ` is implied; bounds for `a` and for `b` consecutive rounds
  add to a bound for `a + b`; a bound for `m` rounds holds for every `m' ≥ m`.
* `MiddleBound.of_inactiveSpace`: the window argument as a middle bound. If
  `inactiveSpace A mask w = ⊥`, then `MiddleBound A mask m (m / w)`.
* `scaleRounds`, `IsTrail.scale`, `scheduledWeight_scale`: following every linear map by
  multiplication by a nonzero `c` turns a trail `T` into the trail `n ↦ c ^ n • T n` with the
  same charged weight.
* `MiddleBound.smul`, `MiddleBound.smul_iff`, `MiddleBound.diagPlusOnes`: a nonzero scalar factor
  of `A` changes nothing, so a bound for the Poseidon2 internal matrix `diag d + J` holds for
  `c • (diag d + J)`, e.g. with a Montgomery factor `c`.
* `IsTrail.outer_middle_bound_of`, `outer_middle_bound_of`: the outer-round count of
  `IsTrail.outer_bound` plus a middle bound `μ`, for any trail and for two actual executions.
  With `μ = m / w` and `MiddleBound.of_inactiveSpace` this is `IsTrail.outer_middle_bound`.
* `hades_probability_with_middle_bound_exact`, `hades_probability_with_middle_bound`: the
  independent-key trail bounds of `Probability.lean` and `Subspace.lean` with `μ` in place of
  `m / w`, as an exact ratio and in whole bits per charged S-box.

## What is not claimed

A middle bound is a lower bound on charged S-boxes in the `IsTrail` model; nothing here says it
is attained. No middle bound beyond `m / w` is proved in this file: larger bounds need their own
proofs (certificates for a concrete matrix), which this file only consumes. If `A` is not the
linear map of a linear equivalence, no round has it as its linear map, and for `m ≥ 1` the
property holds for every `μ` for that reason alone; the theorems below that consume a middle
bound apply it to rounds whose linear map is `A`. The probability statements concern one trail
in the model with an additional independent uniform key per round: not the permutation with its
fixed constants, and not a differential.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Hades

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- **A middle bound.** Every trail through `m` consecutive rounds whose linear map is `A` and
whose mask is `mask`, starting from a nonzero difference, charges at least `μ` S-boxes. `IsTrail`
records only supports, the mask and the linear map, so the property is independent of the S-boxes
and of the round constants. -/
def MiddleBound (A : Module.End K (Idx → K)) (mask : Finset Idx) (m μ : ℕ) : Prop :=
  ∀ (rounds : ℕ → RoundSpec Idx K) (T : ℕ → Idx → K), IsTrail rounds T m → T 0 ≠ 0 →
    (∀ j < m, ((rounds j).lin : Module.End K (Idx → K)) = A) →
    (∀ j < m, (rounds j).mask = mask) → μ ≤ scheduledWeight rounds T 0 m

omit [DecidableEq Idx] in
/-- A trail through `R` rounds, restricted to the rounds `s, …, s + m - 1` with `s + m ≤ R`, is a
trail through `m` rounds. -/
theorem IsTrail.shift {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K} {R : ℕ}
    (hT : IsTrail rounds T R) (s m : ℕ) (h : s + m ≤ R) :
    IsTrail (fun n => rounds (s + n)) (fun n => T (s + n)) m := by
  intro n hn
  obtain ⟨b, hb, hl, hout⟩ := hT (s + n) (by omega)
  exact ⟨b, hb, hl, hout⟩

/-- The charged weight of the restricted trail is the charged weight of the window. -/
theorem scheduledWeight_shift (rounds : ℕ → RoundSpec Idx K) (T : ℕ → Idx → K) (s m : ℕ) :
    scheduledWeight (fun n => rounds (s + n)) (fun n => T (s + n)) 0 m =
      scheduledWeight rounds T s m := by
  simp [scheduledWeight]

/-- **A middle bound applies inside a longer trail.** If the rounds `s, …, s + m - 1` of a trail
through `R ≥ s + m` rounds, starting from a nonzero difference, have linear map `A` and mask
`mask`, they charge at least `μ` S-boxes. -/
theorem MiddleBound.apply {A : Module.End K (Idx → K)} {mask : Finset Idx} {m μ : ℕ}
    (h : MiddleBound A mask m μ) {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K} {R : ℕ}
    (hT : IsTrail rounds T R) (h0 : T 0 ≠ 0) (s : ℕ) (hs : s + m ≤ R)
    (hlin : ∀ j < m, ((rounds (s + j)).lin : Module.End K (Idx → K)) = A)
    (hmask : ∀ j < m, (rounds (s + j)).mask = mask) : μ ≤ scheduledWeight rounds T s m := by
  rw [← scheduledWeight_shift]
  exact h _ _ (hT.shift s m hs) (by simpa using hT.ne_zero h0 s (by omega)) hlin hmask

/-- The bound `0` holds for every linear map, mask and number of rounds. -/
theorem MiddleBound.zero (A : Module.End K (Idx → K)) (mask : Finset Idx) (m : ℕ) :
    MiddleBound A mask m 0 :=
  fun _ _ _ _ _ _ => Nat.zero_le _

/-- A middle bound implies every smaller one. -/
theorem MiddleBound.mono {A : Module.End K (Idx → K)} {mask : Finset Idx} {m μ μ' : ℕ}
    (h : MiddleBound A mask m μ) (hle : μ' ≤ μ) : MiddleBound A mask m μ' :=
  fun rounds T hT h0 hlin hmask => le_trans hle (h rounds T hT h0 hlin hmask)

/-- **Middle bounds add.** Bounds `μa` for `a` consecutive rounds and `μb` for `b` consecutive
rounds, with the same linear map and mask, give `μa + μb` for `a + b` consecutive rounds: the two
windows are disjoint. -/
theorem MiddleBound.add {A : Module.End K (Idx → K)} {mask : Finset Idx} {a b μa μb : ℕ}
    (ha : MiddleBound A mask a μa) (hb : MiddleBound A mask b μb) :
    MiddleBound A mask (a + b) (μa + μb) := by
  intro rounds T hT h0 hlin hmask
  have h1 : μa ≤ scheduledWeight rounds T 0 a :=
    ha rounds T (fun n hn => hT n (by omega)) h0 (fun j hj => hlin j (by omega))
      (fun j hj => hmask j (by omega))
  have h2 : μb ≤ scheduledWeight rounds T a b :=
    hb.apply hT h0 a le_rfl (fun j hj => hlin (a + j) (by omega))
      (fun j hj => hmask (a + j) (by omega))
  rw [scheduledWeight_add, Nat.zero_add]
  omega

/-- A middle bound for `m` rounds holds for every longer window: the extra rounds charge at least
`0`. -/
theorem MiddleBound.length_mono {A : Module.End K (Idx → K)} {mask : Finset Idx} {m m' μ : ℕ}
    (h : MiddleBound A mask m μ) (hm : m ≤ m') : MiddleBound A mask m' μ := by
  have h' := h.add (MiddleBound.zero A mask (m' - m))
  rwa [Nat.add_zero, Nat.add_sub_cancel' hm] at h'

/-- **The window argument as a middle bound.** If no nonzero difference stays inactive through
`w` consecutive rounds with `A` and `mask` (`inactiveSpace A mask w = ⊥`), then every trail
through `m` such rounds charges at least `m / w` S-boxes. This is `IsTrail.middle_bound` in the
form of a middle bound. -/
theorem MiddleBound.of_inactiveSpace {A : Module.End K (Idx → K)} {mask : Finset Idx} {w : ℕ}
    (h : inactiveSpace A mask w = ⊥) (m : ℕ) : MiddleBound A mask m (m / w) := by
  intro rounds T hT h0 hlin hmask
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hL : ∀ j < m, (rounds (0 + j)).lin = (rounds 0).lin := fun j hj =>
      LinearEquiv.toLinearMap_injective (by rw [Nat.zero_add, hlin j hj, hlin 0 hm])
    have htriv : inactiveSpace (rounds 0).lin.toLinearMap mask w = ⊥ := by
      rw [show (rounds 0).lin.toLinearMap = A from hlin 0 hm]
      exact h
    exact hT.middle_bound h0 (rounds 0).lin mask 0 m w (by omega) hL
      (fun j hj => by rw [Nat.zero_add]; exact hmask j hj) htriv

/-! ### A nonzero scale is invisible -/

omit [DecidableEq Idx] in
/-- A nonzero scalar multiple has the same support. -/
theorem activePattern_smul {a : K} (ha : a ≠ 0) (v : Idx → K) :
    activePattern (a • v) = activePattern v := by
  ext i
  simp [mem_activePattern, ha]

/-- A nonzero scalar multiple has the same charged weight. -/
theorem sboxWeight_smul (mask : Finset Idx) {a : K} (ha : a ≠ 0) (v : Idx → K) :
    sboxWeight mask (a • v) = sboxWeight mask v := by
  simp only [sboxWeight, activeSboxes, activePattern_smul ha]

/-- The rounds `rounds` with every linear map followed by multiplication by a nonzero `c`. The
masks, S-boxes and constants are unchanged. -/
def scaleRounds (rounds : ℕ → RoundSpec Idx K) {c : K} (hc : c ≠ 0) : ℕ → RoundSpec Idx K :=
  fun n => { rounds n with lin := (rounds n).lin.trans (LinearEquiv.smulOfNeZero K (Idx → K) c hc) }

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- Round `n` of `scaleRounds rounds hc` has `c` times the linear map of round `n` of `rounds`. -/
theorem scaleRounds_lin (rounds : ℕ → RoundSpec Idx K) {c : K} (hc : c ≠ 0) (n : ℕ) :
    ((scaleRounds rounds hc n).lin : Module.End K (Idx → K)) =
      c • ((rounds n).lin : Module.End K (Idx → K)) := by
  ext v i
  simp [scaleRounds]

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
@[simp] theorem scaleRounds_mask (rounds : ℕ → RoundSpec Idx K) {c : K} (hc : c ≠ 0) (n : ℕ) :
    (scaleRounds rounds hc n).mask = (rounds n).mask :=
  rfl

omit [DecidableEq Idx] in
/-- **Scaling a trail.** If `T` is a trail for `rounds`, then `n ↦ c ^ n • T n` is a trail for
the rounds whose linear maps are followed by multiplication by the nonzero `c`. -/
theorem IsTrail.scale {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K} {R : ℕ}
    (hT : IsTrail rounds T R) {c : K} (hc : c ≠ 0) :
    IsTrail (scaleRounds rounds hc) (fun n => c ^ n • T n) R := by
  intro n hn
  obtain ⟨b, hb, hl, hout⟩ := hT n hn
  refine ⟨c ^ n • b, ?_, ?_, ?_⟩
  · rw [activePattern_smul (pow_ne_zero n hc), activePattern_smul (pow_ne_zero n hc), hb]
  · change c • (rounds n).lin (c ^ n • b) = c ^ (n + 1) • T (n + 1)
    rw [map_smul, hl, smul_smul, pow_succ']
  · intro i hi
    simp only [Pi.smul_apply, scaleRounds_mask] at hi ⊢
    rw [hout i hi]

/-- Scaling a trail does not change its charged weight. -/
theorem scheduledWeight_scale (rounds : ℕ → RoundSpec Idx K) (T : ℕ → Idx → K) {c : K}
    (hc : c ≠ 0) (s l : ℕ) :
    scheduledWeight (scaleRounds rounds hc) (fun n => c ^ n • T n) s l =
      scheduledWeight rounds T s l := by
  unfold scheduledWeight
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scaleRounds_mask, sboxWeight_smul _ (pow_ne_zero _ hc)]

/-- **A nonzero scale is invisible.** A middle bound for `A` holds for `c • A` when `c ≠ 0`: a
trail for rounds with linear map `c • A` becomes, after multiplying the difference entering
round `n` by `c⁻¹ ^ n`, a trail for rounds with linear map `A`, with the same supports. -/
theorem MiddleBound.smul {A : Module.End K (Idx → K)} {mask : Finset Idx} {m μ : ℕ} {c : K}
    (hc : c ≠ 0) (h : MiddleBound A mask m μ) : MiddleBound (c • A) mask m μ := by
  intro rounds T hT h0 hlin hmask
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  rw [← scheduledWeight_scale rounds T hc' 0 m]
  refine h _ _ (hT.scale hc') (by simpa using h0) (fun j hj => ?_) (fun j hj => ?_)
  · rw [scaleRounds_lin, hlin j hj, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rw [scaleRounds_mask, hmask j hj]

/-- The same as an equivalence: for `c ≠ 0`, a middle bound holds for `c • A` exactly when it
holds for `A`. -/
theorem MiddleBound.smul_iff {A : Module.End K (Idx → K)} {mask : Finset Idx} {m μ : ℕ} {c : K}
    (hc : c ≠ 0) : MiddleBound (c • A) mask m μ ↔ MiddleBound A mask m μ := by
  refine ⟨fun h => ?_, MiddleBound.smul hc⟩
  have h' := h.smul (inv_ne_zero hc)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'

/-- **The Poseidon2 internal matrix.** A middle bound for `diag d + J` holds for
`c • (diag d + J)` (`Poseidon2.diagPlusOnes c d`) whenever `c ≠ 0`, for instance for a
Montgomery factor `c = R⁻¹`. -/
theorem MiddleBound.diagPlusOnes {mask : Finset Idx} {m μ : ℕ} {c : K}
    (hc : c ≠ 0) {d : Idx → K} (h : MiddleBound (Poseidon2.diagPlusOnes 1 d) mask m μ) :
    MiddleBound (Poseidon2.diagPlusOnes c d) mask m μ := by
  rw [Poseidon2.diagPlusOnes_eq_smul]
  exact h.smul hc

/-! ### Outer and middle rounds together -/

/-- **Outer rounds and a middle bound.** The two full blocks are counted as in
`IsTrail.outer_bound`; the `m` middle rounds, sharing the linear map `A` and the mask `mask`,
add `μ` when `MiddleBound A mask m μ` holds. The three windows are disjoint, so the
contributions add. With `μ = m / w` from `MiddleBound.of_inactiveSpace` this is
`IsTrail.outer_middle_bound`. -/
theorem IsTrail.outer_middle_bound_of {rounds : ℕ → RoundSpec Idx K} {T : ℕ → Idx → K}
    (r m s B μ : ℕ) (hT : IsTrail rounds T (r + m + s)) (h0 : T 0 ≠ 0)
    (hp : ∀ j < r, (rounds j).mask = Finset.univ)
    (hs : ∀ j < s, (rounds (r + m + j)).mask = Finset.univ)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (rounds j).lin B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (rounds (r + m + j)).lin B)
    (A : Module.End K (Idx → K)) (mask : Finset Idx)
    (hlin : ∀ j < m, ((rounds (r + j)).lin : Module.End K (Idx → K)) = A)
    (hmask : ∀ j < m, (rounds (r + j)).mask = mask) (hmid : MiddleBound A mask m μ) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 + μ ≤ scheduledWeight rounds T 0 (r + m + s) := by
  have hp' := hT.window_bound h0 0 r B (by omega) (by simpa using hp) (by simpa using hbp)
  have hs' := hT.window_bound h0 (r + m) s B (by omega) hs hbs
  have hm' := hmid.apply hT h0 r (by omega) hlin hmask
  have hsplit := scheduledWeight_add rounds T 0 (r + m) s
  have hsplit' := scheduledWeight_add rounds T 0 r m
  simp only [zero_add] at hsplit hsplit'
  rw [Nat.add_mul]
  omega

/-- **The same bound for two actual executions on distinct inputs.** -/
theorem outer_middle_bound_of (rounds : ℕ → RoundSpec Idx K) {x y : Idx → K} (hxy : x ≠ y)
    (r m s B μ : ℕ)
    (hp : ∀ j < r, (rounds j).mask = Finset.univ)
    (hs : ∀ j < s, (rounds (r + m + j)).mask = Finset.univ)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (rounds j).lin B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (rounds (r + m + j)).lin B)
    (A : Module.End K (Idx → K)) (mask : Finset Idx)
    (hlin : ∀ j < m, ((rounds (r + j)).lin : Module.End K (Idx → K)) = A)
    (hmask : ∀ j < m, (rounds (r + j)).mask = mask) (hmid : MiddleBound A mask m μ) :
    (r / 2 + s / 2) * B + r % 2 + s % 2 + μ ≤
      scheduledWeight rounds (differenceTrace rounds x y) 0 (r + m + s) :=
  (differenceTrace_isTrail rounds x y (r + m + s)).outer_middle_bound_of r m s B μ
    (differenceTrace_ne_zero rounds hxy 0) hp hs hbp hbs A mask hlin hmask hmid

/-! ### The independent-key trail bounds with a middle bound -/

variable [Fintype K]

/-- **The trail count with a middle bound, as an exact ratio.** Under the hypotheses of
`hades_probability_with_middle_exact`, with the inactive-space hypothesis replaced by
`MiddleBound A mask m μ` for the common linear map `A` of the middle rounds, and with
`N = (r / 2 + s / 2) * B + r % 2 + s % 2 + μ` charged S-boxes,
`keyCount * card K ^ N ≤ u ^ N * card (Idx → K) ^ (r + m + s)`. No relation between `u` and
`card K` is assumed.

This concerns one trail in the model with an additional independent uniform key per round:
not the permutation with its fixed constants, and not a differential. -/
theorem hades_probability_with_middle_bound_exact (r m s B μ : ℕ) (mask : Finset Idx)
    (boxes : ℕ → Idx → K ≃ K) (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K)) (values : ℕ → Idx → K)
    {u : ℕ} (hu : ∀ n < r + m + s, ∀ i, IsDiffUniform (boxes n i) u)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (linear j) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (linear (r + m + j)) B)
    (A : Module.End K (Idx → K)) (hmid : ∀ j < m, (linear (r + j) : Module.End K (Idx → K)) = A)
    (hμ : MiddleBound A mask m μ) {T : ℕ → Idx → K} (h0 : T 0 ≠ 0) (x : Idx → K) :
    keyCount (hadesSchedule r m s mask boxes linear values) (r + m + s) T x
      * Fintype.card K ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + μ)
      ≤ u ^ ((r / 2 + s / 2) * B + r % 2 + s % 2 + μ) * Fintype.card (Idx → K) ^ (r + m + s) := by
  let rounds := hadesSchedule r m s mask boxes linear values
  by_cases hz : keyCount rounds (r + m + s) T x = 0
  · change keyCount rounds _ _ _ * _ ≤ _
    simp [hz]
  · exact keyCount_weight_bound_exact_of_le rounds _ (fun n hn i _ => hu n hn i) T x
      ((isTrail_of_keyCount_ne_zero hz).outer_middle_bound_of r m s B μ h0
        (fun j hj => hadesMask_prefix r m s mask hj)
        (fun j hj => hadesMask_suffix r m s mask hj) hbp hbs A mask
        (fun j hj => hmid j hj)
        (fun j hj => hadesMask_middle r m s mask hj) hμ)

/-- **The trail count with a middle bound, in whole bits.** As
`hades_probability_with_middle_bound_exact`, charging `d` bits per charged S-box when
`u * 2 ^ d ≤ card K`: `keyCount * 2 ^ (d * N) ≤ card (Idx → K) ^ (r + m + s)` with
`N = (r / 2 + s / 2) * B + r % 2 + s % 2 + μ`.

The sample space is the same: one trail, an additional independent uniform key per round.
Nothing is claimed about the fixed public constants alone, nor about a differential. -/
theorem hades_probability_with_middle_bound (r m s B μ : ℕ) (mask : Finset Idx)
    (boxes : ℕ → Idx → K ≃ K) (linear : ℕ → (Idx → K) ≃ₗ[K] (Idx → K)) (values : ℕ → Idx → K)
    {u d : ℕ} (hu : ∀ n < r + m + s, ∀ i, IsDiffUniform (boxes n i) u)
    (hd : u * 2 ^ d ≤ Fintype.card K)
    (hbp : ∀ j, j + 1 < r → isBranchBound id (linear j) B)
    (hbs : ∀ j, j + 1 < s → isBranchBound id (linear (r + m + j)) B)
    (A : Module.End K (Idx → K)) (hmid : ∀ j < m, (linear (r + j) : Module.End K (Idx → K)) = A)
    (hμ : MiddleBound A mask m μ) {T : ℕ → Idx → K} (h0 : T 0 ≠ 0) (x : Idx → K) :
    keyCount (hadesSchedule r m s mask boxes linear values) (r + m + s) T x
      * 2 ^ (d * ((r / 2 + s / 2) * B + r % 2 + s % 2 + μ))
      ≤ Fintype.card (Idx → K) ^ (r + m + s) := by
  let rounds := hadesSchedule r m s mask boxes linear values
  by_cases hz : keyCount rounds (r + m + s) T x = 0
  · change keyCount rounds _ _ _ * _ ≤ _
    simp [hz]
  · have hactivity := (isTrail_of_keyCount_ne_zero hz).outer_middle_bound_of r m s B μ h0
      (fun j hj => hadesMask_prefix r m s mask hj)
      (fun j hj => hadesMask_suffix r m s mask hj) hbp hbs A mask
      (fun j hj => hmid j hj)
      (fun j hj => hadesMask_middle r m s mask hj) hμ
    exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left d hactivity)))
      (keyCount_weight_bound rounds _ (fun n hn i _ => hu n hn i) hd T x)

end Hades
