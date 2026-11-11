import WideTrail.Hades.Probability
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Inactive propagation through partial rounds

The outer-round bound in `Bounds.lean` charges nothing to the middle rounds. This
file says what the middle rounds do contribute, and when they contribute nothing.

A difference is *inactive* for a mask when it vanishes on every S-box coordinate.
An inactive round acts on the difference as its linear map alone: the masked
coordinates carry a zero difference in and therefore a zero difference out, and
the remaining coordinates are untouched. So a run of inactive rounds is a run of
matrix multiplications, and the differences that survive `r` such rounds form a
linear subspace, `inactiveSpace L mask r`.

Everything is stated for `IsTrail`, which actual executions satisfy
(`differenceTrace_isTrail`), so the results apply both to pairs of real inputs and
to the trails counted by the probability bridge.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

namespace Hades

variable {Idx K : Type*} [Fintype Idx] [DecidableEq Idx] [Field K] [DecidableEq K]

/-- A difference that vanishes on every S-box coordinate of the mask. -/
def Inactive (mask : Finset Idx) (a : Idx → K) : Prop := ∀ i ∈ mask, a i = 0

/-- Zero charged activity is exactly inactivity. -/
theorem sboxWeight_eq_zero_iff (mask : Finset Idx) (a : Idx → K) :
    sboxWeight mask a = 0 ↔ Inactive mask a := by
  unfold sboxWeight activeSboxes Inactive
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h i hi
    by_contra hne
    exact h i (Finset.mem_inter.mpr ⟨hi, mem_activePattern.mpr hne⟩)
  · intro h i hmem
    obtain ⟨hi, ha⟩ := Finset.mem_inter.mp hmem
    exact (mem_activePattern.mp ha) (h i hi)

/-- **An inactive round is linear on the difference.** No assumption is made about
the S-boxes beyond what `IsTrail` already records, and the round constants do not
appear: the next difference is the linear image of the current one. -/
theorem IsTrail.succ_of_inactive {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K}
    {R n : Nat} (hT : IsTrail rounds T R) (hn : n < R)
    (hin : Inactive (rounds n).mask (T n)) : T (n + 1) = (rounds n).lin (T n) := by
  obtain ⟨b, hb, hl, hout⟩ := hT n hn
  have hbT : b = T n := by
    funext i
    by_cases hi : i ∈ (rounds n).mask
    · have hz : T n i = 0 := hin i hi
      have hnot : i ∉ activePattern b := by
        rw [hb]
        exact fun hmem => (mem_activePattern.mp hmem) hz
      have hb0 : b i = 0 := by
        by_contra hne
        exact hnot (mem_activePattern.mpr hne)
      rw [hb0, hz]
    · exact hout i hi
  rw [← hl, hbT]

/-- The differences that stay inactive through `r` consecutive applications of `L`.
For a single S-box coordinate this is the kernel of the Krylov matrix whose rows
are that coordinate's functional composed with `L ^ 0, …, L ^ (r - 1)`. -/
def inactiveSpace (L : Module.End K (Idx → K)) (mask : Finset Idx) (r : Nat) :
    Submodule K (Idx → K) where
  carrier := {a | ∀ j < r, ∀ i ∈ mask, (L ^ j) a i = 0}
  add_mem' := by
    intro a b ha hb j hj i hi
    rw [map_add, Pi.add_apply, ha j hj i hi, hb j hj i hi, add_zero]
  zero_mem' := by
    intro j _ i _
    rw [map_zero, Pi.zero_apply]
  smul_mem' := by
    intro c a ha j hj i hi
    rw [map_smul, Pi.smul_apply, ha j hj i hi, smul_zero]

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
theorem mem_inactiveSpace {L : Module.End K (Idx → K)} {mask : Finset Idx} {r : Nat}
    {a : Idx → K} : a ∈ inactiveSpace L mask r ↔ ∀ j < r, ∀ i ∈ mask, (L ^ j) a i = 0 :=
  Iff.rfl

omit [Fintype Idx] [DecidableEq Idx] [DecidableEq K] in
/-- Longer windows are harder to survive. -/
theorem inactiveSpace_anti (L : Module.End K (Idx → K)) (mask : Finset Idx) {r r' : Nat}
    (h : r ≤ r') : inactiveSpace L mask r' ≤ inactiveSpace L mask r :=
  fun _ ha j hj i hi => ha j (lt_of_lt_of_le hj h) i hi

/-- **A run of inactive rounds is a run of matrix multiplications.** Over a window
whose rounds share one linear map and one mask, inactivity at every step makes the
difference at step `j` equal to `L ^ j` applied to the difference at the start. -/
theorem IsTrail.window_of_inactive {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K}
    {R : Nat} (hT : IsTrail rounds T R) (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (mask : Finset Idx) (start r : Nat) (hend : start + r ≤ R)
    (hlin : ∀ j < r, (rounds (start + j)).lin = L)
    (hmask : ∀ j < r, (rounds (start + j)).mask = mask)
    (hin : ∀ j < r, Inactive mask (T (start + j))) :
    ∀ j ≤ r, T (start + j) = (L.toLinearMap ^ j) (T start) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjr : j < r := by omega
    have hstep := hT.succ_of_inactive (n := start + j) (by omega)
      (by rw [hmask j hjr]; exact hin j hjr)
    rw [show start + (j + 1) = start + j + 1 by omega, hstep, hlin j hjr, ih (by omega),
      Module.End.pow_apply, Module.End.pow_apply, Function.iterate_succ_apply']
    rfl

/-- **If no nonzero difference survives `r` inactive rounds, every window of `r`
such rounds activates an S-box.** The hypothesis is a statement about the linear
map and the mask only; for one S-box coordinate it is a rank condition on a
Krylov matrix. -/
theorem IsTrail.active_in_window {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K}
    {R : Nat} (hT : IsTrail rounds T R) (h0 : T 0 ≠ 0) (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (mask : Finset Idx) (start r : Nat) (hend : start + r ≤ R)
    (hlin : ∀ j < r, (rounds (start + j)).lin = L)
    (hmask : ∀ j < r, (rounds (start + j)).mask = mask)
    (htriv : inactiveSpace L.toLinearMap mask r = ⊥) :
    1 ≤ scheduledWeight rounds T start r := by
  by_contra hcon
  have hzero : scheduledWeight rounds T start r = 0 := by omega
  have hin : ∀ j < r, Inactive mask (T (start + j)) := by
    intro j hj
    have hterm := (Finset.sum_eq_zero_iff.mp hzero) j (Finset.mem_range.mpr hj)
    rw [hmask j hj] at hterm
    exact (sboxWeight_eq_zero_iff mask _).mp hterm
  have hprop := hT.window_of_inactive L mask start r hend hlin hmask hin
  have hmem : T start ∈ inactiveSpace L.toLinearMap mask r := by
    intro j hj i hi
    rw [← hprop j (by omega)]
    exact hin j hj i hi
  rw [htriv, Submodule.mem_bot] at hmem
  exact hT.ne_zero h0 start (by omega) hmem

/-- **The middle rounds are not free.** Tiling `m` rounds with windows of length
`r` gives one active S-box per window. With `r = 0` the statement is `0 ≤ _`. -/
theorem IsTrail.middle_bound {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K}
    {R : Nat} (hT : IsTrail rounds T R) (h0 : T 0 ≠ 0) (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (mask : Finset Idx) (start m r : Nat) (hend : start + m ≤ R)
    (hlin : ∀ j < m, (rounds (start + j)).lin = L)
    (hmask : ∀ j < m, (rounds (start + j)).mask = mask)
    (htriv : inactiveSpace L.toLinearMap mask r = ⊥) :
    m / r ≤ scheduledWeight rounds T start m := by
  have htile : ∀ q, q * r ≤ m → q ≤ scheduledWeight rounds T start (q * r) := by
    intro q
    induction q with
    | zero => intro _; simp
    | succ q ih =>
      intro hq
      have hq' : q * r ≤ m := by nlinarith
      have hwin := hT.active_in_window h0 L mask (start + q * r) r (by nlinarith)
        (fun j hj => by rw [Nat.add_assoc]; exact hlin _ (by nlinarith))
        (fun j hj => by rw [Nat.add_assoc]; exact hmask _ (by nlinarith)) htriv
      rw [show (q + 1) * r = q * r + r by ring, scheduledWeight_add]
      have := ih hq'
      omega
  have hle : m / r * r ≤ m := Nat.div_mul_le_self m r
  have hsplit := scheduledWeight_add rounds T start (m / r * r) (m - m / r * r)
  rw [show m / r * r + (m - m / r * r) = m by omega] at hsplit
  have := htile (m / r) hle
  omega

/-- **Differences in the inactive space cross the window for free.** If the
difference entering a window lies in `inactiveSpace L mask r`, then every one of
the `r` rounds is inactive, no S-box is charged, and the difference leaving the
window is `L ^ r` applied to the one entering it.

This is the converse of `IsTrail.active_in_window` and the attack-side reading of
the same subspace: the conclusion holds for every trail through that difference,
whatever the S-boxes and round constants are. -/
theorem IsTrail.free_window {rounds : Nat → RoundSpec Idx K} {T : Nat → Idx → K}
    {R : Nat} (hT : IsTrail rounds T R) (L : (Idx → K) ≃ₗ[K] (Idx → K))
    (mask : Finset Idx) (start r : Nat) (hend : start + r ≤ R)
    (hlin : ∀ j < r, (rounds (start + j)).lin = L)
    (hmask : ∀ j < r, (rounds (start + j)).mask = mask)
    (hmem : T start ∈ inactiveSpace L.toLinearMap mask r) :
    (∀ j ≤ r, T (start + j) = (L.toLinearMap ^ j) (T start))
      ∧ scheduledWeight rounds T start r = 0 := by
  have hprop : ∀ j ≤ r, T (start + j) = (L.toLinearMap ^ j) (T start) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjr : j < r := by omega
      have hinj : Inactive (rounds (start + j)).mask (T (start + j)) := by
        rw [hmask j hjr, ih (by omega)]
        exact fun i hi => hmem j hjr i hi
      have hstep := hT.succ_of_inactive (n := start + j) (by omega) hinj
      rw [show start + (j + 1) = start + j + 1 by omega, hstep, hlin j hjr, ih (by omega),
        Module.End.pow_apply, Module.End.pow_apply, Function.iterate_succ_apply']
      rfl
  refine ⟨hprop, ?_⟩
  unfold scheduledWeight
  apply Finset.sum_eq_zero
  intro j hj
  have hjr : j < r := Finset.mem_range.mp hj
  rw [hmask j hjr, sboxWeight_eq_zero_iff, hprop j (by omega)]
  exact fun i hi => hmem j hjr i hi

end Hades
