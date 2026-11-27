/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Hull
import WideTrail.Linear.Checks.Character

/-!
# Linear trails and hulls on a one-bundle toy

The theorems of `Trail.lean` and `Hull.lean`, instantiated on the smallest interesting cipher and
compared with the kernel's direct evaluation of their definitions. The state is three bits,
`Bits3 = Fin 3 → ZMod 2`, with the bit pairing `B3`; each round is `x ↦ chi3 (x + k)`, the χ map
of `Checks/Character.lean` after a round key, with the identity as linear layer. Two rounds, the
masks `m3 = (1, 1, 0)` and `m5 = (1, 0, 1)`.

* **The fixed-key expansion.** `one_expansion` is `walsh_run_eq_sum_trails` at `r = 1` on this
  toy: `8 · walsh (run k) m3 m5` is the signed sum over the eight trails `m3 → c → m5`.
  `one_expansion_direct` is the same proposition evaluated by the kernel for all `64` key
  vectors.
* **Nyberg's identity, a typed bridge.** `one_elpCount_direct`: the kernel sums the squared Walsh
  values over all `64` key pairs and gets `512`. `one_trail_sum`: the squared correlations of
  the eight trails sum to `512`. `one_nyberg` is `elpCount_succ_eq_sum_trails` at `r = 1`, and
  `one_elpCount_via_nyberg` derives the count `512` from it and `one_trail_sum`, in agreement
  with the direct count.
* **Separation is needed.** Under the zero pairing, which is not separating
  (`zeroPairing_not_separating`) but for which the identity is still an adjoint of the linear
  layer, the identity of `elpCount_succ_eq_sum_trails` at `r = 1` fails at the masks `(0, 0)`
  (`one_nyberg_fails_zeroPairing`).

The values were computed outside Lean first; the kernel rechecks every value used.

## What is not claimed

These checks concern this toy only. The direct evaluations are numerical cross-checks of the
identities on one instance; they prove nothing beyond the stated instances.
-/

set_option autoImplicit false

namespace Linear.Checks

/-! ### Shared facts -/

/-- Three bits make eight states. -/
theorem card_Bits3 : Fintype.card Bits3 = 8 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rfl

/-- The bit pairing of three bits is separating (`bitPairing_separating`), stated for `B3`. -/
theorem B3_separating : B3.Separating sign₂ := bitPairing_separating (Fin 3)

/-- The masks of the one-bundle toy: `m3 = (1, 1, 0)` and `m5 = (1, 0, 1)`, bit `i` first. -/
def m3 : Bits3 := ![1, 1, 0]

/-- See `m3`. -/
def m5 : Bits3 := ![1, 0, 1]

/-! ### One bundle: the fixed-key expansion and Nyberg's identity against the definition -/

/-- The identity of `Bits3`, as an additive bijection: the linear layer of the one-bundle toy. -/
abbrev idBits : Bits3 ≃+ Bits3 := AddEquiv.refl Bits3

/-- The identity is an adjoint of the identity, for the bit pairing. -/
theorem idBits_isAdjoint : ∀ n : ℕ,
    IsAdjoint B3 B3 ((fun _ => idBits) n) ((fun _ => (id : Bits3 → Bits3)) n) :=
  fun _ _ _ => rfl

/-- The fixed-key expansion `walsh_run_eq_sum_trails` on the one-bundle toy, at `r = 1`: two
rounds, one intermediate mask. -/
theorem one_expansion (k : Fin (1 + 1) → Bits3) :
    (8 : ℤ) * walsh sign₂ B3 B3 (Scheduled.run (fun _ => idBits) (fun _ => chi3) (1 + 1) k) m3 m5
      = ∑ d : Fin 1 → Bits3, trailPhase sign₂ B3 (1 + 1) k (Scheduled.throughTrail m3 d m5)
          * trailCorr sign₂ B3 (fun _ => id) (fun _ => chi3) (1 + 1)
              (Scheduled.throughTrail m3 d m5) := by
  have h := walsh_run_eq_sum_trails B3_separating (fun _ => idBits)
    (fun _ => id) idBits_isAdjoint (fun _ => chi3) 1 k m3 m5
  simp only [card_Bits3, Nat.cast_ofNat, pow_one] at h
  exact h

/-- The same identity, both sides evaluated by the kernel for all `64` key vectors. -/
theorem one_expansion_direct : ∀ k : Fin (1 + 1) → Bits3,
    (8 : ℤ) * walsh sign₂ B3 B3 (Scheduled.run (fun _ => idBits) (fun _ => chi3) (1 + 1) k) m3 m5
      = ∑ d : Fin 1 → Bits3, trailPhase sign₂ B3 (1 + 1) k (Scheduled.throughTrail m3 d m5)
          * trailCorr sign₂ B3 (fun _ => id) (fun _ => chi3) (1 + 1)
              (Scheduled.throughTrail m3 d m5) := by
  decide +kernel

/-- The key-averaged count by its definition: the kernel sums the squared Walsh values of the
two-round toy at `(m3, m5)` over all `64` key pairs. -/
theorem one_elpCount_direct :
    elpCount B3 (fun _ => idBits) (fun _ => chi3) 2 m3 m5 = 512 := by
  decide +kernel

/-- The trail side of Nyberg's identity, evaluated by the kernel: the squared correlations of the
eight trails `m3 → c → m5` sum to `512`. -/
theorem one_trail_sum :
    ∑ d : Fin 1 → Bits3, (trailCorr sign₂ B3 (fun _ => id) (fun _ => chi3) 2
      (Scheduled.throughTrail m3 d m5)).natAbs ^ 2 = 512 := by
  decide +kernel

/-- Nyberg's identity `elpCount_succ_eq_sum_trails` on the one-bundle toy, at `r = 1`. -/
theorem one_nyberg :
    elpCount B3 (fun _ => idBits) (fun _ => chi3) 2 m3 m5 * 8 ^ 2
      = 8 ^ 2 * ∑ d : Fin 1 → Bits3, (trailCorr sign₂ B3 (fun _ => id) (fun _ => chi3) 2
          (Scheduled.throughTrail m3 d m5)).natAbs ^ 2 := by
  have h := elpCount_succ_eq_sum_trails B3_separating (fun _ => idBits)
    (fun _ => id) idBits_isAdjoint (fun _ => chi3) 1 m3 m5
  simp only [card_Bits3, Nat.reduceMul, Nat.reduceAdd] at h
  exact h

/-- **The typed bridge.** The count `512` follows from the theorem and the trail sum, and agrees
with the kernel's direct count over the key pairs (`one_elpCount_direct`). -/
theorem one_elpCount_via_nyberg :
    elpCount B3 (fun _ => idBits) (fun _ => chi3) 2 m3 m5 = 512 := by
  have h := one_nyberg
  rw [one_trail_sum] at h
  omega

/-- **Separation is needed for Nyberg's identity.** Under the zero pairing, which is not
separating (`zeroPairing_not_separating`), every map has the identity as an adjoint, and the
identity of `elpCount_succ_eq_sum_trails` at `r = 1` fails at the masks `(0, 0)`:
`4096 · 64 ≠ 64 · 32768`. -/
theorem one_nyberg_fails_zeroPairing :
    IsAdjoint zeroPairing zeroPairing idBits id ∧
    elpCount zeroPairing (fun _ => idBits) (fun _ => chi3) 2 0 0 * 8 ^ 2
      ≠ 8 ^ 2 * ∑ d : Fin 1 → Bits3, (trailCorr sign₂ zeroPairing (fun _ => id)
          (fun _ => chi3) 2 (Scheduled.throughTrail 0 d 0)).natAbs ^ 2 :=
  ⟨fun _ _ => rfl, by decide +kernel⟩

end Linear.Checks
