/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.AESSbox
import WideTrail.Linear.Checks.Conventions

/-!
# Checks for the AES S-box linearity bound

Controls for `Linear/AESSbox.lean`, under the trace pairing `GF256.tracePairing`:

* `sbox_walsh_witness_direct`: the witness `W_S(0x55, 0x01) = -32`, evaluated by the kernel
  directly from the definition of `walsh` (a sum of 256 signs), without the reduction of
  `Linear/AESSbox.lean`. It agrees with `AES.sbox_walsh_attained`, which is derived through the
  reduction;
* `sbox_not_isLinearityBound_31`: no bound below `32` holds; with the value `32` of
  `AES.sbox_isLinearityBound` lowered by one the statement is false;
* `sbox_walsh_zero_zero` and `not_forall_sbox_walsh_le`: at the zero masks the Walsh value is
  `256`, so the hypothesis `b ≠ 0` of `AES.sbox_walsh_le` cannot be dropped;
* `walsh_inv_one_witness` and `not_forall_walsh_inv_one_le_28`: the Walsh value of inversion at
  `(0x5c, 1)` is `32`, so not every value of the spectrum is at most `28` in absolute value (the
  natural-number form is `Linear.AESSpectrum.not_forall_specLe_28`);
* `sbox_mul_two_pow_three` and `not_sbox_mul_two_pow_four`: `32 · 2³ ≤ |GF256|` and
  `32 · 2⁴ > |GF256|`. With the bound `32`, the hypothesis `c · 2 ^ d ≤ |K|` of
  `natAbs_trailCorr_mul_pow_le` and `trailCorr_le_of_spec` (`Linear/Trail.lean`) holds for
  `d = 3` and fails for `d = 4`. Through those theorems this S-box bound gives a factor `2⁻³` per
  active S-box in the bound on the correlation `trailCorr` of one trail, which is one summand of
  the fixed-key correlation and not the cipher's correlation for a fixed key;
* `affine_not_selfAdjoint`: the linear part `A` of the S-box's affine map is not a trace adjoint
  of itself (`trace (1 · A 0x20) ≠ trace (A 1 · 0x20)`), so the table of `AES.affAdj` is not the
  trivial choice;
* `trace_eq_trA0`: `GF256.trace` is the functional `Linear.Checks.trA0` of
  `Checks/Conventions.lean`, so the statements made there for the trace form of `trA0` hold for
  the trace pairing, and `trA0` is the absolute trace (`GF256.trace_eq_fieldTrace`).

## What is not claimed

These are checks of single values and of the arithmetic around the bound. They do not recompute
the linear approximation table of the S-box; the bound itself is `AES.sbox_isLinearityBound`.
-/

set_option autoImplicit false

namespace Linear.Checks

open GF256 AES

/-! ### The AES S-box -/

/-- `|GF256| = 256`. This is `card_gf256` of `Differential/AESProb.lean`, proved again here so
that this file does not import the differential modules. -/
theorem card_gf256_eq : Fintype.card GF256 = 256 := by
  rw [Fintype.card_congr (equivBitVec.trans BitVec.equivFin.toEquiv), Fintype.card_fin]
  rfl

/-- A trace-pairing Walsh value as a sum over `n < 256`, the byte `⟨BitVec.ofNat 8 n⟩` standing
for `n`. -/
theorem walsh_eq_sum_range (F : GF256 → GF256) (a b : GF256) :
    walsh sign₂ tracePairing tracePairing F a b
      = ∑ n ∈ Finset.range 256, sign₂ (trace (b * F ⟨BitVec.ofNat 8 n⟩)
          - trace (a * ⟨BitVec.ofNat 8 n⟩)) := by
  rw [← sum_toNat_eq_sum_range fun n => sign₂ (trace (b * F ⟨BitVec.ofNat 8 n⟩)
    - trace (a * ⟨BitVec.ofNat 8 n⟩))]
  unfold walsh
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [show (⟨BitVec.ofNat 8 z.val.toNat⟩ : GF256) = z by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
  rfl

/-- The term `n` of the Walsh sum of the S-box at `(0x55, 0x01)`. -/
def witnessTerm (n : ℕ) : ℤ :=
  sign₂ (trace (⟨0x01#8⟩ * sbox ⟨BitVec.ofNat 8 n⟩) - trace (⟨0x55#8⟩ * ⟨BitVec.ofNat 8 n⟩))

theorem witness_sum₀ : ∑ n ∈ Finset.range 64, witnessTerm n = -2 := by decide +kernel

theorem witness_sum₁ : ∑ n ∈ Finset.range 64, witnessTerm (64 + n) = -2 := by decide +kernel

theorem witness_sum₂ : ∑ n ∈ Finset.range 64, witnessTerm (128 + n) = -26 := by decide +kernel

theorem witness_sum₃ : ∑ n ∈ Finset.range 64, witnessTerm (192 + n) = -2 := by decide +kernel

/-- **The witness, evaluated directly**: the kernel sums the 256 signs of the definition of
`walsh` at `(0x55, 0x01)`, in four chunks of 64 (`-2`, `-2`, `-26`, `-2`). -/
theorem sbox_walsh_witness_direct :
    walsh sign₂ tracePairing tracePairing sbox ⟨0x55#8⟩ ⟨0x01#8⟩ = -32 := by
  rw [walsh_eq_sum_range]
  change ∑ n ∈ Finset.range (64 + 64 + 64 + 64), witnessTerm n = -32
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  simp only [Nat.reduceAdd, witness_sum₀, witness_sum₁, witness_sum₂, witness_sum₃]
  decide

/-- **Negative control**: `31` is not a linearity bound of the S-box under the trace pairing. -/
theorem sbox_not_isLinearityBound_31 : ¬ IsLinearityBound tracePairing sbox 31 := fun h =>
  absurd ((sbox_isLinearityBound_iff 31).mp h) (by decide)

/-- At the zero masks the Walsh value is `|GF256| = 256`. -/
theorem sbox_walsh_zero_zero : walsh sign₂ tracePairing tracePairing sbox 0 0 = 256 := by
  rw [walsh_zero_zero, card_gf256_eq]
  rfl

/-- **The hypothesis `b ≠ 0` of `AES.sbox_walsh_le` is needed.** -/
theorem not_forall_sbox_walsh_le :
    ¬ ∀ a b : GF256, (walsh sign₂ tracePairing tracePairing sbox a b).natAbs ≤ 32 := fun h => by
  have h0 := h 0 0
  rw [sbox_walsh_zero_zero] at h0
  exact absurd h0 (by decide)

/-- The Walsh value of inversion at `(0x5c, 1)` is `32`: `0x5c = 0x55 · affAdj 0x01`. -/
theorem walsh_inv_one_witness :
    walsh sign₂ tracePairing tracePairing (fun x => x⁻¹) ⟨0x5c#8⟩ 1 = 32 := by
  have hc : (⟨0x5c#8⟩ : GF256) = ⟨0x55#8⟩ * affAdj ⟨0x01#8⟩ := by decide +kernel
  rw [walsh_inv_one_eq_spectrum, hc, phi_witness]
  have hac : (⟨0xac#8⟩ : GF256).val.toNat = 0xac := rfl
  rw [hac, Linear.AESSpectrum.mism_ac]
  decide

/-- **Negative control for the spectrum**: not every Walsh value of inversion at the output mask
`1` is at most `28` in absolute value. -/
theorem not_forall_walsh_inv_one_le_28 :
    ¬ ∀ c : GF256, (walsh sign₂ tracePairing tracePairing (fun x => x⁻¹) c 1).natAbs ≤ 28 :=
  fun h => by
    have h5c := h ⟨0x5c#8⟩
    rw [walsh_inv_one_witness] at h5c
    exact absurd h5c (by decide)

/-- `32 · 2³ ≤ |GF256|`: the hypothesis `c · 2 ^ d ≤ |K|` of `natAbs_trailCorr_mul_pow_le` holds
for `c = 32` and `d = 3`, so the bound that theorem gives on the correlation `trailCorr` of one
trail has a factor `2⁻³` per active S-box. -/
theorem sbox_mul_two_pow_three : 32 * 2 ^ 3 ≤ Fintype.card GF256 := by
  rw [card_gf256_eq]
  decide

/-- **`32 · 2⁴ > |GF256|`**: the hypothesis `c · 2 ^ d ≤ |K|` of `natAbs_trailCorr_mul_pow_le`
fails for `c = 32` and `d = 4`, so with the bound `32` the exponent `3` cannot be raised to `4`
there. -/
theorem not_sbox_mul_two_pow_four : ¬ 32 * 2 ^ 4 ≤ Fintype.card GF256 := by
  rw [card_gf256_eq]
  decide

/-- The linear part of the S-box's affine map is not a trace adjoint of itself. -/
theorem affine_not_selfAdjoint : ¬ IsAdjoint tracePairing tracePairing affine affine := fun h => by
  have h1 := h ⟨0x01#8⟩ ⟨0x20#8⟩
  revert h1
  decide +kernel

/-- `GF256.trace` is the functional with mask `0xA0` of `Checks/Conventions.lean`. -/
theorem trace_eq_trA0 : GF256.trace = trA0 :=
  addHom_ext (by decide +kernel)

end Linear.Checks
