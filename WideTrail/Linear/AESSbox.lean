/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.GF256Trace
import WideTrail.Linear.Binary
import WideTrail.Algebra.AESSbox

/-!
# The linearity bound of the AES S-box, under the trace pairing

Every trace-pairing Walsh value of the AES S-box at a nonzero output mask is at most `32` in
absolute value: every correlation of a component `x ↦ Tr(b · S x)` with a linear function
`x ↦ Tr(a · x)` is at most `2⁻³` in absolute value (`AES.sbox_walsh_le`). The bound is attained
(`AES.sbox_walsh_attained`).

## The pairing

The pairing is the trace pairing `GF256.tracePairing`, `⟨u, x⟩ = trace (u * x)`, for the
functional `GF256.trace` with mask `0xA0`, which equals the absolute trace of `GF(2⁸)`
(`GF256.trace_eq_fieldTrace`). It is separating for `sign₂` (`GF256.tracePairing_separating`).
It is the pairing chosen for AES (see `Character.lean`): under it the adjoint of a
`GF(2⁸)`-matrix is its field transpose. Nothing here makes it *the* pairing of the type `GF256`;
the bit pairing (parity of `u ∧ x`) is not treated in this file.

## The reduction

The S-box is `S x = A (x⁻¹) + 0x63` with `A = AES.affine` additive. The Walsh values of all
`256 · 255` pairs of masks with `b ≠ 0` reduce to one spectrum of 256 values:

1. `AES.affAdj`, given by the images `1e 6e 88 5f b8 6b d0 ef` of the basis bytes, is a trace
   adjoint of `A`: `trace (b * A y) = trace (affAdj b * y)` (`AES.affine_isAdjoint`). The identity
   is checked by the kernel on the `8 · 8` basis pairs and extended by additivity in each
   argument. `affAdj b ≠ 0` for `b ≠ 0`, from the separation of the pairing
   (`AES.affAdj_eq_zero`).
2. (W2) and (W3) (`walsh_postAdd`, `walsh_comp_adjoint`):
   `W_S(a, b) = sign₂ (trace (b * 0x63)) · W_inv(a, affAdj b)` (`AES.walsh_sbox_eq`).
3. (W10) (`walsh_inv_mul`): for `β ≠ 0`, `W_inv(a, β) = W_inv(a * β, 1)`.
4. `W_inv(c, 1) = ∑_z (-1) ^ (trace z⁻¹ + trace (c * z)) = 256 - 2 · mism (phi c) 256`
   (`AES.walsh_inv_one_eq_spectrum`), with `mism` the count of `Linear/AESSpectrum.lean`. The sum
   over `GF256` is reindexed as a sum over `n < 256`; each term is rewritten with
   `GF256.trace_inv_eq_g` (the table of `trace z⁻¹`) and `GF256.trace_mul_eq_par8` (the mask
   `phi c` of `z ↦ trace (c * z)`).
5. `Linear.AESSpectrum.spectrum_bound`: `|256 - 2 · mism w 256| ≤ 32` for every mask `w < 256`,
   checked by the kernel on natural numbers.

Together (`AES.walsh_sbox_eq_spectrum`): for `b ≠ 0`,
`W_S(a, b) = sign₂ (trace (b * 0x63)) · (256 - 2 · mism (phi (a * affAdj b)) 256)`. By its
definition `W_inv(c, 1)` is the binary Kloosterman sum of `c` with the term `z = 0` included; no
property of Kloosterman sums is used.

Two lemmas used in step 4 are stated in this file because they need Mathlib's finite sums, which
`Linear/AESSpectrum.lean` does not import: `Linear.AESSpectrum.mism_eq_sum` (the count
`mism w N` as a sum over `n < N`) and `Linear.sign₂_natCast_sub` (one term of a Walsh sum, with
the two bits given as natural numbers).

## What is proved

* `AES.walsh_inv_one_le`: `|W_inv(c, 1)| ≤ 32` for every `c`;
* `AES.sbox_walsh_le`: `|W_S(a, b)| ≤ 32` for every `a` and every `b ≠ 0`;
* `AES.sbox_isLinearityBound`: `IsLinearityBound tracePairing sbox 32`, which also covers
  `b = 0` (the Walsh value is `0` there for `a ≠ 0`, by (W8));
* `AES.sbox_walsh_attained`: `W_S(0x55, 0x01) = -32`, so `32` is the least linearity bound
  (`AES.sbox_isLinearityBound_iff`).

## What is not claimed

This is a statement about one S-box under the trace pairing. Nothing here is about a trail, a key
or a round of AES. The bit-pairing linear approximation table of the S-box is not computed; the
two pairings differ by a relabelling of masks (`walsh_maskRelabel`) through `GF256.phi`, but
`phi` is not shown here to be a bijection, so no bit-pairing bound is derived. The full table of
`255 · 256` Walsh values is not evaluated: the bound comes from the reduction above and the one
spectrum of 256 values.
-/

set_option autoImplicit false

namespace GF256

open Linear

/-- The trace pairing of `GF(2⁸)`: `⟨u, x⟩ = trace (u * x)`. -/
abbrev tracePairing : Pairing GF256 (ZMod 2) := Pairing.traceForm trace

theorem tracePairing_dot (u x : GF256) : tracePairing.dot u x = trace (u * x) := rfl

/-- The trace pairing is separating: `trace 0x20 = 1`. -/
theorem tracePairing_separating : tracePairing.Separating sign₂ :=
  Pairing.traceForm_separating trace (t := basis 5) (by decide +kernel)

/-- Every byte is its own negative: `v + v = 0` (the sum is xor). -/
theorem add_self (v : GF256) : v + v = 0 := ext BitVec.xor_self

/-- A sum over the bytes, reindexed as a sum over `n < 256`. -/
theorem sum_toNat_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ z : GF256, f z.val.toNat = ∑ n ∈ Finset.range 256, f n := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (equivBitVec.trans BitVec.equivFin.toEquiv) _ _ fun _ => rfl

end GF256

namespace Linear

/-- One term of a Walsh sum, with the two bits given as natural numbers `a, b < 2`:
`sign₂ (b - a) = 1 - 2 (a xor b)`. -/
theorem sign₂_natCast_sub {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    sign₂ ((b : ZMod 2) - (a : ZMod 2)) = 1 - 2 * ((a ^^^ b : ℕ) : ℤ) := by
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  all_goals obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  all_goals decide

/-- The count `mism w N` as a sum of its terms. -/
theorem AESSpectrum.mism_eq_sum (w N : ℕ) :
    (AESSpectrum.mism w N : ℤ)
      = ∑ n ∈ Finset.range N, ((AESSpectrum.par8 (w &&& n) ^^^ AESSpectrum.g n : ℕ) : ℤ) := by
  induction N with
  | zero => simp [AESSpectrum.mism]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [AESSpectrum.mism]

end Linear

namespace AES

open Linear GF256
open Linear.AESSpectrum (par8 g mism)

/-! ### The trace adjoint of the affine map -/

/-- The images of the basis bytes `2⁰, …, 2⁷` under `affAdj`. -/
def affAdjImg : Fin 8 → GF256 :=
  ![⟨0x1e#8⟩, ⟨0x6e#8⟩, ⟨0x88#8⟩, ⟨0x5f#8⟩, ⟨0xb8#8⟩, ⟨0x6b#8⟩, ⟨0xd0#8⟩, ⟨0xef#8⟩]

/-- A trace adjoint of `A = AES.affine` (the S-box's affine map without its constant `0x63`):
the additive map with `affAdj 2ⁱ = affAdjImg i` (`affine_isAdjoint`). -/
def affAdj : GF256 →+ GF256 where
  toFun b := ∑ i : Fin 8, if b.val.getLsbD i then affAdjImg i else 0
  map_zero' := by decide +kernel
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (if (x.val ^^^ y.val).getLsbD i then affAdjImg i else 0) = _
    rw [BitVec.getLsbD_xor]
    cases x.val.getLsbD i <;> cases y.val.getLsbD i <;> simp [GF256.add_self]

/-- **`affAdj` is a trace adjoint of `A`**: `trace (b * A y) = trace (affAdj b * y)`. The
identity is checked on the `8 · 8` basis pairs and extended by additivity in `y`, then in `b`. -/
theorem affine_isAdjoint : IsAdjoint tracePairing tracePairing affine affAdj := by
  have hbasis : ∀ i j : Fin 8,
      trace (basis i * affine (basis j)) = trace (affAdj (basis i) * basis j) := by
    decide +kernel
  have hb : ∀ b j, trace (b * affine (basis j)) = trace (affAdj b * basis j) := fun b j =>
    DFunLike.congr_fun (addHom_ext (f := trace.comp (AddMonoidHom.mulRight (affine (basis j))))
      (f' := (trace.comp (AddMonoidHom.mulRight (basis j))).comp affAdj) fun i => hbasis i j) b
  intro b y
  exact DFunLike.congr_fun (addHom_ext
    (f := (trace.comp (AddMonoidHom.mulLeft b)).comp affineEquiv.toAddMonoidHom)
    (f' := trace.comp (AddMonoidHom.mulLeft (affAdj b))) (hb b)) y

/-- `affAdj b = 0` only for `b = 0`: `A` is onto and the trace pairing is separating. -/
theorem affAdj_eq_zero {b : GF256} (h : affAdj b = 0) : b = 0 := by
  refine tracePairing_separating.eq_zero_of_dot_left fun x => ?_
  have hx := affine_isAdjoint b (affineInv x)
  rw [affine_right_inv] at hx
  rw [hx, h]
  simp

/-! ### The reduction to one spectrum -/

/-- **(W2) and (W3) for the S-box**: `W_S(a, b) = sign₂ (trace (b * 0x63)) · W_inv(a, affAdj b)`. -/
theorem walsh_sbox_eq (a b : GF256) :
    walsh sign₂ tracePairing tracePairing sbox a b
      = sign₂ (trace (b * ⟨0x63#8⟩))
        * walsh sign₂ tracePairing tracePairing (fun x => x⁻¹) a (affAdj b) := by
  have h := walsh_postAdd sign₂ tracePairing tracePairing (fun x => affine x⁻¹) ⟨0x63#8⟩ a b
  rw [walsh_comp_adjoint sign₂ tracePairing tracePairing tracePairing affine_isAdjoint
    (fun x => x⁻¹) a b] at h
  exact h

/-- **The Walsh values of inversion at the output mask `1` are one spectrum**:
`W_inv(c, 1) = ∑_z (-1) ^ (trace z⁻¹ + trace (c * z)) = 256 - 2 · mism (phi c) 256`. -/
theorem walsh_inv_one_eq_spectrum (c : GF256) :
    walsh sign₂ tracePairing tracePairing (fun x => x⁻¹) c 1
      = 256 - 2 * (mism (phi c).val.toNat 256 : ℤ) := by
  have hterm : ∀ z : GF256, sign₂ (tracePairing.dot 1 z⁻¹ - tracePairing.dot c z)
      = 1 - 2 * ((par8 ((phi c).val.toNat &&& z.val.toNat) ^^^ g z.val.toNat : ℕ) : ℤ) :=
    fun z => by
      rw [tracePairing_dot, tracePairing_dot, one_mul, trace_inv_eq_g, trace_mul_eq_par8]
      exact sign₂_natCast_sub (AESSpectrum.par8_lt_two _) (AESSpectrum.g_lt_two _)
  unfold walsh
  simp_rw [hterm]
  rw [sum_toNat_eq_sum_range
      (fun n => 1 - 2 * ((par8 ((phi c).val.toNat &&& n) ^^^ g n : ℕ) : ℤ)),
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← AESSpectrum.mism_eq_sum]
  simp

/-- **Every Walsh value of inversion at the output mask `1` is at most `32`** in absolute
value. -/
theorem walsh_inv_one_le (c : GF256) :
    (walsh sign₂ tracePairing tracePairing (fun x => x⁻¹) c 1).natAbs ≤ 32 := by
  rw [walsh_inv_one_eq_spectrum]
  have h := Linear.AESSpectrum.spectrum_bound (phi c).val.toNat (phi c).val.isLt
  omega

/-- **The reduction**: for `b ≠ 0`, `W_S(a, b) = sign₂ (trace (b * 0x63)) · W_inv(a * affAdj b, 1)`
with `W_inv(c, 1) = 256 - 2 · mism (phi c) 256`. -/
theorem walsh_sbox_eq_spectrum (a b : GF256) (hb : b ≠ 0) :
    walsh sign₂ tracePairing tracePairing sbox a b
      = sign₂ (trace (b * ⟨0x63#8⟩))
        * (256 - 2 * (mism (phi (a * affAdj b)).val.toNat 256 : ℤ)) := by
  rw [walsh_sbox_eq, walsh_inv_mul sign₂ trace a (affAdj b) fun h => hb (affAdj_eq_zero h),
    walsh_inv_one_eq_spectrum]

/-! ### The bound -/

/-- **The AES S-box linearity bound**: under the trace pairing, every Walsh value of the S-box at
a nonzero output mask is at most `32` in absolute value, so every such correlation is at most
`2⁻³` in absolute value. -/
theorem sbox_walsh_le (a b : GF256) (hb : b ≠ 0) :
    (walsh sign₂ tracePairing tracePairing sbox a b).natAbs ≤ 32 := by
  rw [walsh_sbox_eq, Int.natAbs_mul, natAbs_sign₂, one_mul,
    walsh_inv_mul sign₂ trace a (affAdj b) fun h => hb (affAdj_eq_zero h)]
  exact walsh_inv_one_le _

/-- **The AES S-box has linearity bound `32` under the trace pairing**: `|W_S(a, b)| ≤ 32` for
every `a ≠ 0` and every `b`. At `b = 0` the Walsh value is `0` (W8). -/
theorem sbox_isLinearityBound : IsLinearityBound tracePairing sbox 32 := by
  intro a ha b
  by_cases hb : b = 0
  · subst hb
    rw [walsh_zero_right tracePairing_separating sbox ha]
    simp
  · exact sbox_walsh_le a b hb

/-- `phi (0x55 * affAdj 0x01) = 0xac`. -/
theorem phi_witness : phi (⟨0x55#8⟩ * affAdj ⟨0x01#8⟩) = ⟨0xac#8⟩ := by decide +kernel

/-- **The bound `32` is attained**: `W_S(0x55, 0x01) = -32`. -/
theorem sbox_walsh_attained :
    walsh sign₂ tracePairing tracePairing sbox ⟨0x55#8⟩ ⟨0x01#8⟩ = -32 := by
  rw [walsh_sbox_eq_spectrum _ _ (by decide), phi_witness]
  have h63 : trace (⟨0x01#8⟩ * ⟨0x63#8⟩) = 1 := by decide +kernel
  have hac : (⟨0xac#8⟩ : GF256).val.toNat = 0xac := rfl
  rw [h63, hac, Linear.AESSpectrum.mism_ac]
  decide

/-- `32` is the least linearity bound of the S-box under the trace pairing. -/
theorem sbox_isLinearityBound_iff (c : ℕ) : IsLinearityBound tracePairing sbox c ↔ 32 ≤ c := by
  constructor
  · intro h
    have := h ⟨0x55#8⟩ (by decide) ⟨0x01#8⟩
    rw [sbox_walsh_attained] at this
    exact this
  · intro hc a ha b
    exact (sbox_isLinearityBound a ha b).trans hc

end AES
