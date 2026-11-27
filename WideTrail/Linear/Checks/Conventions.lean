/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Masks
import WideTrail.Linear.Binary
import WideTrail.Algebra.AESMix

/-!
# Which pairing gives which transpose, on `GF(2⁸)`

Which maps are adjoints of a linear map depends on the pairing. On `GF(2⁸)` there are two natural
pairings:

* the **bit pairing** `bytePairing`, `⟨u, x⟩ = ∑ᵢ uᵢ xᵢ` on the eight bits (the parity of
  `u ∧ x`), pulled back from `bitPairing (Fin 8)` along the bit decomposition `byteBits`;
* a **trace-form pairing** `Pairing.traceForm ℓ`, `⟨u, x⟩ = ℓ (u · x)`, for an additive
  `ℓ : GF256 →+ ZMod 2`.

Throughout, `two = ⟨0x02#8⟩` is the field element `x`. (The numeral `2 : GF256` is `1 + 1 = 0`.)

Under the bit pairing, multiplication by `two` is **not** an adjoint of itself:

* `bytePairing_counterexample`: `⟨0x01, two · 0x02⟩ = 0` while `⟨two · 0x01, 0x02⟩ = 1`, so
  `not_isAdjoint_byte_two`;
* `isAdjoint_byte_two`: the binary transpose `byteT2` (the transpose of the `8 × 8` bit matrix
  `M2` of `x ↦ two · x`) is an adjoint, and `byteT2 0x01 = 0x80`;
* `byte_adjoint_two_apply_one`: the bit pairing is separating, so every bit adjoint of
  `x ↦ two · x` maps `0x01` to `0x80`.

Under every trace-form pairing, multiplication by a field constant is an adjoint of itself
(`isAdjoint_mul_left` in `Masks.lean`; `trace_adjoint_two` for the constant `two`), and the field
transpose of the `MixColumns` matrix is an adjoint of it (`trace_adjoint_aesMatrix`,
`trace_adjoint_aesMixColumns`). These need not be the only adjoints: under the zero trace form
every map is one (`isAdjoint_traceForm_zero`). For the functional `trA0` with mask `0xA0`,
`x ↦ bit₅ x + bit₇ x`, the trace-form pairing is separating (`trA0_separating`), so the adjoint
of `x ↦ two · x` is unique and every adjoint maps `0x01` to `0x02`
(`trA0_adjoint_two_apply_one`). Under the bit pairing the field transpose of `aesMatrix` is not
an adjoint of `MixColumns`' matrix (`not_isAdjoint_byte_aesMatrix`).

This is why the pairing is chosen per instance (`Character.lean`): a separating trace-form
pairing for ciphers whose linear layers are `GF(2⁸)`-matrices, so that masks move through field
transposes; the bit pairing for byte ciphers without field structure. The identification of
`trA0` with the absolute trace `z + z² + ⋯ + z¹²⁸` is not proved in this file; nothing here
depends on it.
-/

set_option autoImplicit false

namespace Linear.Checks

open GF256

/-- The field element `x` of `GF(2⁸)`, the byte `0x02`. -/
def two : GF256 := ⟨0x02#8⟩

/-- The bits of a byte, least significant first, as an additive bijection. -/
def byteBits : GF256 ≃+ (Fin 8 → ZMod 2) where
  toFun x i := if x.val.getLsbD i then 1 else 0
  invFun z := ⟨BitVec.ofNat 8 (∑ i : Fin 8, (z i).val * 2 ^ (i : ℕ))⟩
  left_inv := by
    change ∀ x, _ = x
    decide +kernel
  right_inv := by
    change ∀ z, _ = z
    decide +kernel
  map_add' x y := by
    funext i
    change (if (x.val ^^^ y.val).getLsbD i then (1 : ZMod 2) else 0)
      = (if x.val.getLsbD i then 1 else 0) + (if y.val.getLsbD i then 1 else 0)
    rw [BitVec.getLsbD_xor]
    cases x.val.getLsbD i <;> cases y.val.getLsbD i <;> decide

/-- The bit pairing of `GF(2⁸)`: `⟨u, x⟩ = ∑ᵢ uᵢ xᵢ` on the bits, the parity of `u ∧ x`. -/
abbrev bytePairing : Pairing GF256 (ZMod 2) :=
  (bitPairing (Fin 8)).comap byteBits.toAddMonoidHom

theorem bytePairing_separating : bytePairing.Separating sign₂ :=
  (bitPairing_separating (Fin 8)).comap byteBits

/-! ### The bit pairing -/

/-- `⟨0x01, two · 0x02⟩ = 0` and `⟨two · 0x01, 0x02⟩ = 1` for the bit pairing. -/
theorem bytePairing_counterexample :
    bytePairing.dot ⟨0x01#8⟩ (two * ⟨0x02#8⟩) = 0
      ∧ bytePairing.dot (two * ⟨0x01#8⟩) ⟨0x02#8⟩ = 1 := by
  decide +kernel

/-- Under the bit pairing, multiplication by `two` is not self-adjoint. -/
theorem not_isAdjoint_byte_two :
    ¬ IsAdjoint bytePairing bytePairing (fun y => two * y) (fun v => two * v) := fun h => by
  have h1 := h ⟨0x01#8⟩ ⟨0x02#8⟩
  rw [bytePairing_counterexample.1, bytePairing_counterexample.2] at h1
  exact absurd h1 (by decide)

/-- `x ↦ two · x`, read on bits. -/
def mulTwoBits : (Fin 8 → ZMod 2) →+ (Fin 8 → ZMod 2) :=
  byteBits.toAddMonoidHom.comp ((AddMonoidHom.mulLeft two).comp byteBits.symm.toAddMonoidHom)

/-- The bit matrix of `x ↦ two · x`: column `j` holds the bits of `two · 2ʲ`. -/
def M2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => mulTwoBits (Pi.single j 1) i

/-- `M2` is the matrix of `x ↦ two · x` on bits. Both sides are additive, so it is checked on
the `8 × 2` vectors `Pi.single i x`. -/
theorem mulTwoBits_eq_mulVec (z : Fin 8 → ZMod 2) : mulTwoBits z = M2.mulVec z := by
  have h := AddMonoidHom.functions_ext (Fin 8 → ZMod 2) mulTwoBits
    (AddMonoidHom.mk' M2.mulVec M2.mulVec_add) (by decide +kernel)
  exact DFunLike.congr_fun h z

/-- `M2` is the matrix of `x ↦ two · x` on the bits of every byte. -/
theorem byteBits_mul_two (x : GF256) : byteBits (two * x) = M2.mulVec (byteBits x) := by
  rw [← mulTwoBits_eq_mulVec]
  simp [mulTwoBits]

/-- The binary transpose of `x ↦ two · x`: apply the transpose of the bit matrix `M2`. -/
def byteT2 (v : GF256) : GF256 := byteBits.symm (M2.transpose.mulVec (byteBits v))

/-- **The binary transpose is a bit-pairing adjoint of `x ↦ two · x`.** -/
theorem isAdjoint_byte_two : IsAdjoint bytePairing bytePairing (fun y => two * y) byteT2 := by
  have h := (isAdjoint_mulVec (AddMonoidHom.id (ZMod 2)) M2).comap byteBits byteBits
  intro v y
  have hv := h v y
  simp only [← byteBits_mul_two, AddEquiv.symm_apply_apply] at hv
  exact hv

/-- The binary transpose of `x ↦ two · x` maps `0x01` to `0x80`. -/
theorem byteT2_one : byteT2 ⟨0x01#8⟩ = ⟨0x80#8⟩ := by decide +kernel

/-- **Every bit-pairing adjoint of `x ↦ two · x` maps `0x01` to `0x80`**, not to `two · 0x01`. -/
theorem byte_adjoint_two_apply_one {Lt : GF256 → GF256}
    (h : IsAdjoint bytePairing bytePairing (fun y => two * y) Lt) : Lt ⟨0x01#8⟩ = ⟨0x80#8⟩ := by
  rw [h.unique bytePairing_separating isAdjoint_byte_two, byteT2_one]

/-- Under the bit pairing the field transpose of the `MixColumns` matrix is not an adjoint of
it: at `v = (0x01, 0, 0, 0)` and `y = (0x02, 0, 0, 0)`, `⟨v, M y⟩ = 0` and `⟨Mᵀ v, y⟩ = 1`. -/
theorem not_isAdjoint_byte_aesMatrix :
    ¬ IsAdjoint bytePairing.pi bytePairing.pi aesMatrix.mulVec aesMatrix.transpose.mulVec :=
  fun h => by
    have h1 := h ![⟨0x01#8⟩, 0, 0, 0] ![⟨0x02#8⟩, 0, 0, 0]
    revert h1
    decide +kernel

/-! ### Trace-form pairings -/

/-- **Under every trace-form pairing, multiplication by `two` is an adjoint of itself.** -/
theorem trace_adjoint_two (ℓ : GF256 →+ ZMod 2) :
    IsAdjoint (Pairing.traceForm ℓ) (Pairing.traceForm ℓ) (fun y => two * y)
      (fun v => two * v) :=
  isAdjoint_mul_left ℓ two

/-- **Under every trace-form pairing, the field transpose of the `MixColumns` matrix is an adjoint
of it.** It is the only one when the trace form is separating (`IsAdjoint.unique`). -/
theorem trace_adjoint_aesMatrix (ℓ : GF256 →+ ZMod 2) :
    IsAdjoint (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi aesMatrix.mulVec
      aesMatrix.transpose.mulVec :=
  isAdjoint_mulVec ℓ aesMatrix

/-- The same, column by column: `aesMixColumns` has the column-wise field transpose of
`aesMatrix` as an adjoint, under every trace-form pairing. -/
theorem trace_adjoint_aesMixColumns (ℓ : GF256 →+ ZMod 2) :
    IsAdjoint (Pairing.traceForm ℓ).pi (Pairing.traceForm ℓ).pi aesMixColumns
      (fun a i => aesMatrix.transpose.mulVec (fun r => a (r, i.2)) i.1) :=
  isAdjoint_colMatrix ℓ aesMatrix

/-- The functional with mask `0xA0`: `x ↦ bit₅ x + bit₇ x`. -/
def trA0 : GF256 →+ ZMod 2 := bytePairing.dot ⟨0xA0#8⟩

/-- Its trace-form pairing is separating: `trA0 0x20 = 1`. -/
theorem trA0_separating : (Pairing.traceForm trA0).Separating sign₂ :=
  Pairing.traceForm_separating trA0 (t := ⟨0x20#8⟩) (by decide +kernel)

/-- **Under the trace form of `trA0`, every adjoint of `x ↦ two · x` maps `0x01` to `0x02`**:
the pairing is separating, so the adjoint is unique and equals multiplication by `two`. -/
theorem trA0_adjoint_two_apply_one {Lt : GF256 → GF256}
    (h : IsAdjoint (Pairing.traceForm trA0) (Pairing.traceForm trA0) (fun y => two * y) Lt) :
    Lt ⟨0x01#8⟩ = ⟨0x02#8⟩ := by
  rw [h.unique trA0_separating (trace_adjoint_two trA0)]
  decide +kernel

end Linear.Checks
