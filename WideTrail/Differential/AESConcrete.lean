import WideTrail.Algebra.AESSbox
import WideTrail.Differential.Polynomial
import WideTrail.Differential.AESProb

/-! AES S-box obligations discharged for the independent-round-key trail bounds. -/

set_option autoImplicit false

namespace AES

theorem diffCount_postAdd {X Y : Type*} [Fintype X] [AddCommGroup X]
    [AddCommGroup Y] [DecidableEq Y] (f : X → Y) (c : Y) (a : X) (b : Y) :
    diffCount (fun x => f x + c) a b = diffCount f a b := by
  unfold diffCount
  congr 1
  ext x
  simp [mem_diffSet]

/-- The concrete AES S-box has differential uniformity at most four. -/
theorem sbox_uniform : IsDiffUniform sbox 4 := by
  intro a ha b
  have h : diffCount sbox a b = diffCount (fun x : GF256 => x⁻¹) a (affineEquiv.symm b) := by
    change diffCount (fun x => affineEquiv x⁻¹ + (⟨0x63#8⟩ : GF256)) a b = _
    rw [diffCount_postAdd, diffCount_addEquiv]
  rw [h]
  exact Sbox.inv_uniform a ha _

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
-- This one differential enumerates the 256 concrete input bytes.
/-- The upper bound is attained, so the concrete uniformity is exactly four. -/
theorem sbox_uniformity_witness : diffCount sbox ⟨1#8⟩ ⟨0x1f#8⟩ = 4 := by decide

theorem four_round_probability {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer (fun _ => sbox)) 4 T x * 2 ^ 150
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 4 :=
  aes_four_round_prob (fun _ => sbox_injective) (fun _ => sbox_uniform) h0 x

theorem ten_round_probability {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer (fun _ => sbox)) 10 T x * 2 ^ 330
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 10 :=
  aes128_ten_round_prob (fun _ => sbox_injective) (fun _ => sbox_uniform) h0 x

theorem twelve_round_probability {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer (fun _ => sbox)) 12 T x * 2 ^ 450
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 12 :=
  aes192_twelve_round_prob (fun _ => sbox_injective) (fun _ => sbox_uniform) h0 x

theorem fourteen_round_probability {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer (fun _ => sbox)) 14 T x * 2 ^ 480
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 14 :=
  aes256_fourteen_round_prob (fun _ => sbox_injective) (fun _ => sbox_uniform) h0 x

end AES
