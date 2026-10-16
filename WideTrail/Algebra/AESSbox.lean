import WideTrail.Algebra.GF256

/-! The FIPS 197 byte substitution: inversion followed by the binary affine map. -/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace AES

def affine (x : GF256) : GF256 :=
  ⟨x.val ^^^ x.val.rotateLeft 1 ^^^ x.val.rotateLeft 2
    ^^^ x.val.rotateLeft 3 ^^^ x.val.rotateLeft 4⟩

def affineInv (x : GF256) : GF256 :=
  ⟨x.val.rotateLeft 1 ^^^ x.val.rotateLeft 3 ^^^ x.val.rotateLeft 6⟩

theorem affine_left_inv : ∀ x, affineInv (affine x) = x := by decide

theorem affine_right_inv : ∀ x, affine (affineInv x) = x := by decide

theorem rotate_xor (x y : BitVec 8) (n : Nat) :
    (x ^^^ y).rotateLeft n = x.rotateLeft n ^^^ y.rotateLeft n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  by_cases h : i < n % 8 <;> simp [h, hi]

theorem affine_add (x y : GF256) : affine (x + y) = affine x + affine y := by
  apply GF256.ext
  change (x.val ^^^ y.val) ^^^ (x.val ^^^ y.val).rotateLeft 1
      ^^^ (x.val ^^^ y.val).rotateLeft 2 ^^^ (x.val ^^^ y.val).rotateLeft 3
      ^^^ (x.val ^^^ y.val).rotateLeft 4 =
    (x.val ^^^ x.val.rotateLeft 1 ^^^ x.val.rotateLeft 2 ^^^ x.val.rotateLeft 3
      ^^^ x.val.rotateLeft 4) ^^^
    (y.val ^^^ y.val.rotateLeft 1 ^^^ y.val.rotateLeft 2 ^^^ y.val.rotateLeft 3
      ^^^ y.val.rotateLeft 4)
  simp only [rotate_xor]
  ac_rfl

def affineEquiv : GF256 ≃+ GF256 where
  toFun := affine
  invFun := affineInv
  left_inv := affine_left_inv
  right_inv := affine_right_inv
  map_add' := affine_add

/-- The affine constant is the AES byte 0x63, interpreted in the binary field. -/
def sbox (x : GF256) : GF256 := affine x⁻¹ + ⟨0x63#8⟩

def sboxInv (x : GF256) : GF256 := (affineInv (x - ⟨0x63#8⟩))⁻¹

theorem sbox_left_inv (x : GF256) : sboxInv (sbox x) = x := by
  simp [sboxInv, sbox, affine_left_inv]

theorem sbox_right_inv (x : GF256) : sbox (sboxInv x) = x := by
  simp [sboxInv, sbox, affine_right_inv]

def sboxEquiv : GF256 ≃ GF256 where
  toFun := sbox
  invFun := sboxInv
  left_inv := sbox_left_inv
  right_inv := sbox_right_inv

theorem sbox_injective : Function.Injective sbox := sboxEquiv.injective

end AES
