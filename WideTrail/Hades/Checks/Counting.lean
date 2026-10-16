import WideTrail.Hades.Probability
import WideTrail.Hades.Checks.Toy

/-! Small exhaustive counts exercise masked and scheduled probability semantics. -/

set_option autoImplicit false
set_option maxRecDepth 16000

namespace Hades.Toy

theorem cube_uniform : IsDiffUniform cube 2 := by decide

theorem identity_coordinate_free :
    diffCount (maskedBricklayer ({0} : Finset (Fin 2)) (fun _ => cube)) ![0, 1] ![0, 1] = 25 := by
  decide

theorem identity_coordinate_mismatch :
    diffCount (maskedBricklayer ({0} : Finset (Fin 2)) (fun _ => cube)) ![0, 1] ![0, 2] = 0 := by
  decide

def probabilityRounds (n : Nat) : RoundSpec (Fin 2) (ZMod 5) where
  mask := if n = 0 then Finset.univ else {0}
  sbox := fun _ => cube
  lin := mix
  constant := values n

def probabilityTrail : Nat → State
  | 0 => ![1, 0]
  | 1 => ![1, 1]
  | _ => ![0, 1]

/-- Enumerate all 625 two-round key vectors. This is a nonzero trail. -/
theorem scheduled_count : keyCount probabilityRounds 2 probabilityTrail 0 = 50 := by decide

theorem scheduled_product_matches :
    keyCount probabilityRounds 2 probabilityTrail 0 =
      ∏ n ∈ Finset.range 2,
        diffCount (maskedBricklayer (probabilityRounds n).mask
          (fun i => (probabilityRounds n).sbox i)) (probabilityTrail n)
          ((probabilityRounds n).lin.symm (probabilityTrail (n + 1))) := by decide

theorem masked_weight_bound :
    keyCount probabilityRounds 2 probabilityTrail 0
      * 2 ^ scheduledWeight probabilityRounds probabilityTrail 0 2 ≤ 25 ^ 2 :=
  keyCount_weight_bound probabilityRounds 2 (fun _ _ _ _ => cube_uniform) (by decide) _ _

end Hades.Toy
