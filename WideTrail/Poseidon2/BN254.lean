import WideTrail.Poseidon2.BN254Parameters
import WideTrail.Algebra.PowerSbox
import WideTrail.Differential.Polynomial
import WideTrail.Hades.Probability
import Mathlib.Tactic.IntervalCases

/-! A concrete certificate for the pinned BN254 width-three reference permutation.
This covers bijectivity, S-box differential uniformity, external MDS mixing,
outer-round activity, and an independently keyed variant's trail probability.
It does not certify algebraic or subspace-trail resistance. -/

set_option autoImplicit false
set_option maxRecDepth 16000

namespace Poseidon2.BN254

def inverseExponent : Nat :=
  17510594297471420177797124596205820070838691520332827474958563349260646796493

theorem field_card : Fintype.card F = modulus := ZMod.card modulus

theorem inverseExponent_positive : 0 < inverseExponent := by decide

theorem inverseExponent_equation : 5 * inverseExponent = (modulus - 1) * 4 + 1 := by decide

theorem fermat (x : F) (hx : x ≠ 0) : x ^ (modulus - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rw [field_card] at h
  exact h

theorem five_positive : 0 < (5 : Nat) := by decide

def sbox : F ≃ F := Sbox.powerEquivOfFermat modulus 5 inverseExponent 4
  five_positive inverseExponent_positive inverseExponent_equation fermat

theorem sbox_toFun : (sbox : F → F) = fun x => x ^ 5 := rfl

theorem sbox_uniform : IsDiffUniform sbox 4 := by
  rw [sbox_toFun]
  exact Sbox.pow_five_uniform (by decide)

/-- An even power is rejected as a permutation S-box over this field. -/
theorem square_not_injective : ¬ Function.Injective (fun x : F => x ^ 2) := by
  intro h
  have heq : (1 : F) = -1 := h (by ring)
  have htwo : (2 : F) = 0 := by linear_combination heq
  exact (by decide : (2 : F) ≠ 0) htwo

def externalMatrix : Matrix (Fin 3) (Fin 3) F := !![2, 1, 1; 1, 2, 1; 1, 1, 2]

def internalMatrix : Matrix (Fin 3) (Fin 3) F := !![2, 1, 1; 1, 2, 1; 1, 1, 3]

theorem four_ne_zero : (4 : F) ≠ 0 := by decide

theorem seven_ne_zero : (7 : F) ≠ 0 := by decide

def external : State ≃ₗ[F] State where
  toFun x := ![2 * x 0 + x 1 + x 2, x 0 + 2 * x 1 + x 2, x 0 + x 1 + 2 * x 2]
  invFun y := ![(3 * y 0 - y 1 - y 2) / 4, (-y 0 + 3 * y 1 - y 2) / 4,
    (-y 0 - y 1 + 3 * y 2) / 4]
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> field_simp [four_ne_zero] <;> ring
  right_inv y := by
    funext i
    fin_cases i <;> simp <;> field_simp [four_ne_zero] <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

def internal : State ≃ₗ[F] State where
  toFun x := ![2 * x 0 + x 1 + x 2, x 0 + 2 * x 1 + x 2, x 0 + x 1 + 3 * x 2]
  invFun y := ![(5 * y 0 - 2 * y 1 - y 2) / 7, (-2 * y 0 + 5 * y 1 - y 2) / 7,
    (-y 0 - y 1 + 3 * y 2) / 7]
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> field_simp [seven_ne_zero] <;> ring
  right_inv y := by
    funext i
    fin_cases i <;> simp <;> field_simp [seven_ne_zero] <;> ring
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

theorem external_eq_mulVec (x : State) : external x = externalMatrix.mulVec x := by
  funext i
  fin_cases i <;> simp [external, externalMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem internal_eq_mulVec (x : State) : internal x = internalMatrix.mulVec x := by
  funext i
  fin_cases i <;> simp [internal, internalMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

set_option maxHeartbeats 4000000 in
-- The small minors are enumerated; full-size minors use permutation symmetry.
theorem external_mds : IsMDS externalMatrix := by
  have h : ∀ (k : Nat) (a b : Fin k → Fin 3), Function.Injective a → Function.Injective b →
      (externalMatrix.submatrix a b).det ≠ 0 := by
    intro k a b ha hb
    have hk : k ≤ 3 := by simpa using Fintype.card_le_of_injective a ha
    interval_cases k
    · simp
    · revert a b ha hb; decide
    · revert a b ha hb; simp only [Matrix.det_fin_two]; decide
    · have habij : Function.Bijective a :=
        (Fintype.bijective_iff_injective_and_card a).mpr ⟨ha, rfl⟩
      have hbbij : Function.Bijective b :=
        (Fintype.bijective_iff_injective_and_card b).mpr ⟨hb, rfl⟩
      have heq : externalMatrix.submatrix a b =
          (externalMatrix.submatrix (Equiv.ofBijective a habij) id).submatrix
            id (Equiv.ofBijective b hbbij) := by
        rw [Matrix.submatrix_submatrix]; rfl
      rw [heq, Matrix.det_permute', Matrix.det_permute]
      have hsign (σ : Equiv.Perm (Fin 3)) : ((Equiv.Perm.sign σ : ℤ) : F) ≠ 0 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      apply mul_ne_zero (hsign _)
      apply mul_ne_zero (hsign _)
      rw [Matrix.det_fin_three]
      decide
  intro k Row Col hRow hCol
  exact h k _ _
    (fun a b hab => (Row.orderIsoOfFin hRow).injective (Subtype.ext hab))
    (fun a b hab => (Col.orderIsoOfFin hCol).injective (Subtype.ext hab))

theorem external_branch : isBranchBound id external 4 :=
  Hades.branch_of_mds external_mds external external_eq_mulVec

def linear (n : Nat) : State ≃ₗ[F] State := if n < 4 ∨ 60 ≤ n then external else internal

/-- Partial rounds add their constant only at the S-box coordinate. -/
theorem partial_constants_zero : ∀ n : Fin 56, ∀ i : Fin 3, i ≠ 0 → values (4 + n.val) i = 0 := by
  decide

def rounds : Nat → Hades.RoundSpec (Fin 3) F :=
  Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values

/-- Poseidon2 includes the initial external linear layer before its HADES schedule. -/
def permutation (x : State) : State := Hades.execute rounds (external x) 64

theorem permutation_bijective : Function.Bijective permutation :=
  (Hades.execute_bijective rounds 64).comp external.bijective

theorem full_prefix (j : Nat) (hj : j + 1 < 4) : isBranchBound id (linear j) 4 := by
  simpa [linear, show j < 4 by omega] using external_branch

theorem full_suffix (j : Nat) (hj : j + 1 < 4) : isBranchBound id (linear (4 + 56 + j)) 4 := by
  simpa [linear, show 60 ≤ 4 + 56 + j by omega] using external_branch

/-- Every distinct input pair incurs at least sixteen actual S-box applications. -/
theorem activity {x y : State} (hxy : x ≠ y) :
    16 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 64 := by
  simpa only [rounds] using
    Hades.hades_bound 4 56 4 4 {0} (fun _ _ => sbox) linear values
      (fun h => hxy (external.injective h)) full_prefix full_suffix

/-- Exact trail bound for the additional-independent-key model only. -/
theorem independent_key_probability {T : Nat → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values)
        (4 + 56 + 4) T x * 2 ^ (251 * ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2))
      ≤ Fintype.card (Fin 3 → F) ^ (4 + 56 + 4) := by
  have hd : 4 * 2 ^ 251 ≤ Fintype.card F := by rw [ZMod.card]; decide
  exact
    Hades.hades_probability (Idx := Fin 3) (K := F) (u := 4) (d := 251)
      4 56 4 4 {0} (fun _ _ => sbox) linear values
      (fun _ _ _ => sbox_uniform) hd full_prefix full_suffix h0 x

/-- The displayed bound's concrete exponent, separated from large-space conversion. -/
theorem probability_exponent : 251 * ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2) = 4016 := by
  decide

end Poseidon2.BN254
