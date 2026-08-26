/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Cipher
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Fin.Basic

/-!
# The AES-shaped instantiation

A square state `Fin m × Fin m` indexed by `(row, column)`, partitioned into columns by
`Prod.snd`, with the AES dispersion layer: row `r` is rotated by `r` positions.

Everything here is about `π`. The two remaining ingredients are supplied as hypotheses,
and it is worth being exact about which is which:

* `PreserveSupport sbox` is *free* for any bricklayer of invertible S-boxes. It says only
  that an S-box sends a zero difference to a zero difference and a nonzero one to a
  nonzero one. Nothing about the AES S-box is used.
* `IsColBranchBound aesCol mix 5` is **not** proved here. It is the MDS property of AES
  MixColumns, equivalent to every square submatrix of the `4 × 4` circulant over
  `GF(2⁸)` being nonsingular. Proving it needs a concrete field and a minor enumeration,
  which is deliberately out of scope; it enters as a named hypothesis so that any reader
  can see precisely what the `25` rests on.

So `aes_four_round` should be read as: *given* that MixColumns has branch number 5, four
rounds of an AES-shaped cipher activate at least 25 S-boxes, and that implication is
kernel-checked.
-/

set_option autoImplicit false

variable {K : Type*} [Zero K] [DecidableEq K]

/-- The state of a square AES-like cipher, indexed by `(row, column)`. -/
abbrev SquareIdx (m : ℕ) := Fin m × Fin m

/-- The column partition of a square state. -/
abbrev sqCol (m : ℕ) : SquareIdx m → Fin m := Prod.snd

/-- The AES dispersion layer as a permutation of bundle positions: reading the paper's
convention `bᵢ = a_{p(i)}`, the bundle at `(r, c)` of the output is the bundle at
`(r, c + r)` of the input, i.e. row `r` is rotated left by `r`. -/
def rowShiftPerm (m : ℕ) [NeZero m] : Equiv.Perm (SquareIdx m) where
  toFun i := (i.1, i.2 + i.1)
  invFun i := (i.1, i.2 - i.1)
  left_inv := fun i => by simp
  right_inv := fun i => by simp

/-- Row rotation is diffusion-optimal on a square state: two distinct bundles of one
column sit in distinct rows, and within a fixed column the shift `r ↦ c + r` is
injective, so they land in distinct columns.

This is the whole content of Definition 5 for AES, and it holds for every square state
size, not just `4`. -/
theorem rowShift_diffusionOptimal (m : ℕ) [NeZero m] :
    DiffusionOptimal (sqCol m) (rowShiftPerm m) := by
  rintro ⟨r, c⟩ ⟨r', c'⟩ hne hcol h
  simp only [rowShiftPerm, Equiv.coe_fn_mk] at h
  subst hcol
  exact hne (by simp [add_left_cancel h])

/-- The same fact for the AES state size, re-derived by kernel evaluation over all
`16 × 16` position pairs. Redundant with `rowShift_diffusionOptimal`, and kept as an
independent check that the permutation really is the ShiftRows one. -/
theorem shiftRows_diffusionOptimal :
    DiffusionOptimal (sqCol 4) (rowShiftPerm 4) := by
  change ∀ i j : SquareIdx 4, i ≠ j → i.2 = j.2 →
    (rowShiftPerm 4 i).2 ≠ (rowShiftPerm 4 j).2
  decide

/-- An AES-shaped wide-trail specification: SubBytes, ShiftRows, MixColumns.

`mix` and its branch number are parameters, so this covers AES itself and every cipher
with the same round shape and a branch-`b` column mixing. -/
def squareSpec (m : ℕ) [NeZero m] (sbox mix : (SquareIdx m → K) → (SquareIdx m → K))
    (b : ℕ) (hsbox : PreserveSupport sbox) (hmix : IsColBranchBound (sqCol m) mix b)
    (hnd : NonDegenerate mix) : WideTrailSpec (SquareIdx m) (Fin m) K where
  col := sqCol m
  sbox := sbox
  disp := rowShiftPerm m
  mix := mix
  branch := b
  sbox_preserves := hsbox
  disp_optimal := rowShift_diffusionOptimal m
  mix_branch := hmix
  mix_nondeg := hnd

/-- The AES specification: a `4 × 4` byte state and a branch-5 MixColumns. -/
def aesSpec (sbox mix : (SquareIdx 4 → K) → (SquareIdx 4 → K))
    (hsbox : PreserveSupport sbox) (hmix : IsColBranchBound (sqCol 4) mix 5)
    (hnd : NonDegenerate mix) : WideTrailSpec (SquareIdx 4) (Fin 4) K :=
  squareSpec 4 sbox mix 5 hsbox hmix hnd

section AES

variable (sbox mix : (SquareIdx 4 → K) → (SquareIdx 4 → K))
  (hsbox : PreserveSupport sbox) (hmix : IsColBranchBound (sqCol 4) mix 5)
  (hnd : NonDegenerate mix)

/-- The four-round bound of the AES specification evaluates to `25`, by computation. -/
@[simp] theorem aes_fourRoundBound :
    (aesSpec sbox mix hsbox hmix hnd).fourRoundBound = 25 := rfl

/-- **25 active S-boxes in four rounds.** Any four consecutive rounds of an AES-shaped
cipher on a nonzero trail activate at least 25 S-boxes. -/
theorem aes_four_round {a : SquareIdx 4 → K} (ha : a ≠ 0) (n : ℕ) :
    25 ≤ weight ((aesSpec sbox mix hsbox hmix hnd).trail a n)
      + weight ((aesSpec sbox mix hsbox hmix hnd).trail a (n + 1))
      + weight ((aesSpec sbox mix hsbox hmix hnd).trail a (n + 2))
      + weight ((aesSpec sbox mix hsbox hmix hnd).trail a (n + 3)) :=
  (aesSpec sbox mix hsbox hmix hnd).four_round ha n

/-- **50 active S-boxes in the ten rounds of AES-128**, by splitting off two disjoint
four-round blocks. -/
theorem aes128_ten_round {a : SquareIdx 4 → K} (ha : a ≠ 0) :
    50 ≤ (aesSpec sbox mix hsbox hmix hnd).trailWeight a 10 := by
  have h8 := (aesSpec sbox mix hsbox hmix hnd).trailWeight_bound ha 2
  have hmono := (aesSpec sbox mix hsbox hmix hnd).trailWeight_mono a (r := 4 * 2)
    (r' := 10) (by omega)
  have hval : (2 : ℕ) * (aesSpec sbox mix hsbox hmix hnd).fourRoundBound = 50 := rfl
  omega

end AES
