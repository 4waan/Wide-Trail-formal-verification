/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer1.Grid

/-!
# The AES-shaped instantiation

The square state `Fin m × Fin m` is the `rows = cols` case of `GridIdx`, and the AES
dispersion layer, row `r` rotated by `r`, is `shiftRowsPerm` at the offset vector `id`.
Everything about `π` therefore comes from `Grid.lean`: diffusion optimality of AES
ShiftRows is injectivity of the identity.

The two remaining ingredients are supplied as hypotheses, and it is worth being exact
about which is which:

* `PreserveSupport sbox` is *free* for any bricklayer of invertible S-boxes. It says only
  that an S-box sends a zero difference to a zero difference and a nonzero one to a
  nonzero one. Nothing about the AES S-box is used.
* `IsColBranchBound aesCol mix 5` is **not** proved here. It is the MDS property of AES
  MixColumns, equivalent to every square submatrix of the `4 × 4` circulant over
  `GF(2⁸)` being nonsingular. It is discharged in Layer 2; it enters here as a named
  hypothesis so that any reader can see precisely what the `25` rests on.

So `aes_four_round` should be read as: *given* that MixColumns has branch number 5, four
rounds of an AES-shaped cipher activate at least 25 S-boxes, and that implication is
kernel-checked.

## The round counts

`aes_rounds` is `WideTrailSpec.trailWeight_bound_rounds` with the two AES constants
substituted, and the three key sizes are that theorem at `r = 10, 12, 14`:

| rounds | blocks | tail | bound |
| ------ | ------ | ---- | ----- |
| 10     | 2      | 2    | 55    |
| 12     | 3      | 0    | 75    |
| 14     | 3      | 2    | 80    |

The `55` deserves a word, because the number usually quoted for ten-round AES-128 is
`50`. `50` is what four-round blocks alone give: `10 = 2 · 4 + 2`, and the two rounds left
over get discarded. They need not be. Rounds 8 and 9 are still two consecutive rounds, so
Theorem 1 charges `B = 5` active S-boxes to them, on rounds disjoint from both blocks. The
literature quotes `50` because it states the result per four-round block and leaves the
composition to the reader; the theorems in this repository already proved the stronger
statement, and `trailWeight_bound_add_two` is the one line that extracts it.

`55` is still a lower bound on a lower bound, not the true minimum.
-/

set_option autoImplicit false

variable {K : Type*} [Zero K] [DecidableEq K]

/-- The state of a square AES-like cipher, indexed by `(row, column)`. -/
abbrev SquareIdx (m : ℕ) := GridIdx m m

/-- The column partition of a square state. -/
abbrev sqCol (m : ℕ) : SquareIdx m → Fin m := gridCol m m

/-- The AES dispersion layer as a permutation of bundle positions: reading the paper's
convention `bᵢ = a_{p(i)}`, the bundle at `(r, c)` of the output is the bundle at
`(r, c + r)` of the input, i.e. row `r` is rotated left by `r`.

On a square state the offset vector is the identity, which is where AES's `0, 1, 2, 3`
comes from: the shift amounts are the row indices themselves. -/
def rowShiftPerm (m : ℕ) [NeZero m] : Equiv.Perm (SquareIdx m) := shiftRowsPerm m m id

/-- Row rotation is diffusion-optimal on a square state, because the identity is
injective. Definition 5 for AES is exactly that, and it holds for every square state
size, not just `4`. -/
theorem rowShift_diffusionOptimal (m : ℕ) [NeZero m] :
    DiffusionOptimal (sqCol m) (rowShiftPerm m) :=
  (diffusionOptimal_shiftRowsPerm_iff m m id).mpr Function.injective_id

/-- The same fact for the AES state size, re-derived by kernel evaluation over all
`16 × 16` position pairs. Redundant with `rowShift_diffusionOptimal`, and kept as an
independent check that the permutation really is the ShiftRows one, evaluated rather
than reasoned about. -/
theorem shiftRows_diffusionOptimal :
    DiffusionOptimal (sqCol 4) (rowShiftPerm 4) := by decide

/-- An AES-shaped wide-trail specification: SubBytes, ShiftRows, MixColumns.

`mix` and its branch number are parameters, so this covers AES itself and every cipher
with the same round shape and a branch-`b` column mixing. -/
def squareSpec (m : ℕ) [NeZero m] (sbox mix : (SquareIdx m → K) → (SquareIdx m → K))
    (b : ℕ) (hsbox : PreserveSupport sbox) (hmix : IsColBranchBound (sqCol m) mix b)
    (hnd : NonDegenerate mix) : WideTrailSpec (SquareIdx m) (Fin m) K :=
  gridSpec m m id sbox mix b hsbox Function.injective_id hmix hnd

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

/-- **The AES bound at an arbitrary round count.** `r / 4` four-round blocks contribute
`25` each, and a leftover of two or three rounds still contains a two-round block, which
contributes `5` more on rounds disjoint from every block. -/
theorem aes_rounds {a : SquareIdx 4 → K} (ha : a ≠ 0) (r : ℕ) :
    r / 4 * 25 + (if 2 ≤ r % 4 then 5 else 0)
      ≤ (aesSpec sbox mix hsbox hmix hnd).trailWeight a r := by
  have h := (aesSpec sbox mix hsbox hmix hnd).trailWeight_bound_rounds ha r
  have e₁ : (aesSpec sbox mix hsbox hmix hnd).fourRoundBound = 25 := rfl
  have e₂ : (aesSpec sbox mix hsbox hmix hnd).branch = 5 := rfl
  rwa [e₁, e₂] at h

/-- **55 active S-boxes in the ten rounds of AES-128.** Two disjoint four-round blocks give
`50`; rounds 8 and 9 are a two-round block on top of them and give `5` more. -/
theorem aes128_ten_round {a : SquareIdx 4 → K} (ha : a ≠ 0) :
    55 ≤ (aesSpec sbox mix hsbox hmix hnd).trailWeight a 10 := by
  have h := aes_rounds sbox mix hsbox hmix hnd ha 10
  have hval : (10 : ℕ) / 4 * 25 + (if 2 ≤ 10 % 4 then 5 else 0) = 55 := by decide
  omega

/-- The `50` that discarding the last two rounds gives, kept so that the sharpening is
visible as a strict improvement over the same theorems rather than as a restatement. -/
theorem aes128_ten_round_blocks_only {a : SquareIdx 4 → K} (ha : a ≠ 0) :
    50 ≤ (aesSpec sbox mix hsbox hmix hnd).trailWeight a 10 :=
  le_trans (by decide) (aes128_ten_round sbox mix hsbox hmix hnd ha)

/-- **75 active S-boxes in the twelve rounds of AES-192.** `12 = 3 · 4`, so the block
tiling is exact and there is no tail to recover. -/
theorem aes192_twelve_round {a : SquareIdx 4 → K} (ha : a ≠ 0) :
    75 ≤ (aesSpec sbox mix hsbox hmix hnd).trailWeight a 12 := by
  have h := aes_rounds sbox mix hsbox hmix hnd ha 12
  have hval : (12 : ℕ) / 4 * 25 + (if 2 ≤ 12 % 4 then 5 else 0) = 75 := by decide
  omega

/-- **80 active S-boxes in the fourteen rounds of AES-256.** Three blocks and a two-round
tail. -/
theorem aes256_fourteen_round {a : SquareIdx 4 → K} (ha : a ≠ 0) :
    80 ≤ (aesSpec sbox mix hsbox hmix hnd).trailWeight a 14 := by
  have h := aes_rounds sbox mix hsbox hmix hnd ha 14
  have hval : (14 : ℕ) / 4 * 25 + (if 2 ≤ 14 % 4 then 5 else 0) = 80 := by decide
  omega

end AES
