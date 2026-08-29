/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Layer2.AESMix
import WideTrail.Layer3.TrailProb

/-!
# AES: from `25` active S-boxes to `2⁻¹⁵⁰`

The numbers, at last. AES has `|K| = 256`, `|Idx| = 16`, and an S-box whose differential
uniformity is `4`; since `4 · 2⁶ = 256`, each active S-box costs a factor `2⁻⁶`. Layer 1
supplies the count and Layer 3 supplies the exponent:

| rounds | active S-boxes | trail probability |
| ------ | -------------- | ----------------- |
| 4      | 25             | `2⁻¹⁵⁰`           |
| 10     | 55             | `2⁻³³⁰`           |
| 12     | 75             | `2⁻⁴⁵⁰`           |
| 14     | 80             | `2⁻⁴⁸⁰`           |

Each statement has the exact shape `count · 2 ^ e ≤ |X| ^ r`, where `|X| ^ r = 2 ^ (128 r)`
is the size of the round-key space, so it reads directly as `DP ≤ 2⁻ᵉ` with no division.

## The two hypotheses, and which one is discharged

`aesMixColumns_isColBranchBound` is proved: Layer 2 computes the MDS property of the real
matrix over the real field. The branch number `5` is a theorem here.

`IsDiffUniform s 4` is **not** proved. It is the differential uniformity of the AES S-box,
and it enters exactly the way `IsColBranchBound` entered Layer 1: as a named hypothesis, so
that the reader can see what the `2⁻¹⁵⁰` rests on. It is not left open for lack of
interest. Checking it by kernel `decide` means `256 · 256` differentials each scanning
`256` inputs, about `16.7` million field operations, and `Layer2/GF256.lean` records that
enumerations of exactly that size do not finish in the kernel. Closing it needs the same
kind of structural argument that file used for associativity, applied to inversion in
`GF(2⁸)`, and that is a separate piece of work.

## The S-box field of the specification

`WideTrailSpec` carries an `sbox` field with a `PreserveSupport` obligation. Layer 3 proves
that obligation from injectivity of the actual S-boxes
(`activePattern_eq_of_diffCount_ne_zero`), so the field is never read here and the
placeholder `id` is used. That is the honest reading of the field: it always was a stand-in
for a support constraint, and the constraint is now derived from the cipher rather than
assumed about a function that does not exist.
-/

set_option autoImplicit false
-- `Fintype.card GF256` reduces by evaluating a 256-element enumeration, which needs more
-- than the default recursion budget.
set_option maxRecDepth 8000
-- The exponents here are 150 to 480; `rw` would otherwise emit a notice for declining to
-- evaluate `2 ^ 330` as a numeral, which is exactly what it should decline to do.
set_option exponentiation.threshold 1000

/-- The AES wide-trail specification, used at Layer 3 only through its linear layer, its
branch number `5` and its diffusion-optimal dispersion. The `sbox` placeholder is the
identity: the real S-box layer is the `bricklayer s` appearing in the theorems below, and
its support-preservation is derived, not assumed. -/
def aesLinSpec : WideTrailSpec (SquareIdx 4) (Fin 4) GF256 :=
  aesSpec id aesMixColumns (fun _ => rfl) aesMixColumns_isColBranchBound
    aesMixColumns_nondegenerate

@[simp] theorem aesLinSpec_fourRoundBound : aesLinSpec.fourRoundBound = 25 := rfl

@[simp] theorem aesLinSpec_branch : aesLinSpec.branch = 5 := rfl

theorem aesLinSpec_lin_add (x y : SquareIdx 4 → GF256) :
    aesLinSpec.lin (x + y) = aesLinSpec.lin x + aesLinSpec.lin y := by
  change aesMixColumns (transpose (rowShiftPerm 4) (x + y)) = _
  rw [show transpose (rowShiftPerm 4) (x + y)
      = transpose (rowShiftPerm 4) x + transpose (rowShiftPerm 4) y from rfl,
    aesMixColumns_add]
  rfl

/-- `ShiftRows` followed by `MixColumns`, as an additive bijection of the AES state. This
is the `λ` that the Layer 3 theorems multiply over rounds. -/
noncomputable def aesLin : (SquareIdx 4 → GF256) ≃+ (SquareIdx 4 → GF256) :=
  linAddEquiv aesLinSpec_lin_add aesLinSpec.lin_nondeg

theorem aesLin_apply (b : SquareIdx 4 → GF256) : aesLin b = aesLinSpec.lin b := rfl

/-! ### The size of the state space -/

theorem card_gf256 : Fintype.card GF256 = 256 := by decide

theorem card_squareIdx4 : Fintype.card (SquareIdx 4) = 16 := by decide

/-- The AES state space has `2 ^ 128` elements, so a round-key vector for `r` rounds ranges
over `2 ^ (128 r)` values. That is the denominator every bound below is measured against. -/
theorem card_aesState : Fintype.card (SquareIdx 4 → GF256) = 2 ^ 128 := by
  rw [Fintype.card_fun, card_gf256, card_squareIdx4]
  norm_num

/-- `4 · 2⁶ = 256`: an S-box with differential uniformity `4` over a byte clears a factor
of `2⁻⁶` per active S-box. -/
theorem aes_uniformity_clears : 4 * 2 ^ 6 ≤ Fintype.card GF256 := by
  rw [card_gf256]
  norm_num

/-! ### The bounds

Each is `trailKeyCount_le_of_spec` at the AES constants and one round count. The active
S-box counts `25, 55, 75, 80` are Layer 1's, unchanged. -/

variable {s : SquareIdx 4 → GF256 → GF256}

/-- **Four rounds of AES: every differential trail has probability at most `2⁻¹⁵⁰`,
averaged over independent round keys.** `25` active S-boxes at `2⁻⁶` each. -/
theorem aes_four_round_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer s) 4 T x * 2 ^ 150
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 4 := by
  have h := trailKeyCount_le_of_spec aesLinSpec (d := 6) hs hu aes_uniformity_clears
    (fun b => aesLin_apply b) (r := 4) h0 x
  have he : 6 * (4 / 4 * aesLinSpec.fourRoundBound
      + (if 2 ≤ 4 % 4 then aesLinSpec.branch else 0)) = 150 := by
    rw [aesLinSpec_fourRoundBound, aesLinSpec_branch]
    decide
  rwa [he] at h

/-- **Ten rounds of AES-128: at most `2⁻³³⁰`.** `55` active S-boxes at `2⁻⁶` each, so the
sharpened count of Layer 1 buys five orders of `2⁶` over the usual `50`. -/
theorem aes128_ten_round_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer s) 10 T x * 2 ^ 330
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 10 := by
  have h := trailKeyCount_le_of_spec aesLinSpec (d := 6) hs hu aes_uniformity_clears
    (fun b => aesLin_apply b) (r := 10) h0 x
  have he : 6 * (10 / 4 * aesLinSpec.fourRoundBound
      + (if 2 ≤ 10 % 4 then aesLinSpec.branch else 0)) = 330 := by
    rw [aesLinSpec_fourRoundBound, aesLinSpec_branch]
    decide
  rwa [he] at h

/-- **Twelve rounds of AES-192: at most `2⁻⁴⁵⁰`.** -/
theorem aes192_twelve_round_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer s) 12 T x * 2 ^ 450
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 12 := by
  have h := trailKeyCount_le_of_spec aesLinSpec (d := 6) hs hu aes_uniformity_clears
    (fun b => aesLin_apply b) (r := 12) h0 x
  have he : 6 * (12 / 4 * aesLinSpec.fourRoundBound
      + (if 2 ≤ 12 % 4 then aesLinSpec.branch else 0)) = 450 := by
    rw [aesLinSpec_fourRoundBound, aesLinSpec_branch]
    decide
  rwa [he] at h

/-- **Fourteen rounds of AES-256: at most `2⁻⁴⁸⁰`.** -/
theorem aes256_fourteen_round_prob (hs : ∀ i, Function.Injective (s i))
    (hu : ∀ i, IsDiffUniform (s i) 4) {T : Nat → (SquareIdx 4 → GF256)} (h0 : T 0 ≠ 0)
    (x : SquareIdx 4 → GF256) :
    trailKeyCount aesLin (bricklayer s) 14 T x * 2 ^ 480
      ≤ Fintype.card (SquareIdx 4 → GF256) ^ 14 := by
  have h := trailKeyCount_le_of_spec aesLinSpec (d := 6) hs hu aes_uniformity_clears
    (fun b => aesLin_apply b) (r := 14) h0 x
  have he : 6 * (14 / 4 * aesLinSpec.fourRoundBound
      + (if 2 ≤ 14 % 4 then aesLinSpec.branch else 0)) = 480 := by
    rw [aesLinSpec_fourRoundBound, aesLinSpec_branch]
    decide
  rwa [he] at h
