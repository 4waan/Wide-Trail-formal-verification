/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.KoalaBearPrimality
import WideTrail.Poseidon2.Plonky3
import WideTrail.Algebra.PowerSbox
import WideTrail.Differential.PowerMap

/-!
# A certificate for SP1 v6.10.0 Poseidon2 over KoalaBear

SP1 `6.10.0` hashes with `SP1Perm = Poseidon2<KoalaBear, Poseidon2ExternalMatrixGeneral,
SP1DiffusionMatrix, 16, 3>` (`sp1-primitives` `6.10.0` `src/lib.rs:1145`), where
`SP1DiffusionMatrix = DiffusionMatrixKoalaBear` (`src/lib.rs:1139-1142`). The instance is
`poseidon2_init() = slop_koala_bear::my_kb_16_perm()` (`src/lib.rs:1133-1136`). This file
instantiates the generic model `WideTrail.Poseidon2.Plonky3` with that instance and discharges
every hypothesis of its theorems by `decide`.

## The pinned parameters

* **Field.** `F = ZMod modulus`, `modulus = 2130706433 = 0x7f000001 = 2^31 - 2^24 + 1`
  (`p3-koala-bear` `0.4.3-succinct` `src/koala_bear.rs:19`; `slop-koala-bear` `6.10.0` pins
  that version, `Cargo.toml:41-42`). Primality is the Lucas certificate of
  `KoalaBearPrimality.lean`, installed as a global `Fact` instance.
* **S-box.** `x ↦ x^3` on all `16` coordinates of a full round and on coordinate `0` of a
  partial round (`SP1Perm`'s parameters `16, 3`). `sbox` is `Sbox.powerEquivOfFermat` with
  inverse `x ↦ x^1420470955`, since `3 * 1420470955 = 2 (p - 1) + 1`; the code computes
  `x^{1/3}` with the same exponent (`p3-koala-bear` `src/koala_bear.rs:203`).
* **Rounds.** Four full rounds, `20` partial rounds, four full rounds (`ROUNDS_F = 8`,
  `ROUNDS_P = 20`, `slop-koala-bear` `src/koala_bear_poseidon2.rs:49-50`), preceded by the
  initial external layer (`p3-poseidon2` `0.4.3-succinct` `src/lib.rs:177-202`).
* **External layer.** `external` is `Plonky3.external`, i.e. `circ(2 M4, M4, M4, M4)` with
  `M4 = circ(2, 3, 1, 1)`; `external_eq_mdsLight` identifies it with the transcription of
  `mds_light_permutation` (`p3-poseidon2` `src/matrix.rs:110-139`, called at `:156`).
* **Internal layer.** `internal x i = R^{-1} (d_i x_i + ∑_j x_j)` with
  `d = (-2, 1, 2, 4, …, 2^13, 2^15)` and `R^{-1} = 1057030144`, the inverse of `R = 2^32`
  (`montyInverse_mul`). This is what `DiffusionMatrixKoalaBear` computes on Montgomery
  representatives (`p3-koala-bear` `src/poseidon2.rs:35-58`, `:95-113`), as described in the
  generic model; that reading is not derived in Lean, but the upstream known-answer test in
  `Checks/KoalaBear.lean` exercises it end to end. The same constant `1057030144` multiplies the
  internal layer of the gnark chip (`sp1-recursion-gnark-ffi` `6.10.0`
  `go/sp1/poseidon2/poseidon2_koalabear.go:135`).
* **Round constants.** `roundConstants` is the table `RC16` of `slop-koala-bear` `6.10.0`
  (`src/koala_bear_poseidon2.rs:96`), `28` rows of `16` hexadecimal strings, copied literally.
  The code reads each string with `KoalaBear::from_canonical_u64` (lines 11-15); every entry is
  below `p`, so the literal is the field element. `koala_bear_round_consts` (lines 69-87) takes
  rows `0-3` for the first full rounds, column `0` of rows `4-23` for the partial rounds and
  rows `24-27` for the last full rounds, and `my_kb_16_perm` (lines 48-63) concatenates the two
  full blocks. Columns `1-15` of rows `4-23` are zero (`partial_constants_zero`), so adding a
  whole row, as a HADES round does, adds the code's partial constant to `state[0]` only
  (`values_eq_roundValues`, `rounds_apply_partial`). The literal table was compared entry by
  entry with the crate source outside Lean. The table `RC_16_30` that still exists in
  `sp1-primitives` `6.10.0` (`src/lib.rs:45`) is not used by `poseidon2_init` and is not
  modelled.

## Results

* `permutation_bijective`; `permutation_bijective_general` for every round-constant table.
* `sbox_uniform`: the S-box has differential uniformity at most `2`.
* `external_isBranchBound`: the external layer has branch number at least `8`.
* `internal_inactive_trivial`: no nonzero difference stays inactive through `16` consecutive
  partial rounds. The proof is a Krylov certificate: the literal tables `krylov`
  (`u j = A^j e_0` for `A = diag d + J`) and `krylovInv` (a left inverse of the matrix with rows
  `u j`) were computed outside Lean, and `decide` checks the recurrence and the inverse. By
  `Plonky3.inactiveSpace_internal` the factor `R^{-1}` plays no role.
* `internal_inactive_trivial_by_criterion`, `inactive_trivial_by_criterion`: the same statement
  for the code's layer and for `diag d + J`, proved a second way with no table: the diagonal
  entries off coordinate `0` are pairwise distinct in `F` (`diag_injOn`, by `decide`), and
  `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff` applies. `finrank_inactive_eq`: exactly
  `16 - r` dimensions of differences stay inactive through `r ≤ 16` consecutive partial rounds.
* `activity`, `activity_general`: two distinct inputs incur at least `33` charged S-box
  applications, `32` in the full rounds and `20 / 16 = 1` in the partial rounds.
* `independent_key_probability`, `independent_key_probability_general`: for every nonzero
  trail `T`, `keyCount * 2^(29 * (32 + 20 / 16)) ≤ |F^16|^(8 + 20)`, and
  `probability_exponent` evaluates the exponent to `957`. Here `u = 2` (`sbox_uniform`) and
  `29` is the largest `dd` with `2 * 2^dd ≤ p` (`Checks/KoalaBear.lean` shows `30` fails).
* `independent_key_differential_exact`, `independent_key_differential_sharp`, and their
  `_general` forms for every round-constant table: in the same model, for every nonzero input
  difference `a`, every output difference `b` and every input `x`, the key count of the
  differential `(a, b)` over the `28` rounds that follow the initial external layer satisfies
  `diffKeyCount * p^7 ≤ 2^7 * |F^16|^28` and `diffKeyCount * 2^209 ≤ |F^16|^28`. Only `7` S-boxes
  of the first two full rounds are charged, one fewer than the branch number `8`, and `209` is
  the largest exponent this arithmetic gives (`differential_sharp_exponent_bound`;
  `Checks/KoalaBear.lean` shows `210` fails).

## What is not claimed

The activity counts are lower bounds on charged S-box applications for actual input pairs; they are
not claimed to be attained. The trail-probability statements concern one trail in the model with an
additional independent uniform key per round. The differential statements
(`independent_key_differential_*`) bound the key-averaged differential of the rounds after the
initial external layer, in the same model, and charge only `B - 1 = 7` S-boxes of the first two full
rounds. None of these is a statement about the permutation with its fixed constants, or about any
one key. Nothing is said about subspace-trail resistance beyond the inactive-space statements here,
about algebraic attacks, about the sponge, duplex and compression constructions built on the
permutation, or about equivalence with the Rust code, the AIR or the gnark circuit beyond the
transcriptions stated in `WideTrail.Poseidon2.Plonky3` and the round lemmas here. The model works
with field elements, not with the Montgomery representatives the code stores.
-/

set_option autoImplicit false

namespace Poseidon2.KoalaBear

/-! ### The field -/

/-- The KoalaBear prime `0x7f000001` (`p3-koala-bear` `0.4.3-succinct` `src/koala_bear.rs:19`). -/
def modulus : ℕ := 2130706433

theorem modulus_eq : modulus = 2 ^ 31 - 2 ^ 24 + 1 := by decide

instance : Fact (Nat.Prime modulus) := ⟨prime_2130706433⟩

abbrev F := ZMod modulus
abbrev State := Fin 16 → F

theorem field_card : Fintype.card F = modulus := ZMod.card modulus

theorem fermat (x : F) (hx : x ≠ 0) : x ^ (modulus - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rw [field_card] at h
  exact h

/-! ### The S-box -/

/-- The inverse exponent of the cube map: the code's `exp_1420470955`, used for `x^{1/3}`
(`p3-koala-bear` `0.4.3-succinct` `src/koala_bear.rs:203`). -/
def inverseExponent : ℕ := 1420470955

theorem inverseExponent_positive : 0 < inverseExponent := by decide

theorem inverseExponent_equation : 3 * inverseExponent = (modulus - 1) * 2 + 1 := by decide

theorem three_positive : 0 < (3 : ℕ) := by decide

/-- The S-box `x ↦ x^3` (`SP1Perm`'s degree `3`, `sp1-primitives` `6.10.0` `src/lib.rs:1145`),
with inverse `x ↦ x^1420470955`. -/
def sbox : F ≃ F := Sbox.powerEquivOfFermat modulus 3 inverseExponent 2
  three_positive inverseExponent_positive inverseExponent_equation fermat

theorem sbox_toFun : (sbox : F → F) = fun x => x ^ 3 := rfl

theorem sbox_symm_toFun : (sbox.symm : F → F) = fun x => x ^ inverseExponent := rfl

theorem three_ne_zero : (3 : F) ≠ 0 := by decide

/-- The cube S-box has differential uniformity at most `2` (`Sbox.pow_three_uniform`). -/
theorem sbox_uniform : IsDiffUniform sbox 2 := by
  rw [sbox_toFun]
  exact Sbox.pow_three_uniform three_ne_zero

/-! ### The linear layers -/

/-- `R^{-1}` for `R = 2^32`: the canonical value of the code's `MONTY_INVERSE`, the element with
Montgomery representative `1` (`p3-koala-bear` `0.4.3-succinct` `src/poseidon2.rs:35`), and the
constant `montyInverse` of the gnark chip (`sp1-recursion-gnark-ffi` `6.10.0`
`go/sp1/poseidon2/poseidon2_koalabear.go:135`). -/
def montyInverse : F := 1057030144

theorem montyInverse_mul : montyInverse * 2 ^ 32 = 1 := by decide

/-- The four field conditions of the generic model, each closed by `decide`: `35 ≠ 0`,
`2 ≠ 0`, the Sherman–Morrison condition `81917 ≠ 0`, and `R^{-1} ≠ 0`. -/
theorem conditions : Plonky3.Conditions montyInverse :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The primes `2, 3, 5, 7, 11, 17` of the `M4` minors are nonzero in `F`. -/
theorem m4Primes_ne_zero : ∀ q ∈ m4Primes, (q : F) ≠ 0 := by decide

/-- The external layer `circ(2 M4, M4, M4, M4)`, `M4 = circ(2, 3, 1, 1)`. -/
def external : State ≃ₗ[F] State := Plonky3.external conditions.thirtyFive

/-- The external layer is the code's `mds_light_permutation` (`p3-poseidon2` `0.4.3-succinct`
`src/matrix.rs:110-139`). -/
theorem external_eq_mdsLight (x : State) : external x = Plonky3.mdsLight x :=
  Plonky3.external_eq_mdsLight conditions.thirtyFive x

/-- **Branch number `8`** for the external layer. -/
theorem external_isBranchBound : isBranchBound id external 8 :=
  Plonky3.external_isBranchBound m4Primes_ne_zero conditions.thirtyFive

/-- The internal layer `x ↦ R^{-1} (diag d + J) x` with the SP1 diagonal
`d = (-2, 1, 2, 4, …, 2^13, 2^15)` (`p3-koala-bear` `0.4.3-succinct` `src/poseidon2.rs:37-58`,
`:95-113`). -/
def internal : State ≃ₗ[F] State :=
  Plonky3.internal montyInverse conditions.scale conditions.two conditions.shermanMorrison

theorem internal_apply (x : State) (i : Fin 16) :
    internal x i = montyInverse * (Plonky3.sp1Diag F i * x i + ∑ j, x j) :=
  rfl

/-- The Sherman–Morrison quantity `1 + ∑ 1/d_i` is nonzero in `F`. -/
theorem one_add_sum_inv_ne_zero : 1 + ∑ i, (Plonky3.sp1Diag F i)⁻¹ ≠ 0 :=
  (Plonky3.one_add_sum_inv_ne_zero_iff conditions.two).mpr conditions.shermanMorrison

/-! ### Round constants -/

/-- `RC16` of `slop-koala-bear` `6.10.0` (`src/koala_bear_poseidon2.rs:96`), row by row, with the
hexadecimal strings of the source as literals. Rows `0-3` and `24-27` are the full-round
constants; column `0` of rows `4-23` holds the partial-round constants and the other columns of
those rows are zero. -/
def roundConstants : Fin 28 → State :=
  ![![0x7ee56a48, 0x11367045, 0x12e41941, 0x7ebbc12b, 0x1970b7d5, 0x662b60e8, 0x3e4990c6,
      0x679f91f5, 0x350813bb, 0x00874ad4, 0x28a0081a, 0x18fa5872, 0x5f25b071, 0x5e5d5998,
      0x5e6fd3e7, 0x5b2e2660],
    ![0x6f1837bf, 0x3fe6182b, 0x1edd7ac5, 0x57470d00, 0x43d486d5, 0x1982c70f, 0x0ea53af9,
      0x61d6165b, 0x51639c00, 0x2dec352c, 0x2950e531, 0x2d2cb947, 0x08256cef, 0x1a0109f6,
      0x1f51faf3, 0x5cef1c62],
    ![0x3d65e50e, 0x33d91626, 0x133d5a1e, 0x0ff49b0d, 0x38900cd1, 0x2c22cc3f, 0x28852bb2,
      0x06c65a02, 0x7b2cf7bc, 0x68016e1a, 0x15e16bc0, 0x5248149a, 0x6dd212a0, 0x18d6830a,
      0x5001be82, 0x64dac34e],
    ![0x5902b287, 0x426583a0, 0x0c921632, 0x3fe028a5, 0x245f8e49, 0x43bb297e, 0x7873dbd9,
      0x3cc987df, 0x286bb4ce, 0x640a8dcd, 0x512a8e36, 0x03a4cf55, 0x481837a2, 0x03d6da84,
      0x73726ac7, 0x760e7fdf],
    ![0x54dfeb5d, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x7d40afd6, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x722cb316, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x106a4573, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x45a7ccdb, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x44061375, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x154077a5, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x45744faa, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x4eb5e5ee, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x3794e83f, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x47c7093c, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x5694903c, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x69cb6299, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x373df84c, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x46a0df58, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x46b8758a, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x3241ebcb, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x0b09d233, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x1af42357, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x1e66cec2, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
      0x00000000, 0x00000000],
    ![0x43e7dc24, 0x259a5d61, 0x27e85a3b, 0x1b9133fa, 0x343e5628, 0x485cd4c2, 0x16e269f5,
      0x165b60c6, 0x25f683d9, 0x124f81f9, 0x174331f9, 0x77344dc5, 0x5a821dba, 0x5fc4177f,
      0x54153bf5, 0x5e3f1194],
    ![0x3bdbf191, 0x088c84a3, 0x68256c9b, 0x3c90bbc6, 0x6846166a, 0x03f4238d, 0x463335fb,
      0x5e3d3551, 0x6e59ae6f, 0x32d06cc0, 0x596293f3, 0x6c87edb2, 0x08fc60b5, 0x34bcca80,
      0x24f007f3, 0x62731c6f],
    ![0x1e1db6c6, 0x0ca409bb, 0x585c1e78, 0x56e94edc, 0x16d22734, 0x18e11467, 0x7b2c3730,
      0x770075e4, 0x35d1b18c, 0x22be3db5, 0x4fb1fbb7, 0x477cb3ed, 0x7d5311c6, 0x5b62ae7d,
      0x559c5fa8, 0x77f15048],
    ![0x3211570b, 0x490fef6a, 0x77ec311f, 0x2247171b, 0x4e0ac711, 0x2edf69c9, 0x3b5a8850,
      0x65809421, 0x5619b4aa, 0x362019a7, 0x6bf9d4ed, 0x5b413dff, 0x617e181e, 0x5e7ab57b,
      0x33ad7833, 0x3466c7ca]]

/-- The constant table indexed by round, zero past round `27`. -/
def values (n : ℕ) : State := if h : n < 28 then roundConstants ⟨n, h⟩ else 0

/-- Partial rows add their constant only at the S-box coordinate. -/
theorem partial_constants_zero :
    ∀ n : Fin 20, ∀ i : Fin 16, i ≠ 0 → values (4 + n.val) i = 0 := by
  decide

theorem partialRowsAtZero : Plonky3.PartialRowsAtZero 20 values :=
  fun j hj i hi => partial_constants_zero ⟨j, hj⟩ i hi

/-- The code's `external_round_constants`: `KoalaBear_BEGIN_EXT_CONSTS` (rows `0-3`) followed
by `KoalaBear_END_EXT_CONSTS` (rows `24-27`) (`slop-koala-bear` `6.10.0`
`src/koala_bear_poseidon2.rs:51-53`, `:69-87`). -/
def externalConstants (r : Fin 8) : State :=
  if h : r.val < 4 then roundConstants ⟨r.val, by omega⟩
  else roundConstants ⟨r.val + 20, by omega⟩

/-- The code's `KoalaBear_PARTIAL_CONSTS`: column `0` of rows `4-23` (`slop-koala-bear`
`6.10.0` `src/koala_bear_poseidon2.rs:80-81`). -/
def internalConstants (j : Fin 20) : F := roundConstants ⟨j.val + 4, by omega⟩ 0

theorem values_eq_roundValues_lt : ∀ n : Fin 28, ∀ i : Fin 16,
    values n.val i = Plonky3.roundValues 20 externalConstants internalConstants n.val i := by
  decide

/-- **The table is the code's two arrays.** `values` is the table that
`Plonky3.roundValues` builds from `external_round_constants` and `internal_round_constants`. -/
theorem values_eq_roundValues :
    values = Plonky3.roundValues 20 externalConstants internalConstants := by
  funext n i
  by_cases hn : n < 28
  · exact values_eq_roundValues_lt ⟨n, hn⟩ i
  · simp [values, Plonky3.roundValues, hn, show ¬n < 4 by omega, show ¬n < 4 + 20 by omega]

/-! ### The permutation -/

/-- The `28` rounds: four full, twenty partial with the S-box on coordinate `0`, four full. -/
def rounds : ℕ → Hades.RoundSpec (Fin 16) F := Plonky3.rounds conditions 20 sbox values

/-- **The permutation**, the model of `my_kb_16_perm`: the initial external layer, then the
`28` rounds. -/
def permutation (x : State) : State := Plonky3.permutation conditions 20 sbox values x

theorem permutation_eq (x : State) : permutation x = Hades.execute rounds (external x) 28 :=
  rfl

theorem permutation_bijective : Function.Bijective permutation :=
  Plonky3.permutation_bijective conditions 20 sbox values

/-- Bijectivity holds for every round-constant table. -/
theorem permutation_bijective_general (table : ℕ → State) :
    Function.Bijective (Plonky3.permutation conditions 20 sbox table) :=
  Plonky3.permutation_bijective conditions 20 sbox table

/-- A first-half full round is the code's round (`p3-poseidon2` `0.4.3-succinct`
`src/lib.rs:183-187`) with `external_constants[j]`. -/
theorem rounds_apply_prefix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds j).apply x =
      external (fun i => sbox (x i + externalConstants ⟨j, by omega⟩ i)) := by
  rw [rounds, Plonky3.rounds_apply_prefix conditions 20 sbox values hj x, values_eq_roundValues,
    Plonky3.roundValues_prefix 20 _ _ hj]
  rfl

/-- **A partial round is the code's round** (`p3-poseidon2` `0.4.3-succinct`
`src/lib.rs:190-194`): add `internal_constants[j]` to `state[0]`, apply the S-box to `state[0]`
only, then the internal layer. -/
theorem rounds_apply_partial {j : ℕ} (hj : j < 20) (x : State) :
    (rounds (4 + j)).apply x =
      internal (Function.update x 0 (sbox (x 0 + internalConstants ⟨j, hj⟩))) := by
  rw [rounds, values_eq_roundValues]
  exact Plonky3.rounds_roundValues_apply_middle conditions 20 sbox _ _ hj x

/-- A second-half full round is the code's round (`p3-poseidon2` `0.4.3-succinct`
`src/lib.rs:197-201`) with `external_constants[4 + j]`. -/
theorem rounds_apply_suffix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds (24 + j)).apply x =
      external (fun i => sbox (x i + externalConstants ⟨4 + j, by omega⟩ i)) := by
  rw [show 24 + j = 4 + 20 + j by omega, rounds,
    Plonky3.rounds_apply_suffix conditions 20 sbox values hj x, values_eq_roundValues,
    Plonky3.roundValues_suffix 20 _ _ hj]
  rfl

/-! ### The Krylov certificate for the partial rounds -/

/-- Rows `u j = A^j e_0`, `j < 16`, for `A = diag d + J` over `F`, computed outside Lean. -/
def krylov : Fin 16 → State :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2130706432, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![16, 15, 16, 18, 22, 30, 46, 78, 142, 270, 526, 1038, 2062, 4110, 8206, 32782],
    ![49345, 49392, 49409, 49449, 49553, 49857, 50849, 54369, 67553, 118497, 318689, 1112289,
      4272353, 16883937, 67272929, 1074249953],
    ![1164599733, 1164747815, 1164797241, 1164896219, 1165094847, 1165496135, 1166325591,
      1168178039, 1173345207, 1195033655, 1327867191, 172975926, 1391651635, 7992086, 411566644,
      786178734],
    ![677308634, 2040549482, 1074689716, 1273973677, 1673734711, 347381930, 1976211218, 1064471008,
      1914537853, 2113397428, 1048451332, 1154515952, 93142793, 1650789428, 1652172309, 9075976],
    ![1364134715, 497888599, 606718549, 1422527392, 1193684640, 1884743564, 2036317969, 531584206,
      617650939, 418353136, 457106418, 270310083, 1711613077, 1490030729, 936338462, 1821432931],
    ![1747927381, 712672544, 1428221043, 1643480647, 1241435333, 540790907, 1455765963, 144870201,
      437966116, 777865111, 2006268764, 20472647, 586283356, 1037425817, 156305849, 1711172190],
    ![1499536942, 1446651382, 1459714491, 915782127, 11929337, 863807618, 442948128, 1482845970,
      1395274428, 1711748985, 943085300, 390905036, 1854570147, 1401497868, 636927613, 753809930],
    ![1427722820, 1612035220, 954106387, 1697805913, 260818534, 1202067128, 1555485336, 1316442866,
      1911876683, 1578305233, 1485403580, 2010037731, 1406181288, 577520664, 1907041550,
      1860198742],
    ![731246138, 937314132, 1233491686, 1855089698, 1411827184, 1512701496, 94561705, 480071449,
      1144960974, 667902723, 1320421724, 1472207611, 600165753, 1896484459, 1600796189, 1198727937],
    ![1780533551, 2049633526, 1448596333, 9852454, 1753404701, 1877772567, 2007587521, 2007002068,
      648580189, 1638901842, 1734302821, 112758494, 834169697, 557008740, 336604567, 1456266655],
    ![1776963593, 995544922, 1843104062, 1116027645, 188910406, 1291088839, 1398225511, 1682364201,
      997331134, 886322080, 535079620, 1483168303, 629598019, 597827126, 1407106391, 721095401],
    ![1211591469, 1499650711, 2059607480, 706803503, 2015389037, 1985169316, 502487048, 1640093003,
      320104961, 1547676371, 1734447805, 74761332, 843456736, 1022322368, 397858331, 1954570220],
    ![47155289, 1839282505, 197433888, 1036139373, 1547799059, 141744355, 1504272299, 900968769,
      829644575, 233386232, 2003031826, 189804174, 1866816392, 933910277, 1744943289, 791931207],
    ![799007900, 601894550, 1288186254, 776463104, 491472352, 1030521725, 23784087, 1026246003,
      552502428, 980413746, 1575819117, 1358507251, 1645948492, 1571765835, 559282969, 1021461947]]

/-- A left inverse of the matrix with rows `krylov j`, computed outside Lean. -/
def krylovInv : Fin 16 → Fin 16 → F :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![971831887, 1467370403, 1707388605, 1803550303, 161817057, 636840070, 1540314584, 1090527965,
      2129708238, 966580946, 160157714, 1255977925, 2074529752, 1600207920, 1886590091, 1317589722],
    ![1202845848, 230168417, 1447470575, 1711565377, 63505930, 1444093690, 848920230, 1934903214,
      1112139569, 1230710250, 1591535735, 1430124617, 572543184, 1081097941, 1997512306,
      1127396612],
    ![1555872419, 1904692269, 1394095573, 1007509220, 754872690, 1982685408, 1297586963, 807760145,
      1094415619, 925748578, 497128373, 1711489545, 1233525055, 790873788, 1503238274, 1070761984],
    ![2072433101, 1572866738, 765543168, 1521082794, 303602509, 1851882667, 1604805578, 1836047688,
      1774485760, 631375143, 1805299795, 6216880, 1810584665, 704593998, 709633967, 1881155269],
    ![1610653609, 1020400669, 1793240898, 300385158, 691135432, 799149190, 1251426984, 1179108996,
      1524331761, 415649027, 1981475904, 782757462, 1066969504, 1285805490, 380209332, 739230216],
    ![373828513, 1908264526, 1918732597, 1815192754, 2036792385, 1617915365, 1392572151, 993902365,
      2022546644, 1956092758, 137260209, 1478003804, 866017025, 1016815444, 182225825, 232481936],
    ![337333617, 2080692829, 403146810, 2045121800, 1587864743, 963009091, 1091698240, 935528099,
      1343020415, 1001862951, 1173787530, 1092844011, 1968835608, 788334971, 2008501647, 185079431],
    ![737720128, 949077855, 1107645305, 1665758916, 251150753, 64388563, 975668009, 173030453,
      1761761842, 254504337, 671713548, 909017895, 324148339, 1115072193, 839131615, 1734633503],
    ![1179932652, 1440319449, 666518921, 1142661107, 352196238, 1390334218, 292913189, 933646707,
      1713004571, 193439204, 2077569260, 243045207, 861034732, 534402050, 1284293350, 2042025988],
    ![177102598, 1410771681, 957710865, 382567300, 503262820, 731927467, 1962645153, 744136411,
      282947733, 1671370965, 573654854, 1631712154, 780243364, 2017021071, 126341295, 381705361],
    ![1763648709, 1746095436, 1952733830, 61696382, 2109254313, 328679627, 615559504, 432824550,
      936717248, 1441186945, 1341692288, 1951715963, 1220052833, 379505292, 1788931471, 1142482851],
    ![1845057722, 1714302753, 1790216758, 1518752399, 1012540878, 401539618, 1671896371, 1723296793,
      175931818, 1436806927, 421945978, 126914208, 344983837, 254174625, 316822275, 543195213],
    ![2055288507, 1113810677, 234187463, 848170013, 204716939, 669303635, 2083700425, 6976691,
      155416353, 1267574570, 770543982, 2042369678, 2125912588, 676111819, 963953162, 629465757],
    ![1532114498, 794524945, 1102390247, 1018252097, 901277263, 185475257, 1241503409, 697944674,
      268869290, 1119822450, 1188557487, 2056859735, 1024661862, 126827010, 203263098, 2027476122],
    ![1760694090, 1953705684, 1935336282, 203385844, 1850248648, 1847721165, 1305147107, 1425310280,
      750354603, 402219980, 522622374, 326602380, 771609116, 413394986, 724297323, 1990971499]]

theorem krylov_zero : ∀ j : Fin 16, (j : ℕ) = 0 → krylov j = Pi.single 0 1 := by
  decide

theorem krylov_succ : ∀ j k : Fin 16, (k : ℕ) = j + 1 →
    krylov k = fun i => Plonky3.sp1Diag F i * krylov j i + ∑ m, krylov j m := by
  decide

theorem krylovInv_mul : ∀ i k : Fin 16,
    ∑ j, krylovInv i j * krylov j k = if i = k then 1 else 0 := by
  decide

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds**, for
the unscaled layer `diag d + J`. -/
theorem inactive_trivial :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (Plonky3.sp1Diag F)) ({0} : Finset (Fin 16)) 16 =
      ⊥ :=
  Hades.inactiveSpace_diagPlusOnes_eq_bot one_ne_zero (Plonky3.sp1Diag F) 0 16 krylov
    krylov_zero krylov_succ krylovInv krylovInv_mul

/-- **The same for the code's internal layer**, with its factor `R^{-1}`. -/
theorem internal_inactive_trivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 16 = ⊥ := by
  rw [internal, Plonky3.inactiveSpace_internal]
  exact inactive_trivial

/-! ### Activity -/

/-- **Thirty-three active S-boxes, for every round-constant table.** Two distinct inputs incur
at least `33` charged S-box applications over the `28` rounds: `32` in the full rounds and
`20 / 16 = 1` in the partial rounds. A lower bound; it is not claimed to be attained. -/
theorem activity_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    33 ≤ Hades.scheduledWeight (Plonky3.rounds conditions 20 sbox table)
      (Hades.differenceTrace (Plonky3.rounds conditions 20 sbox table) (external x) (external y))
      0 28 :=
  Plonky3.activity_with_middle conditions m4Primes_ne_zero 20 sbox table inactive_trivial hxy

/-- **Thirty-three active S-boxes** for the pinned permutation. -/
theorem activity {x y : State} (hxy : x ≠ y) :
    33 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 28 :=
  activity_general values hxy

/-! ### The independent-key trail bound -/

/-- `u * 2^dd ≤ |F|` for `u = 2`, `dd = 29`. -/
theorem two_mul_two_pow_le_card : 2 * 2 ^ 29 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- **Trail bound, for every round-constant table.** In the model with an additional
independent uniform key per round, the number of keys realising a fixed nonzero trail `T`, times
`2^(29 * (32 + 20 / 16))`, is at most the number of all key sequences. This concerns one trail in
that model only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.rounds conditions 20 sbox table) (8 + 20) T x *
        2 ^ (29 * (32 + 20 / 16))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Plonky3.independent_key_probability_with_middle conditions m4Primes_ne_zero 20 sbox table
    sbox_uniform two_mul_two_pow_le_card inactive_trivial h0 x

/-- **Trail bound for the pinned rounds**, in the same model. The exponent keeps its round
arithmetic; `probability_exponent` evaluates it. -/
theorem independent_key_probability {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * 2 ^ (29 * (32 + 20 / 16))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_general values h0 x

/-- The displayed bound's concrete exponent. -/
theorem probability_exponent : 29 * (32 + 20 / 16) = 957 := by
  decide

end Poseidon2.KoalaBear

/-! ### The exact ratio and the sharp exponent

`independent_key_probability` charges `29` bits per charged S-box, the largest `dd` with
`2 * 2^dd ≤ p`, so `957` bits over the `33` charged S-boxes. Keeping the ratio `p / 2` exact
(`independent_key_probability_exact`) gives `989` bits (`independent_key_probability_sharp`),
since `33 * log2 (p / 2) ≈ 989.6`. The `_general` forms state the same for every round-constant
table. The sample space is the same: one trail, an additional independent uniform key per
round. -/

namespace Poseidon2.KoalaBear

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^(32 + 20 / 16) = p^33` (`p = modulus`), is at most `2^33` times
the number of all key sequences. Here `u = 2` (`sbox_uniform`), and the `33` charged S-boxes are
counted as in `activity_general`. This concerns one trail in that model only: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.rounds conditions 20 sbox table) (8 + 20) T x
        * modulus ^ (32 + 20 / 16)
      ≤ 2 ^ (32 + 20 / 16) * Fintype.card (Fin 16 → F) ^ (8 + 20) := by
  have h := Plonky3.independent_key_probability_with_middle_exact conditions m4Primes_ne_zero
    20 sbox table sbox_uniform inactive_trivial h0 x
  rw [field_card] at h
  exact h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the model with an additional
independent uniform key per round: for every nonzero trail `T`, the number of key sequences
realising `T`, times `p^(32 + 20 / 16) = p^33` (`p = modulus`), is at most `2^33` times the
number of all key sequences. Here `u = 2` (`sbox_uniform`), and the `33` charged S-boxes are
counted as in `activity`. This concerns one trail in that model only: not the permutation with
its fixed constants, and not a differential. -/
theorem independent_key_probability_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * modulus ^ (32 + 20 / 16)
      ≤ 2 ^ (32 + 20 / 16) * Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_exact_general values h0 x

set_option exponentiation.threshold 1000 in
/-- `2^989 * 2^33 ≤ p^33`, by `decide`. `Checks/KoalaBear.lean` shows that `2^990 * 2^33 ≤ p^33`
fails, so `989` is the largest such exponent. -/
theorem sharp_exponent_bound : 2 ^ 989 * 2 ^ (32 + 20 / 16) ≤ modulus ^ (32 + 20 / 16) := by
  decide

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^989`, is at
most the number of all key sequences. It follows from
`independent_key_probability_exact_general` and `sharp_exponent_bound`, and `989` is the largest
exponent that this arithmetic gives. This concerns one trail in that model only: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.rounds conditions 20 sbox table) (8 + 20) T x * 2 ^ 989
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Hades.mul_le_of_ratio (independent_key_probability_exact_general table h0 x)
    sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model: for every
nonzero trail `T`, the number of key sequences realising `T`, times `2^989`, is at most the
number of all key sequences. It follows from `independent_key_probability_exact` and
`sharp_exponent_bound`, and `989` is the largest exponent that this arithmetic gives. This
concerns one trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 20) T x * 2 ^ 989 ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_sharp_general values h0 x

end Poseidon2.KoalaBear

/-! ### Exact inactive dimensions through the diagonal criterion

`internal_inactive_trivial` is proved by a Krylov certificate: the literal tables `krylov` and
`krylovInv`, computed outside Lean and checked by `decide`. The results below are a second,
general route to the same statement. The fifteen diagonal entries off coordinate `0`, namely
`1, 2, 4, …, 2^13, 2^15`, are pairwise distinct in `F` (`diag_injOn`, by `decide`), so the
criterion `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff` applies with no table
(`inactive_trivial_by_criterion`, `internal_inactive_trivial_by_criterion`), and the space of
differences that stay inactive through `r ≤ 16` consecutive partial rounds has dimension exactly
`16 - r` (`finrank_inactive_eq`).

These are statements about inactive differences of the partial rounds only: they are the
linear-algebra fact behind "at most `15` consecutive partial rounds can be linearized", not a
proof of resistance to subspace trails in general, and they say nothing about the full
rounds. -/

namespace Poseidon2.KoalaBear

/-- The diagonal entries `d 1, …, d 15` are pairwise distinct in `F`, by `decide`. -/
theorem diag_injOn : Set.InjOn (Plonky3.sp1Diag F) {i | i ≠ 0} :=
  Plonky3.injOn_sp1Diag_of_forall (by decide)

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds**, for
the unscaled layer `diag d + J`: the statement of `inactive_trivial`, proved by the diagonal
criterion instead of the Krylov certificate. -/
theorem inactive_trivial_by_criterion :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (Plonky3.sp1Diag F)) ({0} : Finset (Fin 16)) 16 =
      ⊥ :=
  Plonky3.inactiveSpace_sixteen_eq_bot_iff.mpr diag_injOn

/-- **The same for the code's internal layer**: the statement of `internal_inactive_trivial`,
proved by the diagonal criterion instead of the Krylov certificate. -/
theorem internal_inactive_trivial_by_criterion :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Plonky3.inactiveSpace_internal_sixteen_eq_bot _ _ _ _ diag_injOn

/-- **Exactly `16 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds**, for `r ≤ 16`. For `r = 15` one dimension remains; for `r = 16` none. -/
theorem finrank_inactive_eq {r : ℕ} (hr : r ≤ 16) :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) r) =
      16 - r :=
  Plonky3.finrank_inactiveSpace_internal_eq _ _ _ _ diag_injOn hr

end Poseidon2.KoalaBear

/-! ### The independent-key differential bound

The trail bounds above concern one trail. `independent_key_differential_exact` bounds a
differential, the sum over all trails from a nonzero input difference `a` to an output difference
`b`, in the same model with an additional independent uniform key per round
(`Plonky3.independent_key_differential_exact`). It charges `7` S-boxes of the first two full
rounds, one fewer than the branch number `8`, at the ratio `p / 2` each; the other rounds are not
charged. Since `7 * log2 (p / 2) ≈ 209.9`, the sharp exponent is `209`
(`independent_key_differential_sharp`). The `_general` forms state the same for every
round-constant table. Nothing here concerns the permutation with its fixed constants. -/

namespace Poseidon2.KoalaBear

/-- **Differential bound as an exact ratio, for every round-constant table**, in the model with
an additional independent uniform key per round: for every nonzero input difference `a`, every
output difference `b` and every input `x`, the number of key sequences under which `(x, x + a)`
has output difference `b` after the `28` rounds, times `p^7` (`p = modulus`), is at most `2^7`
times the number of all key sequences. Here `u = 2` (`sbox_uniform`). This concerns the
key-averaged differential only: not the permutation with its fixed constants, and not any one
key. -/
theorem independent_key_differential_exact_general (table : ℕ → State) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.rounds conditions 20 sbox table) (8 + 20) a b x * modulus ^ 7
      ≤ 2 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 20) := by
  have h := Plonky3.independent_key_differential_exact conditions m4Primes_ne_zero 20 sbox table
    sbox_uniform ha b x
  rw [field_card] at h
  exact h

/-- **Differential bound as an exact ratio** for the pinned rounds, in the same model: for every
nonzero input difference `a`, the key count of the differential `(a, b)` times `p^7` is at most
`2^7` times the number of all key sequences. This concerns the key-averaged differential only:
not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_exact {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 20) a b x * modulus ^ 7
      ≤ 2 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_differential_exact_general values ha b x

/-- `2^209 * 2^7 ≤ p^7`, by `decide`. `Checks/KoalaBear.lean` shows that `2^210 * 2^7 ≤ p^7`
fails, so `209` is the largest such exponent. -/
theorem differential_sharp_exponent_bound : 2 ^ 209 * 2 ^ 7 ≤ modulus ^ 7 := by
  decide

/-- **Differential bound with the sharp exponent, for every round-constant table**, in the same
model: for every nonzero input difference `a`, the key count of the differential `(a, b)`, times
`2^209`, is at most the number of all key sequences. It follows from
`independent_key_differential_exact_general` and `differential_sharp_exponent_bound`, and `209` is
the largest exponent that this arithmetic gives. This concerns the key-averaged differential
only: not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_sharp_general (table : ℕ → State) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.rounds conditions 20 sbox table) (8 + 20) a b x * 2 ^ 209
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  Hades.mul_le_of_ratio (independent_key_differential_exact_general table ha b x)
    differential_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Differential bound with the sharp exponent** for the pinned rounds, in the same model: for
every nonzero input difference `a`, the key count of the differential `(a, b)`, times `2^209`, is
at most the number of all key sequences. This concerns the key-averaged differential only: not
the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_sharp {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 20) a b x * 2 ^ 209 ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_differential_sharp_general values ha b x

end Poseidon2.KoalaBear
