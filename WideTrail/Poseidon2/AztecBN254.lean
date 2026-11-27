/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BN254
import WideTrail.Poseidon2.HorizenLabsM4
import WideTrail.Algebra.DiagPlusOnes
import WideTrail.Hades.Subspace
import WideTrail.Hades.Dimension
import WideTrail.Hades.Hull

/-!
# A certificate for the Aztec and Noir Poseidon2 permutation over BN254, width four

Below, `AZ1` is AztecProtocol/aztec-packages tag `v1.0.0` (commit
`79e9bd1698f4bba6deade8f76c676f9bbb12ff74`), `AZ6` is its tag `v6.1.0` (commit
`6595672787600ce14bb6dd0dd612b2ae6219b061`), and `NR1` is noir-lang/noir tag `v1.0.0` (commit
`275d3ab1a5c916c6ea73e8d6b943f685f574500c`). `BB/` abbreviates the barretenberg directory
`barretenberg/cpp/src/barretenberg/`, `P2/` abbreviates `BB/crypto/poseidon2/`, and `NS/` the
Noir directory `acvm-repo/bn254_blackbox_solver/src/`.

## Who deploys it

* **Aztec (barretenberg).** `Poseidon2Permutation<Poseidon2Bn254ScalarFieldParams>`
  (AZ1 `P2/poseidon2_permutation.hpp:25-169`, parameters `P2/poseidon2_params.hpp:16-457`). The
  sponge hash `Poseidon2` (`P2/poseidon2.hpp:15-31`), the WASM export `poseidon2_permutation`
  (`P2/c_bind.cpp:39-41`), the world-state Merkle trees
  (`BB/crypto/merkle_tree/hash.hpp:28-32`) and the in-circuit gadget
  (`BB/stdlib/hash/poseidon2/poseidon2_permutation.cpp:229-230`)
  are instantiated with these parameters. AZ6 has the same constants and the same loop,
  refactored (`permutation_inplace`, AZ6 `P2/poseidon2_permutation.hpp:131-158`); it renames
  the diagonal `internal_matrix_diagonal_minus_one` (AZ6 `P2/poseidon2_params.hpp:24-31`).
* **Noir.** The ACVM black-box solver `poseidon2_permutation` (NR1 `NS/poseidon2.rs:8-13`,
  `:81-122`, configuration `NS/poseidon2_constants.rs:36-449`), reached from
  `std::hash::poseidon2_permutation` (NR1 `noir_stdlib/src/hash/mod.nr:340-349`, state size `4`
  for BN254 by its documentation `:326-327`). The Aztec protocol circuits hash through it (AZ1
  `noir-projects/noir-protocol-circuits/crates/types/src/hash.nr:233-235`, `:384`).

The `256` round constants and the `4` diagonal entries are identical in AZ1, AZ6, NR1 and noir
tag `nightly-2025-06-19`, the Noir that AZ1 vendors (compared outside Lean).

## The pinned parameters

* **Field.** `F = Poseidon2.BN254.F = ZMod modulus`, the BN254 scalar field
  `p = 21888242871839275222246405745257275088548364400416034343698204186575808495617`
  (AZ1 `BB/ecc/curves/bn254/fr.hpp:26-29`), with the primality
  certificate of `WideTrail.Poseidon2.BN254Primality`. Field elements are canonical values; the
  Montgomery form of barretenberg is a representation of the same element.
* **S-box.** `x ↦ x^5` (AZ1 `P2/poseidon2_params.hpp:20`, computed as `x * (x^2)^2` at
  `P2/poseidon2_permutation.hpp:115-121`; NR1 `NS/poseidon2.rs:28-31`), the S-box
  `Poseidon2.BN254.sbox` of the width-three certificate.
* **Rounds.** The initial external layer, four full rounds, `56` partial rounds with the S-box on
  coordinate `0`, four full rounds (AZ1 `P2/poseidon2_params.hpp:19-22`,
  `P2/poseidon2_permutation.hpp:137-168`; NR1 `NS/poseidon2.rs:81-122`). Each round adds its
  constants, applies the S-box layer, then the linear layer.
* **External layer.** `external` is `hlMat4 = [[5, 7, 1, 3], [4, 6, 1, 1], [1, 3, 5, 7],
  [1, 1, 4, 6]]`, row `i` giving output `i` (AZ1 `P2/poseidon2_permutation.hpp:52-83`; NR1
  `NS/poseidon2.rs:48-68`), as a linear equivalence with the explicit inverse
  `y ↦ 8⁻¹ • hlMat4Inv8 y` (`external_symm_apply`). The addition chain of the code is
  transcribed in `WideTrail.Poseidon2.AztecBN254Execution` and proved to compute these rows.
* **Internal layer.** `internal x i = d_i x_i + ∑_j x_j`, i.e. `diag(d) + J`
  (AZ1 `P2/poseidon2_permutation.hpp:92-103`; NR1 `NS/poseidon2.rs:70-79`). The stored array is
  `d` itself (`internalDiag`): the true diagonal entries of the matrix are `d_i + 1`. There is no
  scale factor.
* **Round constants.** `roundConstants`, the `64 × 4` table of AZ1
  `P2/poseidon2_params.hpp:58-443` (NR1 `NS/poseidon2_constants.rs:61-449`), copied literally.
  The code adds `round_constants[r][0]` to `state[0]` only in a partial round (AZ1
  `P2/poseidon2_permutation.hpp:156`); the table is zero off coordinate `0` in those rows
  (`partial_constants_zero`), so the HADES round, which adds the whole row, is the code's round
  (`rounds_apply_partial`).

## Results

* `external_mds`, `external_branch`: `hlMat4` is MDS over `F`, so the external layer has branch
  number at least `5`. `internalDiag_ne_zero`, `one_add_sum_inv_ne_zero`,
  `internalDiag_injOn`: every diagonal entry is nonzero, the Sherman–Morrison condition holds,
  and the entries off coordinate `0` are pairwise distinct, all by `decide`.
* `permutation_bijective`; `permutation_bijective_general` for every round-constant table.
* `activity`: two distinct inputs incur at least `20` charged S-box applications over the `64`
  rounds, a bound obtained from the eight full rounds alone (`(4 / 2 + 4 / 2) * 5`);
  `activity_with_partial`: at least `34`, adding `56 / 4 = 14` for the partial rounds.
* `internal_inactive_trivial`: no nonzero difference stays inactive through four consecutive
  partial rounds; `internal_inactive_three_ne_bot`: some nonzero difference stays inactive through
  three, so the window is exactly `4`; `finrank_internal_inactive`: the differences that stay
  inactive through `r ≤ 4` consecutive partial rounds form a space of dimension exactly `4 - r`.
* `independent_key_probability`, `independent_key_probability_with_partial`: for every nonzero
  trail `T`, `keyCount * 2^5020 ≤ |F^4|^64` and `keyCount * 2^8534 ≤ |F^4|^64` (`251` bits per
  charged S-box; `probability_exponent`, `probability_exponent_with_partial`).
  `independent_key_probability_exact`: `keyCount * p^34 ≤ 4^34 * |F^4|^64`;
  `independent_key_probability_sharp`: `keyCount * 2^8554 ≤ |F^4|^64`.
* `independent_key_differential_exact`, `independent_key_differential_sharp`: for every nonzero
  input difference, `diffKeyCount * p^4 ≤ 4^4 * |F^4|^64` and `diffKeyCount * 2^1006 ≤ |F^4|^64`,
  charging the `B - 1 = 4` S-boxes of the first two full rounds.
* Each activity, trail and differential statement also has a `_general` form for every
  round-constant table.

`Checks/AztecBN254.lean` shows that the per-S-box exponent `251` and the exponents `8554` and
`1006` cannot be raised and that the branch number is exactly `5`, and proves the known-answer
vectors.

## What is not claimed

The activity counts are lower bounds on charged S-box applications for actual input pairs; they
are not claimed to be attained. The trail-probability statements concern one trail in the model
with an additional independent uniform key per round; the differential statements bound the
key-averaged differential in the same model. None of them is a statement about the permutation
with its fixed constants, or about any one key. Nothing is said about subspace trails beyond the
inactive-space statements here, about algebraic attacks, about the sponges built on the
permutation (barretenberg's `FieldSponge`, Noir's `Poseidon2Hasher`), or about equivalence with
the C++ or Rust code or the circuit gadgets and relations, beyond the transcription stated here
and the known-answer vectors of `Checks/AztecBN254.lean`.
-/

set_option autoImplicit false

namespace Poseidon2.AztecBN254

open Poseidon2.BN254 (modulus F field_card sbox sbox_toFun sbox_uniform)

/-- A width-four state; coordinate `i` is the code's `state[i]`. -/
abbrev State := Fin 4 → F

/-! ### The external layer -/

theorem two_ne_zero_F : (2 : F) ≠ 0 := by decide

/-- **The external layer**: `x ↦ hlMat4 x`, the matrix of barretenberg's
`matrix_multiplication_4x4` (aztec-packages `v1.0.0` `P2/poseidon2_permutation.hpp:52-83`, matrix
in the comment at `:56-61`) and of Noir's (noir `v1.0.0` `NS/poseidon2.rs:48-68`), row `i` giving
output `i`. Its inverse is `y ↦ 8⁻¹ • hlMat4Inv8 y`. -/
def external : State ≃ₗ[F] State := hlMat4Equiv F two_ne_zero_F

theorem external_apply (x : State) :
    external x = ![5 * x 0 + 7 * x 1 + x 2 + 3 * x 3, 4 * x 0 + 6 * x 1 + x 2 + x 3,
      x 0 + 3 * x 1 + 5 * x 2 + 7 * x 3, x 0 + x 1 + 4 * x 2 + 6 * x 3] :=
  hlMat4_mulVec F x

theorem external_eq_mulVec (x : State) : external x = (hlMat4 F).mulVec x :=
  rfl

/-- `8⁻¹` in `F` as an integer representative, checked by `8 * inv8 = 1`. -/
def inv8 : F := 19152212512859365819465605027100115702479818850364030050735928663253832433665

theorem eight_mul_inv8 : (8 : F) * inv8 = 1 := by decide

/-- **The explicit inverse of the external layer.** -/
theorem external_symm_apply (y : State) :
    external.symm y = inv8 • ![-y 0 + 3 * y 1 - 6 * y 2 + 7 * y 3, y 0 - y 1 + 4 * y 2 - 5 * y 3,
      -6 * y 0 + 7 * y 1 - y 2 + 3 * y 3, 4 * y 0 - 5 * y 1 + y 2 - y 3] := by
  rw [external, hlMat4Equiv_symm_apply, inv_eq_of_mul_eq_one_right eight_mul_inv8]
  congr 1
  funext i
  fin_cases i <;>
    simp [hlMat4Inv8, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- The eight primes of `hlMat4Primes` are nonzero in `F`. -/
theorem hlMat4Primes_ne_zero : ∀ p ∈ hlMat4Primes, (p : F) ≠ 0 := by
  decide

/-- **`hlMat4` is MDS over `F`**: every square submatrix is nonsingular. -/
theorem external_mds : IsMDS (hlMat4 F) :=
  hlMat4_isMDS hlMat4Primes_ne_zero

/-- **The external layer has branch number at least `5`.** -/
theorem external_branch : isBranchBound id external 5 :=
  Hades.branch_of_mds external_mds external external_eq_mulVec

/-! ### The internal layer -/

/-- **The internal diagonal `d`**, the array `internal_matrix_diagonal` of aztec-packages `v1.0.0`
`P2/poseidon2_params.hpp:24-29` (`internal_matrix_diagonal_minus_one` in `v6.1.0`
`P2/poseidon2_params.hpp:26-31`; `INTERNAL_MATRIX_DIAGONAL` in noir `v1.0.0`
`NS/poseidon2_constants.rs:49-57`). The code computes `state[i] * d_i + sum`
(aztec-packages `v1.0.0` `P2/poseidon2_permutation.hpp:92-103`), so this array is exactly `d` in
`diag(d) + J`; the diagonal entries of that matrix are `d_i + 1`. -/
def internalDiag : Fin 4 → F :=
  ![0x10dc6e9c006ea38b04b1e03b4bd9490c0d03f98929ca1d7fb56821fd19d3b6e7,
    0x0c28145b6a44df3e0149b3d0a30b3bb599df9756d4dd9b84a86b38cfb45a740b,
    0x00544b8338791518b2c7645a50392798b21f75bb60e3596170067d00141cac15,
    0x222c01175718386f2e2e82eb122789e352e105a3b8fa852613bc534433ee428b]

/-- The inverses of the entries of `internalDiag`, computed outside Lean and checked by
`internalDiag_mul_inv`. -/
def internalDiagInv : Fin 4 → F :=
  ![10503307978722032543573858770574947361370925949551134938739460043484274085297,
    17915558130044465897319677871823371759055953799590209244827921585089065412625,
    6860613596825997654445474816140745877247157403640869166290763655149084892844,
    1360303037482974457629461991961993693912879890380628736159110085615008653536]

theorem internalDiag_mul_inv : ∀ i, internalDiag i * internalDiagInv i = 1 := by
  decide

/-- Every entry of the diagonal is nonzero in `F`. -/
theorem internalDiag_ne_zero : ∀ i, internalDiag i ≠ 0 := by
  decide

/-- **The Sherman–Morrison condition** `1 + ∑ i, (d i)⁻¹ ≠ 0`, by the table of inverses. -/
theorem one_add_sum_inv_ne_zero : 1 + ∑ i, (internalDiag i)⁻¹ ≠ 0 := by
  rw [sum_inv_eq_of_mul_eq_one internalDiag_mul_inv, Fin.sum_univ_four]
  decide

/-- **The diagonal entries off coordinate `0` are pairwise distinct in `F`**, by `decide`. -/
theorem internalDiag_injOn : Set.InjOn internalDiag {i | i ≠ 0} := fun i hi j hj h =>
  (by decide : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → internalDiag i = internalDiag j → i = j)
    i j hi hj h

/-- **The internal layer** `diag(d) + J`, a linear equivalence with the Sherman–Morrison inverse
`diagPlusOnesInv`. -/
def internal : State ≃ₗ[F] State :=
  diagPlusOnesEquiv 1 internalDiag one_ne_zero internalDiag_ne_zero one_add_sum_inv_ne_zero

theorem internal_toLinearMap : internal.toLinearMap = diagPlusOnes (1 : F) internalDiag :=
  rfl

/-- Coordinate `i` of the internal layer is `d_i x_i + (x_0 + x_1 + x_2 + x_3)`. -/
theorem internal_apply (x : State) (i : Fin 4) :
    internal x i = internalDiag i * x i + ∑ j, x j := by
  rw [internal, diagPlusOnesEquiv_apply, diagPlusOnes_apply, one_mul]

/-- **The internal layer is multiplication by `diag(d) + J`.** -/
theorem internal_eq_mulVec (x : State) :
    internal x = (Matrix.diagonal internalDiag + Matrix.of fun _ _ => (1 : F)).mulVec x := by
  rw [internal, diagPlusOnesEquiv_apply, diagPlusOnes_eq_mulVec, one_smul]

/-! ### The round constants -/

/-- **The round constants** `round_constants[r][i]`, `r < 64`, `i < 4`, of aztec-packages
`v1.0.0` `P2/poseidon2_params.hpp:58-443` (row `r` on lines `60 + 6 r` to `63 + 6 r`), equal to
`ROUND_CONSTANT` of noir `v1.0.0` `NS/poseidon2_constants.rs:61-449`, copied as the hexadecimal
literals of the source. Every literal is below `p` (checked outside Lean), so it is the field
element the code reads. -/
def roundConstants : Fin 64 → State :=
  ![![0x19b849f69450b06848da1d39bd5e4a4302bb86744edc26238b0878e269ed23e5,
      0x265ddfe127dd51bd7239347b758f0a1320eb2cc7450acc1dad47f80c8dcf34d6,
      0x199750ec472f1809e0f66a545e1e51624108ac845015c2aa3dfc36bab497d8aa,
      0x157ff3fe65ac7208110f06a5f74302b14d743ea25067f0ffd032f787c7f1cdf8],
    ![0x2e49c43c4569dd9c5fd35ac45fca33f10b15c590692f8beefe18f4896ac94902,
      0x0e35fb89981890520d4aef2b6d6506c3cb2f0b6973c24fa82731345ffa2d1f1e,
      0x251ad47cb15c4f1105f109ae5e944f1ba9d9e7806d667ffec6fe723002e0b996,
      0x13da07dc64d428369873e97160234641f8beb56fdd05e5f3563fa39d9c22df4e],
    ![0x0c009b84e650e6d23dc00c7dccef7483a553939689d350cd46e7b89055fd4738,
      0x011f16b1c63a854f01992e3956f42d8b04eb650c6d535eb0203dec74befdca06,
      0x0ed69e5e383a688f209d9a561daa79612f3f78d0467ad45485df07093f367549,
      0x04dba94a7b0ce9e221acad41472b6bbe3aec507f5eb3d33f463672264c9f789b],
    ![0x0a3f2637d840f3a16eb094271c9d237b6036757d4bb50bf7ce732ff1d4fa28e8,
      0x259a666f129eea198f8a1c502fdb38fa39b1f075569564b6e54a485d1182323f,
      0x28bf7459c9b2f4c6d8e7d06a4ee3a47f7745d4271038e5157a32fdf7ede0d6a1,
      0x0a1ca941f057037526ea200f489be8d4c37c85bbcce6a2aeec91bd6941432447],
    ![0x0c6f8f958be0e93053d7fd4fc54512855535ed1539f051dcb43a26fd926361cf,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x123106a93cd17578d426e8128ac9d90aa9e8a00708e296e084dd57e69caaf811,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x26e1ba52ad9285d97dd3ab52f8e840085e8fa83ff1e8f1877b074867cd2dee75,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1cb55cad7bd133de18a64c5c47b9c97cbe4d8b7bf9e095864471537e6a4ae2c5,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1dcd73e46acd8f8e0e2c7ce04bde7f6d2a53043d5060a41c7143f08e6e9055d0,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x011003e32f6d9c66f5852f05474a4def0cda294a0eb4e9b9b12b9bb4512e5574,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2b1e809ac1d10ab29ad5f20d03a57dfebadfe5903f58bafed7c508dd2287ae8c,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2539de1785b735999fb4dac35ee17ed0ef995d05ab2fc5faeaa69ae87bcec0a5,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0c246c5a2ef8ee0126497f222b3e0a0ef4e1c3d41c86d46e43982cb11d77951d,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x192089c4974f68e95408148f7c0632edbb09e6a6ad1a1c2f3f0305f5d03b527b,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1eae0ad8ab68b2f06a0ee36eeb0d0c058529097d91096b756d8fdc2fb5a60d85,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x179190e5d0e22179e46f8282872abc88db6e2fdc0dee99e69768bd98c5d06bfb,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x29bb9e2c9076732576e9a81c7ac4b83214528f7db00f31bf6cafe794a9b3cd1c,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x225d394e42207599403efd0c2464a90d52652645882aac35b10e590e6e691e08,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x064760623c25c8cf753d238055b444532be13557451c087de09efd454b23fd59,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x10ba3a0e01df92e87f301c4b716d8a394d67f4bf42a75c10922910a78f6b5b87,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0e070bf53f8451b24f9c6e96b0c2a801cb511bc0c242eb9d361b77693f21471c,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1b94cd61b051b04dd39755ff93821a73ccd6cb11d2491d8aa7f921014de252fb,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1d7cb39bafb8c744e148787a2e70230f9d4e917d5713bb050487b5aa7d74070b,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2ec93189bd1ab4f69117d0fe980c80ff8785c2961829f701bb74ac1f303b17db,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2db366bfdd36d277a692bb825b86275beac404a19ae07a9082ea46bd83517926,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x062100eb485db06269655cf186a68532985275428450359adc99cec6960711b8,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0761d33c66614aaa570e7f1e8244ca1120243f92fa59e4f900c567bf41f5a59b,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x20fc411a114d13992c2705aa034e3f315d78608a0f7de4ccf7a72e494855ad0d,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x25b5c004a4bdfcb5add9ec4e9ab219ba102c67e8b3effb5fc3a30f317250bc5a,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x23b1822d278ed632a494e58f6df6f5ed038b186d8474155ad87e7dff62b37f4b,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x22734b4c5c3f9493606c4ba9012499bf0f14d13bfcfcccaa16102a29cc2f69e0,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x26c0c8fe09eb30b7e27a74dc33492347e5bdff409aa3610254413d3fad795ce5,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x070dd0ccb6bd7bbae88eac03fa1fbb26196be3083a809829bbd626df348ccad9,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x12b6595bdb329b6fb043ba78bb28c3bec2c0a6de46d8c5ad6067c4ebfd4250da,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x248d97d7f76283d63bec30e7a5876c11c06fca9b275c671c5e33d95bb7e8d729,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1a306d439d463b0816fc6fd64cc939318b45eb759ddde4aa106d15d9bd9baaaa,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x28a8f8372e3c38daced7c00421cb4621f4f1b54ddc27821b0d62d3d6ec7c56cf,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0094975717f9a8a8bb35152f24d43294071ce320c829f388bc852183e1e2ce7e,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x04d5ee4c3aa78f7d80fde60d716480d3593f74d4f653ae83f4103246db2e8d65,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2a6cf5e9aa03d4336349ad6fb8ed2269c7bef54b8822cc76d08495c12efde187,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2304d31eaab960ba9274da43e19ddeb7f792180808fd6e43baae48d7efcba3f3,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x03fd9ac865a4b2a6d5e7009785817249bff08a7e0726fcb4e1c11d39d199f0b0,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x00b7258ded52bbda2248404d55ee5044798afc3a209193073f7954d4d63b0b64,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x159f81ada0771799ec38fca2d4bf65ebb13d3a74f3298db36272c5ca65e92d9a,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1ef90e67437fbc8550237a75bc28e3bb9000130ea25f0c5471e144cf4264431f,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1e65f838515e5ff0196b49aa41a2d2568df739bc176b08ec95a79ed82932e30d,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2b1b045def3a166cec6ce768d079ba74b18c844e570e1f826575c1068c94c33f,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0832e5753ceb0ff6402543b1109229c165dc2d73bef715e3f1c6e07c168bb173,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x02f614e9cedfb3dc6b762ae0a37d41bab1b841c2e8b6451bc5a8e3c390b6ad16,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0e2427d38bd46a60dd640b8e362cad967370ebb777bedff40f6a0be27e7ed705,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0493630b7c670b6deb7c84d414e7ce79049f0ec098c3c7c50768bbe29214a53a,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x22ead100e8e482674decdab17066c5a26bb1515355d5461a3dc06cc85327cea9,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x25b3e56e655b42cdaae2626ed2554d48583f1ae35626d04de5084e0b6d2a6f16,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1e32752ada8836ef5837a6cde8ff13dbb599c336349e4c584b4fdc0a0cf6f9d0,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2fa2a871c15a387cc50f68f6f3c3455b23c00995f05078f672a9864074d412e5,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x2f569b8a9a4424c9278e1db7311e889f54ccbf10661bab7fcd18e7c7a7d83505,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x044cb455110a8fdd531ade530234c518a7df93f7332ffd2144165374b246b43d,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x227808de93906d5d420246157f2e42b191fe8c90adfe118178ddc723a5319025,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x02fcca2934e046bc623adead873579865d03781ae090ad4a8579d2e7a6800355,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x0ef915f0ac120b876abccceb344a1d36bad3f3c5ab91a8ddcbec2e060d8befac,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000,
      0x0000000000000000000000000000000000000000000000000000000000000000],
    ![0x1797130f4b7a3e1777eb757bc6f287f6ab0fb85f6be63b09f3b16ef2b1405d38,
      0x0a76225dc04170ae3306c85abab59e608c7f497c20156d4d36c668555decc6e5,
      0x1fffb9ec1992d66ba1e77a7b93209af6f8fa76d48acb664796174b5326a31a5c,
      0x25721c4fc15a3f2853b57c338fa538d85f8fbba6c6b9c6090611889b797b9c5f],
    ![0x0c817fd42d5f7a41215e3d07ba197216adb4c3790705da95eb63b982bfcaf75a,
      0x13abe3f5239915d39f7e13c2c24970b6df8cf86ce00a22002bc15866e52b5a96,
      0x2106feea546224ea12ef7f39987a46c85c1bc3dc29bdbd7a92cd60acb4d391ce,
      0x21ca859468a746b6aaa79474a37dab49f1ca5a28c748bc7157e1b3345bb0f959],
    ![0x05ccd6255c1e6f0c5cf1f0df934194c62911d14d0321662a8f1a48999e34185b,
      0x0f0e34a64b70a626e464d846674c4c8816c4fb267fe44fe6ea28678cb09490a4,
      0x0558531a4e25470c6157794ca36d0e9647dbfcfe350d64838f5b1a8a2de0d4bf,
      0x09d3dca9173ed2faceea125157683d18924cadad3f655a60b72f5864961f1455],
    ![0x0328cbd54e8c0913493f866ed03d218bf23f92d68aaec48617d4c722e5bd4335,
      0x2bf07216e2aff0a223a487b1a7094e07e79e7bcc9798c648ee3347dd5329d34b,
      0x1daf345a58006b736499c583cb76c316d6f78ed6a6dffc82111e11a63fe412df,
      0x176563472456aaa746b694c60e1823611ef39039b2edc7ff391e6f2293d2c404]]

/-- The round constants as a total function: row `n` for `n < 64`, zero afterwards. -/
def values (n : ℕ) : State := if h : n < 64 then roundConstants ⟨n, h⟩ else 0

/-- **Partial rounds add their constant only at the S-box coordinate**: rows `4` to `59` of the
table are zero at coordinates `1`, `2` and `3`. -/
theorem partial_constants_zero :
    ∀ n : Fin 56, ∀ i : Fin 4, i ≠ 0 → values (4 + n.val) i = 0 := by
  decide

/-! ### The permutation -/

/-- The linear layer of round `n`: the external layer in the full rounds `n < 4` and
`60 ≤ n`, the internal layer in the partial rounds. -/
def linear (n : ℕ) : State ≃ₗ[F] State := if n < 4 ∨ 60 ≤ n then external else internal

/-- The `64` rounds: four full, `56` partial with the S-box on coordinate `0`, four full. -/
def rounds : ℕ → Hades.RoundSpec (Fin 4) F :=
  Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear values

/-- **The permutation**: the initial external layer (aztec-packages `v1.0.0`
`P2/poseidon2_permutation.hpp:143`), then the `64` rounds (`:146-166`). -/
def permutation (x : State) : State := Hades.execute rounds (external x) 64

theorem permutation_bijective : Function.Bijective permutation :=
  (Hades.execute_bijective rounds 64).comp external.bijective

/-- Bijectivity holds for every round-constant table. -/
theorem permutation_bijective_general (table : ℕ → State) :
    Function.Bijective (fun x => Hades.execute
      (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table) (external x) 64) :=
  (Hades.execute_bijective _ 64).comp external.bijective

theorem linear_prefix {j : ℕ} (hj : j < 4) : linear j = external := by
  simp [linear, hj]

theorem linear_middle {j : ℕ} (hj : j < 56) : linear (4 + j) = internal := by
  simp [linear, show ¬(4 + j < 4) by omega, show ¬(60 ≤ 4 + j) by omega]

theorem linear_suffix (j : ℕ) : linear (4 + 56 + j) = external := by
  simp [linear, show 60 ≤ 4 + 56 + j by omega]

/-- **A full round of the first half is the code's round** (aztec-packages `v1.0.0`
`P2/poseidon2_permutation.hpp:147-151`): add the row, apply the S-box to every coordinate,
then the external layer. -/
theorem rounds_apply_prefix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds j).apply x = external (fun i => sbox (x i + values j i)) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply, Hades.hadesMask_prefix 4 56 4 _ hj,
    linear_prefix hj, Hades.maskedEquiv_apply]
  congr 1
  funext i
  simp

/-- **A partial round is the code's round** (aztec-packages `v1.0.0`
`P2/poseidon2_permutation.hpp:155-159`; noir `v1.0.0` `NS/poseidon2.rs:108-112`): add
`round_constants[4 + j][0]` to `state[0]`, apply the S-box to `state[0]` only, then the internal
layer. This uses `partial_constants_zero`. -/
theorem rounds_apply_partial {j : ℕ} (hj : j < 56) (x : State) :
    (rounds (4 + j)).apply x =
      internal (Function.update x 0 (sbox (x 0 + values (4 + j) 0))) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply,
    Hades.hadesMask_middle 4 56 4 _ hj, linear_middle hj, Hades.maskedEquiv_apply]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst hi
    simp
  · have hz := partial_constants_zero ⟨j, hj⟩ i hi
    simp [hi, hz]

/-- **A full round of the second half is the code's round** (aztec-packages `v1.0.0`
`P2/poseidon2_permutation.hpp:162-166`). -/
theorem rounds_apply_suffix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds (4 + 56 + j)).apply x = external (fun i => sbox (x i + values (4 + 56 + j) i)) := by
  simp only [rounds, Hades.hadesSchedule, Hades.RoundSpec.apply,
    Hades.hadesMask_suffix 4 56 4 _ hj, linear_suffix, Hades.maskedEquiv_apply]
  congr 1
  funext i
  simp

/-! ### Outer-round activity -/

theorem full_prefix (j : ℕ) (_hj : j + 1 < 4) : isBranchBound id (linear j) 5 := by
  rw [linear_prefix (by omega)]
  exact external_branch

theorem full_suffix (j : ℕ) (_hj : j + 1 < 4) : isBranchBound id (linear (4 + 56 + j)) 5 := by
  rw [linear_suffix]
  exact external_branch

/-- **Twenty active S-boxes, for every round-constant table.** Two distinct inputs incur at
least `(4 / 2 + 4 / 2) * 5 = 20` charged S-box applications over the `64` rounds; the bound comes
from the eight full rounds alone (`Hades.hades_bound` with branch number `5`). A lower bound; it
is not claimed to be attained. -/
theorem activity_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    20 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      (Hades.differenceTrace (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (external x) (external y)) 0 64 :=
  Hades.hades_bound 4 56 4 5 {0} (fun _ _ => sbox) linear table
    (fun h => hxy (external.injective h)) full_prefix full_suffix

/-- **Twenty active S-boxes** for the pinned permutation. -/
theorem activity {x y : State} (hxy : x ≠ y) :
    20 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 64 :=
  activity_general values hxy

/-! ### The partial rounds: window `4` by the diagonal criterion

The internal layer is `diagPlusOnes 1 internalDiag` (`internal_toLinearMap`), and its diagonal
entries off coordinate `0` are pairwise distinct (`internalDiag_injOn`). The criterion
`Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff` then says that no nonzero difference stays
inactive through `4` consecutive partial rounds, and `Hades.finrank_inactiveSpace_diagPlusOnes`
gives the dimension `4 - r` for `r ≤ 4`. These are statements about inactive differences of the
partial rounds only, not a proof of resistance to subspace trails in general. -/

/-- **No nonzero difference stays inactive through four consecutive partial rounds.** -/
theorem internal_inactive_trivial :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 4)) 4 = ⊥ := by
  have h := (Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff (one_ne_zero : (1 : F) ≠ 0)
    internalDiag (0 : Fin 4)).mpr internalDiag_injOn
  rw [Fintype.card_fin] at h
  rw [internal_toLinearMap]
  exact h

/-- **Exactly `4 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds**, for `r ≤ 4`. -/
theorem finrank_internal_inactive {r : ℕ} (hr : r ≤ 4) :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 4)) r) =
      4 - r := by
  have h := Hades.finrank_inactiveSpace_diagPlusOnes (one_ne_zero : (1 : F) ≠ 0) internalDiag
    (0 : Fin 4) internalDiag_injOn (r := r) (by rw [Fintype.card_fin]; exact hr)
  rw [Fintype.card_fin] at h
  rw [internal_toLinearMap]
  exact h

/-- **The window `4` cannot be shortened**: some nonzero difference stays inactive through three
consecutive partial rounds. -/
theorem internal_inactive_three_ne_bot :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 4)) 3 ≠ ⊥ :=
  Hades.inactiveSpace_ne_bot _ _ 3 (by simp)

theorem middle_linear (table : ℕ → State) (j : ℕ) (hj : j < 56) :
    (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table (4 + j)).lin = internal :=
  linear_middle hj

theorem middle_mask (table : ℕ → State) (j : ℕ) (hj : j < 56) :
    (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table (4 + j)).mask = {0} :=
  Hades.hadesMask_middle 4 56 4 _ hj

/-- **Thirty-four active S-boxes, for every round-constant table.** Two distinct inputs incur at
least `20` charged S-box applications in the full rounds and `56 / 4 = 14` in the partial rounds,
one per disjoint window of four. A lower bound; it is not claimed to be attained. -/
theorem activity_with_partial_general (table : ℕ → State) {x y : State} (hxy : x ≠ y) :
    34 ≤ Hades.scheduledWeight (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
      (Hades.differenceTrace (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (external x) (external y)) 0 64 :=
  Hades.outer_middle_bound _ (fun h => hxy (external.injective h)) 4 56 4 5 4
    (fun _ hj => Hades.hadesMask_prefix 4 56 4 _ hj)
    (fun _ hj => Hades.hadesMask_suffix 4 56 4 _ hj)
    full_prefix full_suffix internal {0} (middle_linear table) (middle_mask table)
    internal_inactive_trivial

/-- **Thirty-four active S-boxes** for the pinned permutation. -/
theorem activity_with_partial {x y : State} (hxy : x ≠ y) :
    34 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 64 :=
  activity_with_partial_general values hxy

/-! ### The independent-key trail bounds -/

/-- `u * 2^d ≤ |F|` for `u = 4`, `d = 251`. -/
theorem four_mul_two_pow_le_card : 4 * 2 ^ 251 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- **Trail bound from the full rounds, for every round-constant table.** In the model with an
additional independent uniform key per round, the number of keys realising a fixed nonzero
trail `T`, times `2^(251 * 20)`, is at most the number of all key sequences. This concerns one
trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (4 + 56 + 4) T x * 2 ^ (251 * ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2))
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  Hades.hades_probability (Idx := Fin 4) (K := F) (u := 4) (d := 251)
    4 56 4 5 {0} (fun _ _ => sbox) linear table
    (fun _ _ _ => sbox_uniform) four_mul_two_pow_le_card full_prefix full_suffix h0 x

/-- **Trail bound from the full rounds** for the pinned rounds, in the same model. -/
theorem independent_key_probability {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 56 + 4) T x * 2 ^ (251 * ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2))
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_general values h0 x

/-- The displayed bound's concrete exponent. -/
theorem probability_exponent : 251 * ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2) = 5020 := by
  decide

/-- **Trail bound with the partial rounds charged, for every round-constant table**, in the
same model: `keyCount * 2^(251 * (20 + 56 / 4)) ≤ |F^4|^64` for every nonzero trail. This
concerns one trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_with_partial_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (4 + 56 + 4) T x * 2 ^ (251 * ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4))
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  Hades.hades_probability_with_middle (Idx := Fin 4) (K := F) (u := 4) (d := 251)
    4 56 4 5 4 {0} (fun _ _ => sbox) linear table
    (fun _ _ _ => sbox_uniform) four_mul_two_pow_le_card full_prefix full_suffix
    internal (fun _ hj => linear_middle hj) internal_inactive_trivial h0 x

/-- **Trail bound with the partial rounds charged** for the pinned rounds, in the same model. -/
theorem independent_key_probability_with_partial {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 56 + 4) T x
        * 2 ^ (251 * ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4))
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_with_partial_general values h0 x

/-- The displayed bound's concrete exponent. -/
theorem probability_exponent_with_partial :
    251 * ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4) = 8534 := by
  decide

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^34` (`p = modulus`), is at most `4^34` times the number of all
key sequences. The `34` charged S-boxes are counted as in `activity_with_partial_general`. This
concerns one trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_exact_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (4 + 56 + 4) T x * modulus ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4)
      ≤ 4 ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4)
        * Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_probability_with_middle_exact (Idx := Fin 4) (K := F) (u := 4)
    4 56 4 5 4 {0} (fun _ _ => sbox) linear table
    (fun _ _ _ => sbox_uniform) full_prefix full_suffix
    internal (fun _ hj => linear_middle hj) internal_inactive_trivial h0 x
  rw [field_card] at h
  exact h

/-- **Trail bound as an exact ratio** for the pinned rounds, in the same model:
`keyCount * p^34 ≤ 4^34 * |F^4|^64` for every nonzero trail. -/
theorem independent_key_probability_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 56 + 4) T x
        * modulus ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4)
      ≤ 4 ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4)
        * Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_exact_general values h0 x

set_option exponentiation.threshold 9000 in
/-- `2^8554 * 4^34 ≤ p^34`, by `decide`. `Checks/AztecBN254.lean` shows that
`2^8555 * 4^34 ≤ p^34` fails, so `8554` is the largest such exponent. -/
theorem sharp_exponent_bound :
    2 ^ 8554 * 4 ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4) := by
  decide

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^8554`, is at
most the number of all key sequences. `8554` is the largest exponent that this arithmetic gives.
This concerns one trail in that model only: not the permutation with its fixed constants, and
not a differential. -/
theorem independent_key_probability_sharp_general (table : ℕ → State) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (4 + 56 + 4) T x * 2 ^ 8554
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  Hades.mul_le_of_ratio (independent_key_probability_exact_general table h0 x)
    sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned rounds, in the same model:
`keyCount * 2^8554 ≤ |F^4|^64` for every nonzero trail. -/
theorem independent_key_probability_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (4 + 56 + 4) T x * 2 ^ 8554 ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_probability_sharp_general values h0 x

/-! ### The independent-key differential bound

`Hades.hades_differential_bound` charges `B - 1 = 4` S-boxes of the first two full rounds, at the
ratio `p / 4` each; the other rounds are not charged. Since `4 * log2 (p / 4) ≈ 1006.3`, the
sharp exponent is `1006`. Nothing here concerns the permutation with its fixed constants. -/

/-- **Differential bound as an exact ratio, for every round-constant table**, in the model with
an additional independent uniform key per round: for every nonzero input difference `a`, every
output difference `b` and every input `x`, the number of key sequences under which `(x, x + a)`
has output difference `b` after the `64` rounds that follow the initial external layer, times
`p^4`, is at most `4^4` times the number of all key sequences. This concerns the key-averaged
differential only: not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_exact_general (table : ℕ → State) {a : State}
    (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (4 + 56 + 4) a b x * modulus ^ 4
      ≤ 4 ^ 4 * Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) := by
  have h := Hades.hades_differential_bound (Idx := Fin 4) (K := F) (u := 4) 4 56 4 5
    (by norm_num) {0} (fun _ _ => sbox) linear table (fun _ _ _ => sbox_uniform)
    (full_prefix 0 (by norm_num)) ha b x
  rw [field_card, show (5 : ℕ) - 1 = 4 from rfl] at h
  exact h

/-- **Differential bound as an exact ratio** for the pinned rounds, in the same model. -/
theorem independent_key_differential_exact {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (4 + 56 + 4) a b x * modulus ^ 4
      ≤ 4 ^ 4 * Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_differential_exact_general values ha b x

set_option exponentiation.threshold 2000 in
/-- `2^1006 * 4^4 ≤ p^4`, by `decide`. `Checks/AztecBN254.lean` shows that
`2^1007 * 4^4 ≤ p^4` fails, so `1006` is the largest such exponent. -/
theorem differential_sharp_exponent_bound : 2 ^ 1006 * 4 ^ 4 ≤ modulus ^ 4 := by
  decide

/-- **Differential bound with the sharp exponent, for every round-constant table**, in the same
model: for every nonzero input difference `a`, the key count of the differential `(a, b)`, times
`2^1006`, is at most the number of all key sequences. This concerns the key-averaged
differential only: not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_sharp_general (table : ℕ → State) {a : State}
    (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount (Hades.hadesSchedule 4 56 4 {0} (fun _ _ => sbox) linear table)
        (4 + 56 + 4) a b x * 2 ^ 1006
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  Hades.mul_le_of_ratio (independent_key_differential_exact_general table ha b x)
    differential_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Differential bound with the sharp exponent** for the pinned rounds, in the same model. -/
theorem independent_key_differential_sharp {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (4 + 56 + 4) a b x * 2 ^ 1006
      ≤ Fintype.card (Fin 4 → F) ^ (4 + 56 + 4) :=
  independent_key_differential_sharp_general values ha b x

end Poseidon2.AztecBN254
