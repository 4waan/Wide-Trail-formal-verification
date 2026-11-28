/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.AztecBN254Execution
import WideTrail.Algebra.Checks.MDS4

/-!
# Checks for the Aztec and Noir BN254 width-four certificate

`WideTrail.Poseidon2.AztecBN254` models the Poseidon2 permutation of barretenberg
(`Poseidon2Bn254ScalarFieldParams`) and of Noir's ACVM BN254 solver. The checks below test that
model against the published known-answer vectors, record which readings of the code they rule
out, show that the exponents of the certificate are the largest its arithmetic gives (the
arithmetic step fails at `E + 1`; the key-count bounds themselves are not shown to be tight), and
show that the branch number of the external layer is exactly `5`.
Every finite check is kernel `decide`. The whole-permutation checks run on the runner of
`WideTrail.Poseidon2.AztecBN254Execution`, and its transfer lemmas carry the computed values
over to the specification `permutation` (or `permutationWith` for a control).

As in `WideTrail.Poseidon2.AztecBN254`, `AZ1` is aztec-packages tag `v1.0.0` (commit
`79e9bd1698f4bba6deade8f76c676f9bbb12ff74`), `AZ6` its tag `v6.1.0` (commit
`6595672787600ce14bb6dd0dd612b2ae6219b061`), `NR1` noir tag `v1.0.0` (commit
`275d3ab1a5c916c6ea73e8d6b943f685f574500c`), `NRN` noir tag `nightly-2025-06-19` (commit
`e96b40c4214967f14da5beabf2570a2b082940e7`, the Noir that AZ1 vendors), `BB/` the directory
`barretenberg/cpp/src/barretenberg/`, `P2/` the directory `BB/crypto/poseidon2/` and `NS/` the
directory `acvm-repo/bn254_blackbox_solver/src/`.

## Known-answer vectors

All of them use the deployed constants. Inputs and outputs are copied from the sources; the
intermediate states are not.

* `test_vector`: `(0, 1, 2, 3)`, the `TEST_VECTOR_INPUT`/`TEST_VECTOR_OUTPUT` of AZ1
  `P2/poseidon2_params.hpp:445-456`, checked by AZ1 `P2/poseidon2_permutation.test.cpp:12-20`.
  The parameter script emitted it from its matrix-form reference, the same script that generated
  the constants. The same input and output are the bb.js test of AZ1
  `yarn-project/foundation/src/crypto/poseidon/index.test.ts:5-13`, the "sequential small values"
  case of NR1 `NS/poseidon2.rs:158-167`, the documentation example of NR1
  `noir_stdlib/src/hash/mod.nr:333-334` (coordinate `0`) and `TEST_VECTOR_INPUT`,
  `TEST_VECTOR_OUTPUT` of AZ6 `P2/poseidon2_params.hpp:447-452`, `:453-458`.
* `consistency_vector`: four copies of the literal
  `9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789`, AZ1
  `P2/poseidon2_permutation.test.cpp:44-61`. The literal is about `3.2 p`; `fr(std::string)`
  reads it as a 256-bit integer (AZ1 `BB/numeric/uint256/uint256.hpp:52-92`) and reduces it mod
  `p` (`consistency_literal_eq`; AZ1 `BB/ecc/fields/field_declarations.hpp:62-66`, `:131-135`,
  and `BB/ecc/fields/field_impl.hpp:323-334`, whose three `self_reduce_once` calls reduce any
  input below `4 p`). A
  Lean numeral in `F` is reduced mod `p` in the same way. The test's comment (`:41-43`) says these
  values were extracted from the code under test: this vector is self-generated.
* `noir_vector_bbjs`: `(1, 2, 3, 10 · 2^64)`, the bb.js test "test vectors from Noir should
  match" of AZ1 `yarn-project/foundation/src/crypto/poseidon/index.test.ts:15-23`; the test gives
  no provenance beyond its name.
* `zkhash_zeros`, `zkhash_u128_max`, `zkhash_p_sub_one`, `zkhash_arbitrary`: the other four cases
  of NR1 `NS/poseidon2.rs:137-215` (all zeros `:143-152`, `u128::MAX` in every lane `:173-182`,
  `p - 1` in every lane `:188-197`, four full-width values `:203-212`; with the sequential case
  above, all five). Their expected outputs were produced by the generic Poseidon2 code of the
  crate `zkhash` `0.2.0` fed Noir's own parameters (`:130-136`), so they check the loop and the
  layers against a second implementation, not the provenance of the constants. Every input is
  below `p`. The all-zeros output is also the `smoke_test` of NRN `NS/poseidon2.rs:631-643`.

## Negative controls

On the input and output of `test_vector`, the vector is not reproduced with the transpose of
`hlMat4` as external layer, the deployed internal layer and constants
(`test_vector_fails_transposed`); with `diag(d + 1) + J` as internal layer
(`test_vector_fails_diag_succ`); with `diag(d - 1) + J`, the reading of the stored array as the
true diagonal of the matrix (`test_vector_fails_diag_pred`); or without the initial external
layer (`test_vector_fails_skip_initial`). So the vector rules out each of these four
alternatives to the model.

## Exactness and cross-checks

* `whole_bits_succ_fails`: `4 * 2^252 > p`, so `251` is the largest `d` with `4 * 2^d ≤ p`, the
  bits charged per S-box by `independent_key_probability` and
  `independent_key_probability_with_partial`.
* `sharp_exponent_succ_fails`, `differential_sharp_exponent_succ_fails`: `8555` and `1007` fail,
  so `8554` and `1006` are the largest exponents the exact ratios give.
* `external_unit`, `external_not_branch_six`: `e_0` is sent to `(5, 4, 1, 1)`, weight `1 + 4`, so
  the branch number of the external layer is exactly `5`.
* `finrank_inactive_three`: one dimension of differences stays inactive through three
  consecutive partial rounds (with `internal_inactive_three_ne_bot`, the window `4` is exact).
* `declaredInternalMatrix_eq`: the array `internal_matrix` that AZ1 declares but the permutation
  does not read (`P2/poseidon2_params.hpp:31-56`) is `diag(d) + J`, with diagonal entries
  `d_i + 1`.
* `internalDiag_injective`: all four stored entries `d_i` of `internalDiag` are pairwise distinct
  (so are the diagonal entries `d_i + 1`).
* `mds4Checks_hlMat4_eq`: the integer matrix `Poseidon2.MDS4Checks.hlMat4` of
  `WideTrail.Algebra.Checks.MDS4` is `hlMat4 ℤ`, so the two declarations name the same matrix.
* `full_constants_ne_zero`, `partial_constants_ne_zero`: the `32` full-round constants and the
  `56` partial-round constants at coordinate `0` are nonzero.
* `hlMat4_ne_transpose`: the transposed control uses a different matrix.

## What is not claimed

The known-answer tests check single inputs. They show that the model computes the outputs that
the sources assert; they do not prove that model and code agree on every input. Several vectors
were produced by the code under test or by the script that produced the constants, and none of
them is evidence about how the constants were chosen. Nothing here is a comparison with a built
binary, with bb.js, with the circuit gadgets or relations, or with a sponge, and nothing here
strengthens the security claims of `WideTrail.Poseidon2.AztecBN254`.

The axiom footprints of the headline results of `WideTrail.Poseidon2.HorizenLabsM4`,
`WideTrail.Poseidon2.AztecBN254`, `WideTrail.Poseidon2.AztecBN254Execution` and of this file are
pinned at the end of the file.
-/

set_option autoImplicit false
-- Each `decide` on the runner unfolds all rounds at once; the default depth is too small.
set_option maxRecDepth 4000

namespace Poseidon2.AztecBN254.Checks

open Poseidon2.BN254 (F modulus field_card)

/-! ### Known-answer vectors -/

/-- The input `(0, 1, 2, 3)` of `TEST_VECTOR_INPUT` (AZ1 `P2/poseidon2_params.hpp:445-450`). -/
def testVectorInput : State := ![0, 1, 2, 3]

/-- `TEST_VECTOR_OUTPUT` (AZ1 `P2/poseidon2_params.hpp:451-456`). -/
def testVectorOutput : State :=
  ![0x01bd538c2ee014ed5141b29e9ae240bf8db3fe5b9a38629a9647cf8d76c01737,
    0x239b62e7db98aa3a2a8f6a0d2fa1709e7a35959aa6c7034814d9daa90cbac662,
    0x04cbb44c61d928ed06808456bf758cbf0c18d1e15a7b6dbc8245fa7515d5e3cb,
    0x2e11c5cff2a22c64d01304b778d78f6998eff1ab73163a35603f54794c30847a]

/-- **The model reproduces barretenberg's `TEST_VECTOR`** (AZ1
`P2/poseidon2_permutation.test.cpp:12-20`), which is also the bb.js test "from cpp", Noir's
"sequential small values" case and AZ6's `TEST_VECTOR_OUTPUT`. -/
theorem test_vector : permutation testVectorInput = testVectorOutput :=
  permutation_eq_of_dense (by decide)

/-- The literal of `Poseidon2Permutation.ConsistencyCheck` (AZ1
`P2/poseidon2_permutation.test.cpp:46-49`), read in `F`, is its residue mod `p`. -/
theorem consistency_literal_eq :
    (0x9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789 : F) =
      0x09539008b8b85db277c0f1b060715e72864101bf0927e05ce0280e4553456786 := by
  decide

/-- The input of `ConsistencyCheck`: four copies of its literal, reduced mod `p`. -/
def consistencyInput : State :=
  ![0x9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789,
    0x9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789,
    0x9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789,
    0x9a807b615c4d3e2fa0b1c2d3e4f56789fedcba9876543210abcdef0123456789]

/-- The expected output of `ConsistencyCheck` (AZ1 `P2/poseidon2_permutation.test.cpp:54-59`). -/
def consistencyOutput : State :=
  ![0x2bf1eaf87f7d27e8dc4056e9af975985bccc89077a21891d6c7b6ccce0631f95,
    0x0c01fa1b8d0748becafbe452c0cb0231c38224ea824554c9362518eebdd5701f,
    0x018555a8eb50cf07f64b019ebaf3af3c925c93e631f3ecd455db07bbb52bbdd3,
    0x0cbea457c91c22c6c31fd89afd2541efc2edf31736b9f721e823b2165c90fd41]

/-- **The model reproduces `Poseidon2Permutation.ConsistencyCheck`** (AZ1
`P2/poseidon2_permutation.test.cpp:44-61`), a vector the test's comment says was extracted from
the code under test. -/
theorem consistency_vector : permutation consistencyInput = consistencyOutput :=
  permutation_eq_of_dense (by decide)

/-- The input `(1, 2, 3, 0x0a0000000000000000)` of the bb.js test "from Noir" (AZ1
`yarn-project/foundation/src/crypto/poseidon/index.test.ts:16`). -/
def bbjsNoirInput : State := ![1, 2, 3, 0x0a0000000000000000]

/-- Its expected output (AZ1 `yarn-project/foundation/src/crypto/poseidon/index.test.ts:17-22`). -/
def bbjsNoirOutput : State :=
  ![0x0369007aa630f5dfa386641b15416ecb16fb1a6f45b1acb903cb986b221a891c,
    0x1919fd474b4e2e0f8e0cf8ca98ef285675781cbd31aa4807435385d28e4c02a5,
    0x0810e7e9a1c236aae4ebff7d3751d9f7346dc443d1de863977d2b81fe8c557f4,
    0x1f4a188575e29985b6f8ad03afc1f0759488f8835aafb6e19e06160fb64d3d4a]

/-- **The model reproduces the bb.js test vector "from Noir"** (AZ1
`yarn-project/foundation/src/crypto/poseidon/index.test.ts:15-23`). -/
theorem noir_vector_bbjs : permutation bbjsNoirInput = bbjsNoirOutput :=
  permutation_eq_of_dense (by decide)

/-- The expected output for the all-zero input (NR1 `NS/poseidon2.rs:149-152`; NRN
`NS/poseidon2.rs:636-641`). -/
def zerosOutput : State :=
  ![0x18dfb8dc9b82229cff974efefc8df78b1ce96d9d844236b496785c698bc6732e,
    0x095c230d1d37a246e8d2d5a63b165fe0fade040d442f61e25f0590e5fb76f839,
    0x0bb9545846e1afa4fa3c97414a60a20fc4949f537a68cceca34c5ce71e28aa59,
    0x18a4f34c9c6f99335ff7638b82aeed9018026618358873c982bbdde265b2ed6d]

/-- **The model reproduces Noir's all-zeros case** (NR1 `NS/poseidon2.rs:141-154`, expected
outputs from `zkhash` `0.2.0`; also NRN `smoke_test`, `NS/poseidon2.rs:631-643`). -/
theorem zkhash_zeros : permutation ![0, 0, 0, 0] = zerosOutput :=
  permutation_eq_of_dense (by decide)

/-- `u128::MAX` in every lane (NR1 `NS/poseidon2.rs:173-176`). -/
def u128MaxInput : State :=
  ![0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff,
    0xffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffff]

/-- Its expected output (NR1 `NS/poseidon2.rs:179-182`). -/
def u128MaxOutput : State :=
  ![0x1452d1d69a606fb2f6aff10fa4c73ea7486ac4bd59b3557b52311effb283a261,
    0x2433004a0ede6798ef76b637f9e2a0eab454d70b7433a9ab18512d5a980890a9,
    0x05a2ecd90756dd7dbd1840b0f252e490a73594cd103b56f6a3b1add8f38449be,
    0x1d5b91141464c8b36f830f33b7ba06bea37d309a7a5e63a91100bb23c55168f1]

/-- **The model reproduces Noir's `u128::MAX` case** (NR1 `NS/poseidon2.rs:170-184`). -/
theorem zkhash_u128_max : permutation u128MaxInput = u128MaxOutput :=
  permutation_eq_of_dense (by decide)

/-- `p - 1` in every lane (NR1 `NS/poseidon2.rs:188-191`). -/
def pSubOneInput : State :=
  ![0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000,
    0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000,
    0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000,
    0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000]

theorem pSubOneInput_eq : pSubOneInput = fun _ => -1 := by
  decide

/-- Its expected output (NR1 `NS/poseidon2.rs:194-197`). -/
def pSubOneOutput : State :=
  ![0x1b18e6ca21a1e9b15d65f0b5861ede5ff20db8fa3722531823d0c817d69d945d,
    0x0afb50ea6867b1cb2d9d1eac935af746bc7a780e181a1e6ae9b768c9cba68878,
    0x0a521a22ca614e65b877d0676652fb60e90a11b462f9846a08e811d95272a9d8,
    0x2369f077784e0aea99ee3dc6b7b01612af7f80d7f08b755f9f116e2885ee367f]

/-- **The model reproduces Noir's `p - 1` case** (NR1 `NS/poseidon2.rs:185-199`). -/
theorem zkhash_p_sub_one : permutation pSubOneInput = pSubOneOutput :=
  permutation_eq_of_dense (by decide)

/-- Four full-width values (NR1 `NS/poseidon2.rs:203-206`), each below `p`. -/
def arbitraryInput : State :=
  ![0x123456789abcdef00fedcba987654321123456789abcdef00fedcba987654321,
    0x2718281828459045235360287471352662497757247093699959574966967627,
    0x1414213562373095048801688724209698078569671875376948073176679737,
    0x0b172182839274f8e5d4c3b2a1908070605040302010ffeeddccbbaa99887766]

/-- Its expected output (NR1 `NS/poseidon2.rs:209-212`). -/
def arbitraryOutput : State :=
  ![0x1c68b20a2080bcc11a2b6f38a46f8270c3ce1dcd40cf8a16626e1cc936e90d56,
    0x22fdad6f2e2aed646be444efb2ae2eaacd49f0440c846f4882f8b013c01c792c,
    0x1726c0b52c59e7008dbb710a8d3046214257d997a6e7870f46e7dfe5c6729378,
    0x03b4a4b3b3694b4efaf50186e75062f30d3ff4b73d95cab554763b7e19de8ba0]

/-- **The model reproduces Noir's full-width case** (NR1 `NS/poseidon2.rs:200-214`). -/
theorem zkhash_arbitrary : permutation arbitraryInput = arbitraryOutput :=
  permutation_eq_of_dense (by decide)

/-! ### Negative controls -/

/-- The transposed external layer, `x ↦ hlMat4ᵀ x`, which reads the rows of `M4` as columns. -/
def externalT : State ≃ₗ[F] State := hlMat4TEquiv F two_ne_zero_F

/-- The transposed layer on runner states. -/
def mat4T (x : Dense) : Dense :=
  ⟨5 * x.x0 + 4 * x.x1 + x.x2 + x.x3, 7 * x.x0 + 6 * x.x1 + 3 * x.x2 + x.x3,
    x.x0 + x.x1 + 5 * x.x2 + 4 * x.x3, 3 * x.x0 + x.x1 + 7 * x.x2 + 6 * x.x3⟩

theorem mat4T_toState (x : Dense) : (mat4T x).toState = externalT x.toState := by
  rw [externalT, hlMat4TEquiv_apply, hlMat4_transpose_mulVec]
  funext i
  fin_cases i <;> rfl

/-- **Negative control: the transposed matrix.** With `hlMat4ᵀ` as external layer (including the
initial layer), the deployed internal layer and the deployed constants, the vector fails. -/
theorem test_vector_fails_transposed :
    permutationWith externalT internal values testVectorInput ≠ testVectorOutput :=
  permutationWith_ne_of_dense mat4T_toState internalDense_toState values_partialRowsAtZero
    (by decide)

/-- An internal step `diag(dv) + J` on runner states is the linear equivalence
`diagPlusOnesEquiv 1 dv`. -/
theorem internalDense_ofState_toState (dv : Fin 4 → F) (h1 : ∀ i, dv i ≠ 0)
    (h2 : 1 + ∑ i, (dv i)⁻¹ ≠ 0) (x : Dense) :
    (internalDense (Dense.ofState dv) x).toState =
      diagPlusOnesEquiv 1 dv one_ne_zero h1 h2 x.toState := by
  funext i
  rw [internalDense_toState_apply, Dense.toState_ofState, diagPlusOnesEquiv_apply,
    diagPlusOnes_apply, one_mul]

/-- The diagonal `d + 1`, the true diagonal entries of `diag(d) + J`. -/
def diagSucc : Fin 4 → F :=
  ![7626475329478847982857743246276194948757851985510858890691733676098590062312,
    5498568565063849786384470689962419967523752476452646391422913716315471115276,
    148936322117705719734052984176402258788283488576388928671173547788498414614,
    15456385653678559339152734484033356164266089951521103188900320352052358038156]

theorem diagSucc_eq : diagSucc = fun i => internalDiag i + 1 := by
  decide

/-- The inverses of the entries of `diagSucc`, computed outside Lean. -/
def diagSuccInv : Fin 4 → F :=
  ![4477242684478655269323582166481195769957145347925266031312120679854243074605,
    18262526164874756191984089568848271843885519187978169604897297487814761813063,
    5565065278157879101795714696999355495918070273283930504660044077250703758306,
    9127211096148906969983932785981781093995304931709918559998462122264927395014]

theorem diagSucc_mul_inv : ∀ i, diagSucc i * diagSuccInv i = 1 := by
  decide

theorem one_add_sum_inv_diagSucc : 1 + ∑ i, (diagSucc i)⁻¹ ≠ 0 := by
  rw [sum_inv_eq_of_mul_eq_one diagSucc_mul_inv, Fin.sum_univ_four]
  decide

/-- The internal layer `diag(d + 1) + J`. -/
def internalSucc : State ≃ₗ[F] State :=
  diagPlusOnesEquiv 1 diagSucc one_ne_zero (ne_zero_of_mul_eq_one diagSucc_mul_inv)
    one_add_sum_inv_diagSucc

/-- **Negative control: `diag(d + 1) + J`.** With the stored array increased by one in the
internal layer, the deployed external layer and constants, the vector fails. -/
theorem test_vector_fails_diag_succ :
    permutationWith external internalSucc values testVectorInput ≠ testVectorOutput :=
  permutationWith_ne_of_dense mat4_toState
    (internalDense_ofState_toState diagSucc (ne_zero_of_mul_eq_one diagSucc_mul_inv)
      one_add_sum_inv_diagSucc) values_partialRowsAtZero (by decide)

/-- The diagonal `d - 1`: the internal layer `diag(d - 1) + J` has diagonal entries `d_i`, the
reading of the stored array as the true diagonal of the matrix. -/
def diagPred : Fin 4 → F :=
  ![7626475329478847982857743246276194948757851985510858890691733676098590062310,
    5498568565063849786384470689962419967523752476452646391422913716315471115274,
    148936322117705719734052984176402258788283488576388928671173547788498414612,
    15456385653678559339152734484033356164266089951521103188900320352052358038154]

theorem diagPred_eq : diagPred = fun i => internalDiag i - 1 := by
  decide

/-- The inverses of the entries of `diagPred`, computed outside Lean. -/
def diagPredInv : Fin 4 → F :=
  ![11915730992329771121560078833671641084410844673951784244045821024783352963164,
    19247403556527059987028632643328904953872001250641752090323931961255433322871,
    20966171690033149846327997411552857080539593475915155610399410766171648112014,
    10015169947022825585478556188136581442721485971158658069624710314719458007870]

theorem diagPred_mul_inv : ∀ i, diagPred i * diagPredInv i = 1 := by
  decide

theorem one_add_sum_inv_diagPred : 1 + ∑ i, (diagPred i)⁻¹ ≠ 0 := by
  rw [sum_inv_eq_of_mul_eq_one diagPred_mul_inv, Fin.sum_univ_four]
  decide

/-- The internal layer `diag(d - 1) + J`. -/
def internalPred : State ≃ₗ[F] State :=
  diagPlusOnesEquiv 1 diagPred one_ne_zero (ne_zero_of_mul_eq_one diagPred_mul_inv)
    one_add_sum_inv_diagPred

/-- **Negative control: the stored array read as the true diagonal.** With the internal layer
`diag(d - 1) + J`, whose diagonal entries are the stored values, the deployed external layer and
constants, the vector fails. -/
theorem test_vector_fails_diag_pred :
    permutationWith external internalPred values testVectorInput ≠ testVectorOutput :=
  permutationWith_ne_of_dense mat4_toState
    (internalDense_ofState_toState diagPred (ne_zero_of_mul_eq_one diagPred_mul_inv)
      one_add_sum_inv_diagPred) values_partialRowsAtZero (by decide)

/-- **Negative control: the initial external layer is needed.** The `64` rounds alone do not
send the input to the expected output. -/
theorem test_vector_fails_skip_initial :
    Hades.execute rounds testVectorInput 64 ≠ testVectorOutput :=
  execute_ne_of_dense mat4_toState internalDense_toState values_partialRowsAtZero (by decide)

/-! ### Exactness -/

/-- **`251` is the largest `d` with `4 * 2^d ≤ p`.** -/
theorem whole_bits_succ_fails : ¬ 4 * 2 ^ 252 ≤ Fintype.card F := by
  rw [field_card]
  decide

set_option exponentiation.threshold 9000 in
/-- **`8554` is the largest exponent the exact trail ratio gives.** `2^8555 * 4^34 ≤ p^34`
fails; with `sharp_exponent_bound`, `8554` is the largest `E` with `2^E * 4^34 ≤ p^34`. -/
theorem sharp_exponent_succ_fails :
    ¬ 2 ^ 8555 * 4 ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 5 + 4 % 2 + 4 % 2 + 56 / 4) := by
  decide

set_option exponentiation.threshold 2000 in
/-- **`1006` is the largest exponent the differential ratio gives.** `2^1007 * 4^4 ≤ p^4`
fails; with `differential_sharp_exponent_bound`, `1006` is the largest `E` with
`2^E * 4^4 ≤ p^4`. -/
theorem differential_sharp_exponent_succ_fails : ¬ 2 ^ 1007 * 4 ^ 4 ≤ modulus ^ 4 := by
  decide

/-- The external layer sends `e_0` to the first column `(5, 4, 1, 1)` of `hlMat4`. -/
theorem external_unit : external (Pi.single 0 1) = ![5, 4, 1, 1] := by
  rw [external_apply]
  decide

/-- **The bound `5` of `external_branch` is attained**: `e_0` and its image have weight
`1 + 4 = 5`. -/
theorem external_not_branch_six : ¬ isBranchBound id external 6 := by
  intro h
  have hw := h (Pi.single 0 1) (by decide)
  rw [external_unit] at hw
  revert hw
  decide

/-- **One dimension of differences stays inactive through three consecutive partial rounds**
(`finrank_internal_inactive` at `r = 3`). -/
theorem finrank_inactive_three :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 4)) 3) = 1 :=
  finrank_internal_inactive (by norm_num)

/-! ### Cross-checks -/

/-- The array `internal_matrix` of AZ1 `P2/poseidon2_params.hpp:31-56`, declared but not read by
the permutation. -/
def declaredInternalMatrix : Matrix (Fin 4) (Fin 4) F :=
  !![0x10dc6e9c006ea38b04b1e03b4bd9490c0d03f98929ca1d7fb56821fd19d3b6e8, 1, 1, 1;
     1, 0x0c28145b6a44df3e0149b3d0a30b3bb599df9756d4dd9b84a86b38cfb45a740c, 1, 1;
     1, 1, 0x00544b8338791518b2c7645a50392798b21f75bb60e3596170067d00141cac16, 1;
     1, 1, 1, 0x222c01175718386f2e2e82eb122789e352e105a3b8fa852613bc534433ee428c]

/-- **The declared `internal_matrix` is `diag(d) + J`**, the matrix of `internal`
(`internal_eq_mulVec`): its diagonal entries are `d_i + 1`. -/
theorem declaredInternalMatrix_eq :
    declaredInternalMatrix = Matrix.diagonal internalDiag + Matrix.of fun _ _ => (1 : F) := by
  decide

/-- All four stored entries `d_i` of `internalDiag` are pairwise distinct in `F` (equivalently,
so are the diagonal entries `d_i + 1` of `diag(d) + J`). -/
theorem internalDiag_injective : Function.Injective internalDiag := by
  intro i j h
  revert i j
  decide

/-- The `32` constants of the full rounds are nonzero. -/
theorem full_constants_ne_zero : ∀ n : Fin 64, (n.val < 4 ∨ 60 ≤ n.val) → ∀ i : Fin 4,
    values n.val i ≠ 0 := by
  decide

/-- The `56` constants of the partial rounds at coordinate `0` are nonzero. -/
theorem partial_constants_ne_zero : ∀ n : Fin 56, values (4 + n.val) 0 ≠ 0 := by
  decide

/-- The transposed control uses a different matrix: `hlMat4` is not symmetric. -/
theorem hlMat4_ne_transpose : hlMat4 F ≠ (hlMat4 F).transpose := by
  decide

/-- **The two declarations of the HorizenLabs matrix agree**: `Poseidon2.MDS4Checks.hlMat4`, the
integer matrix that `WideTrail.Algebra.Checks.MDS4` shows differs from Plonky3's `m4`, is
`hlMat4 ℤ` of `WideTrail.Poseidon2.HorizenLabsM4`. -/
theorem mds4Checks_hlMat4_eq : MDS4Checks.hlMat4 = hlMat4 ℤ := by
  decide

end Poseidon2.AztecBN254.Checks

/-! ### Axiom footprints: `HorizenLabsM4.lean` -/

/-- info: 'Poseidon2.hlMat4_isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4_isMDS

/-- info: 'Poseidon2.hlMat4_isMDS_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4_isMDS_iff

/-- info: 'Poseidon2.hlMat4_isMDS_of_minors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4_isMDS_of_minors

/-- info: 'Poseidon2.natAbs_hlMinor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.natAbs_hlMinor_mem

/-- info: 'Poseidon2.hlMat4_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4_det

/-- info: 'Poseidon2.hlMat4_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4_isBranchBound

/-- info: 'Poseidon2.hlMat4Equiv_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4Equiv_isBranchBound

/-- info: 'Poseidon2.hlMat4Equiv_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4Equiv_symm_apply

/-- info: 'Poseidon2.hlMat4_mul_hlMat4Inv8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.hlMat4_mul_hlMat4Inv8

/-! ### Axiom footprints: `AztecBN254.lean` and `AztecBN254Execution.lean` -/

/-- info: 'Poseidon2.AztecBN254.external_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.external_symm_apply

/-- info: 'Poseidon2.AztecBN254.external_mds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.external_mds

/-- info: 'Poseidon2.AztecBN254.external_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.external_branch

/-- info: 'Poseidon2.AztecBN254.internalDiag_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.internalDiag_ne_zero

/-- info: 'Poseidon2.AztecBN254.one_add_sum_inv_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.one_add_sum_inv_ne_zero

/-- info: 'Poseidon2.AztecBN254.internalDiag_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.internalDiag_injOn

/-- info: 'Poseidon2.AztecBN254.internal_eq_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.internal_eq_mulVec

/-- info: 'Poseidon2.AztecBN254.partial_constants_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.partial_constants_zero

/-- info: 'Poseidon2.AztecBN254.rounds_apply_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.rounds_apply_prefix

/-- info: 'Poseidon2.AztecBN254.rounds_apply_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.rounds_apply_partial

/-- info: 'Poseidon2.AztecBN254.rounds_apply_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.rounds_apply_suffix

/-- info: 'Poseidon2.AztecBN254.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.permutation_bijective

/-- info: 'Poseidon2.AztecBN254.permutation_bijective_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.permutation_bijective_general

/-- info: 'Poseidon2.AztecBN254.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.activity

/-- info: 'Poseidon2.AztecBN254.activity_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.activity_general

/-- info: 'Poseidon2.AztecBN254.internal_inactive_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.internal_inactive_trivial

/-- info: 'Poseidon2.AztecBN254.finrank_internal_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.finrank_internal_inactive

/-- info: 'Poseidon2.AztecBN254.internal_inactive_three_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.internal_inactive_three_ne_bot

/-- info: 'Poseidon2.AztecBN254.activity_with_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.activity_with_partial

/-- info: 'Poseidon2.AztecBN254.activity_with_partial_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.activity_with_partial_general

/-- info: 'Poseidon2.AztecBN254.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability

/-- info: 'Poseidon2.AztecBN254.independent_key_probability_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_general

/-- info: 'Poseidon2.AztecBN254.probability_exponent' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.probability_exponent

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_with_partial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_with_partial

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_with_partial_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_with_partial_general

/-- info: 'Poseidon2.AztecBN254.probability_exponent_with_partial' does not depend on any axioms -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.probability_exponent_with_partial

/-- info: 'Poseidon2.AztecBN254.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_exact

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_exact_general

/-- info: 'Poseidon2.AztecBN254.sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.sharp_exponent_bound

/-- info: 'Poseidon2.AztecBN254.independent_key_probability_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_sharp

/--
info: 'Poseidon2.AztecBN254.independent_key_probability_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_probability_sharp_general

/-- info: 'Poseidon2.AztecBN254.independent_key_differential_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_differential_exact

/--
info: 'Poseidon2.AztecBN254.independent_key_differential_exact_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_differential_exact_general

/-- info: 'Poseidon2.AztecBN254.differential_sharp_exponent_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.differential_sharp_exponent_bound

/-- info: 'Poseidon2.AztecBN254.independent_key_differential_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_differential_sharp

/--
info: 'Poseidon2.AztecBN254.independent_key_differential_sharp_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.independent_key_differential_sharp_general

/-- info: 'Poseidon2.AztecBN254.sboxDense_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.sboxDense_eq

/-- info: 'Poseidon2.AztecBN254.mat4_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.mat4_toState

/-- info: 'Poseidon2.AztecBN254.internalDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.internalDense_toState

/-- info: 'Poseidon2.AztecBN254.roundDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.roundDense_toState

/-- info: 'Poseidon2.AztecBN254.permutationDense_toState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.permutationDense_toState

/-- info: 'Poseidon2.AztecBN254.permutation_eq_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.permutation_eq_of_dense

/-- info: 'Poseidon2.AztecBN254.permutation_ne_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.permutation_ne_of_dense

/-! ### Axiom footprints: this file -/

/-- info: 'Poseidon2.AztecBN254.Checks.test_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.test_vector

/-- info: 'Poseidon2.AztecBN254.Checks.consistency_literal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.consistency_literal_eq

/-- info: 'Poseidon2.AztecBN254.Checks.consistency_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.consistency_vector

/-- info: 'Poseidon2.AztecBN254.Checks.noir_vector_bbjs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.noir_vector_bbjs

/-- info: 'Poseidon2.AztecBN254.Checks.zkhash_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.zkhash_zeros

/-- info: 'Poseidon2.AztecBN254.Checks.zkhash_u128_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.zkhash_u128_max

/-- info: 'Poseidon2.AztecBN254.Checks.zkhash_p_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.zkhash_p_sub_one

/-- info: 'Poseidon2.AztecBN254.Checks.zkhash_arbitrary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.zkhash_arbitrary

/-- info: 'Poseidon2.AztecBN254.Checks.test_vector_fails_transposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.test_vector_fails_transposed

/-- info: 'Poseidon2.AztecBN254.Checks.test_vector_fails_diag_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.test_vector_fails_diag_succ

/-- info: 'Poseidon2.AztecBN254.Checks.test_vector_fails_diag_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.test_vector_fails_diag_pred

/-- info: 'Poseidon2.AztecBN254.Checks.test_vector_fails_skip_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.test_vector_fails_skip_initial

/-- info: 'Poseidon2.AztecBN254.Checks.whole_bits_succ_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.whole_bits_succ_fails

/-- info: 'Poseidon2.AztecBN254.Checks.sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.sharp_exponent_succ_fails

/-- info: 'Poseidon2.AztecBN254.Checks.differential_sharp_exponent_succ_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.differential_sharp_exponent_succ_fails

/-- info: 'Poseidon2.AztecBN254.Checks.external_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.external_unit

/-- info: 'Poseidon2.AztecBN254.Checks.external_not_branch_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.external_not_branch_six

/-- info: 'Poseidon2.AztecBN254.Checks.finrank_inactive_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.finrank_inactive_three

/-- info: 'Poseidon2.AztecBN254.Checks.declaredInternalMatrix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.declaredInternalMatrix_eq

/-- info: 'Poseidon2.AztecBN254.Checks.internalDiag_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.internalDiag_injective

/-- info: 'Poseidon2.AztecBN254.Checks.full_constants_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.full_constants_ne_zero

/-- info: 'Poseidon2.AztecBN254.Checks.partial_constants_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.partial_constants_ne_zero

/-- info: 'Poseidon2.AztecBN254.Checks.hlMat4_ne_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.hlMat4_ne_transpose

/-- info: 'Poseidon2.AztecBN254.Checks.mds4Checks_hlMat4_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.mds4Checks_hlMat4_eq

/-- info: 'Poseidon2.AztecBN254.Checks.pSubOneInput_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.pSubOneInput_eq

/-- info: 'Poseidon2.AztecBN254.Checks.diagSucc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.diagSucc_eq

/-- info: 'Poseidon2.AztecBN254.Checks.diagPred_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.AztecBN254.Checks.diagPred_eq
