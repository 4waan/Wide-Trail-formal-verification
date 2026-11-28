/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon.StarknetExecution
import WideTrail.Poseidon.StarknetCompressed

/-!
# Checks for the Starknet Poseidon certificate

`WideTrail.Poseidon.Starknet` models Starknet's Poseidon permutation. The checks below test that
model against the published permutation-level known-answer vectors, record which readings of the
code they rule out, and show that the exponents and the branch number of the certificate cannot
be improved. Every finite check is kernel `decide`. The whole-permutation checks run on the
runner of `WideTrail.Poseidon.StarknetExecution`, and its transfer lemmas carry the computed
values over to the specification `permutation` (or `permutationWith` for a control).

## Known-answer vectors

These are the three distinct permutation-level inputs that the sources publish. All of them use
the deployed constants, the table `roundConstants` (directly, or through the compressed table,
which defines the same permutation, `compressedPermutation_eq`). Inputs and outputs are copied
from the sources.

* `zero_vector`: `(0, 0, 0)`. The hexadecimal output of eqlabs/pathfinder commit
  `00a1a74a90a7b8a7f1d07ac3e616be1cb39cf8f1` `crates/stark_poseidon/src/poseidon.rs:105-120`
  (`test_poseidon`, the unoptimised `permute`) and `:122-137` (`test_poseidon_comp`, the
  compressed `permute_comp`); the source comment credits starkware-industries/poseidon. The same
  output in decimal is the test vector of CryptoExperts/poseidon commit
  `68a88df9cb894fe1e0ee8b1b1b5825602c83635a` `sage/poseidon.sage:125-129`
  (`zeroOutput_eq_cryptoexperts`).
* `lambdaworks_vector`: `(9, 11, 2)`, `test_hades_permutation` of starknet-types-core `1.0.0`
  `src/hash/poseidon.rs:91-109` and of lambdaworks-crypto `0.13.0`
  `src/hash/poseidon/mod.rs:107-135`, the code that cairo-vm `4.0.0` runs for its Poseidon
  builtin. Both run the compressed table.
* `corelib_vector`: `(1, 2, 3)`, `test_poseidon_hades_permutation` of starkware-libs/cairo tag
  `v2.22.0` (commit `118efdadf76745701dbf019ef9ead25b2cbea29b`)
  `corelib/src/test/hash_test.cairo:15-33`, which calls the `hades_permutation` libfunc.

The `23` hash-level vectors that the same code bases publish (`poseidon_hash`,
`poseidon_hash_single`, `poseidon_hash_many`) are out of scope: no sponge is modelled.

## Negative controls

* `*_fails_sbox_first`: with the partial S-box on coordinate `0` instead of `2`, none of the
  three vectors is reproduced.
* `*_fails_plus_two`: with the last entry of `M` read as `+2`, as the comments at starknet-crypto
  `0.6.2` `src/poseidon_hash.rs:117` and pathfinder `00a1a74` `poseidon.rs:9` print it, none of
  the three vectors is reproduced.
* `lambdaworks_vector_fails_initial_layer`, `corelib_vector_fails_initial_layer`: with an extra
  `M` in front of the rounds (a Poseidon2-style initial layer), the nonzero vectors are not
  reproduced; `zero_vector_blind_to_initial_layer`: the zero vector cannot detect that mistake,
  since `M 0 = 0`.
* `lambdaworks_vector_fails_partial_at_two_only`: the unoptimised table, with only the
  coordinate-`2` constant added in the partial rounds (the reading under which partial rounds
  add their constant only at the S-box coordinate), does not reproduce the `(9, 11, 2)` vector.
  The partial-round constants off coordinate `2` are nonzero (`values_partial_ne_zero`).
* `lambdaworks_vector_fails_transposed`: the table read column-major, entry `3 n + j` taken as
  `C[(3 n + j) % 91][(3 n + j) / 91]` instead of `C[n][j]`, does not reproduce the `(9, 11, 2)`
  vector: the index `3 i + j` of `poseidon_utils.py:100` is row-major.

The docstring reading of the constants, `sha256("Poseidon" ++ toString k)` (cairo-lang
`v0.14.0.1` `src/starkware/cairo/common/poseidon_utils.py:18-20`), is not tested here: it would
need another `273` literals. Outside Lean, it reproduces none of the five permutation-level
vectors.

## Exactness and cross-checks

* `whole_bits_succ_fails`: `2 * 2^251 > p`, so `250` is the largest `d` with `2 * 2^d ≤ p`.
* `outer_sharp_exponent_bound`, `outer_sharp_exponent_succ_fails`,
  `sharp_exponent_succ_fails`, `differential_sharp_exponent_succ_fails`: the exact ratios give
  the exponents `4000`, `10750` and `750` and no more. Keeping the ratio `p / 2` exact therefore
  gains nothing over the whole-bit charge `250` here.
* `mds_unit`, `mds_not_branch_five`: `e_0` is sent to `(3, 1, 1)`, weight `1 + 3`, so the branch
  number of `M` is exactly `4`.
* `mdsInt_minors_one`, `mdsInt_minors_two`, `mdsInt_det`: over `ℤ`, the `9` entries of `M` lie in
  `{-2, -1, 1, 3}`, its `9` minors of size two in `{-7, -4, -3, 1, 2}`, and `det M = 8`; all
  `19` minors are nonzero with prime factors among `2`, `3`, `7`.
* `finrank_inactive_one`, `finrank_inactive_two`: two and one dimensions of differences stay
  inactive through one and two consecutive partial rounds.
* `values_ne_zero`, `values_partial_ne_zero`: none of the `273` constants is zero.
* `values_zero_eq_air`, `values_four_two_eq_air`: row `0` and the constant `C[4][2]` are constants
  of the Starknet-layout STARK AIR (cairo-lang `v0.14.0.1`
  `src/starkware/cairo/stark_verifier/air/layouts/starknet/autogenerated.cairo:1617-1639`,
  `:1736`).
* `modulus_hex`, `inverseExponent_eq`, `modulus_sub_one_mod_three`, `mdsMatrix_symmetric_ne`.

## What is not claimed

The known-answer tests check single inputs. They show that the model computes the outputs that
the sources assert; they do not prove that model and code agree on every input. Nothing here is a
comparison with a built binary, with the Cairo VM, with the AIR, or with a sponge, and nothing
here strengthens the security claims of `WideTrail.Poseidon.Starknet`.
-/

set_option autoImplicit false
-- Each `decide` on the runner unfolds all rounds at once; the default depth is too small.
set_option maxRecDepth 4000

namespace Poseidon.Starknet.Checks

/-! ### Known-answer vectors -/

/-- The all-zero input. -/
def zeroInput : State := ![0, 0, 0]

/-- The expected output for the all-zero input, the hexadecimal literals of pathfinder `00a1a74`
`crates/stark_poseidon/src/poseidon.rs:109-111` (and `:126-128`). -/
def zeroOutput : State :=
  ![0x79E8D1E78258000A28FC9D49E233BC6852357968577B1E386550ED6A9086133,
    0x3840D003D0F3F96DBB796FF6AA6A63BE5B5404B91CCAABCA256154CBB6FB984,
    0x1EB39DA3F7D3B04142D0AC83D9DA00C9325A61FB2EF326E50B70EAA8A3C7CC7]

/-- The same output in the decimal of CryptoExperts `68a88df` `sage/poseidon.sage:126-129`. -/
theorem zeroOutput_eq_cryptoexperts : zeroOutput =
    ![3446325744004048536138401612021367625846492093718951375866996507163446763827,
      1590252087433376791875644726012779423683501236913937337746052470473806035332,
      867921192302518434283879514999422690776342565400001269945778456016268852423] := by
  decide

/-- **The model reproduces the zero vector** of pathfinder `00a1a74`
`crates/stark_poseidon/src/poseidon.rs:105-137` and CryptoExperts `68a88df`
`sage/poseidon.sage:125-129`. -/
theorem zero_vector : permutation zeroInput = zeroOutput :=
  permutation_eq_of_dense (by decide)

/-- The input `(0x9, 0xb, 0x2)` of starknet-types-core `1.0.0` `src/hash/poseidon.rs:93-97` and
lambdaworks-crypto `0.13.0` `src/hash/poseidon/mod.rs:110-114`. -/
def lambdaworksInput : State := ![0x9, 0xb, 0x2]

/-- Its expected output (starknet-types-core `1.0.0` `src/hash/poseidon.rs:98-105`;
lambdaworks-crypto `0.13.0` `src/hash/poseidon/mod.rs:119-130`). -/
def lambdaworksOutput : State :=
  ![0x510f3a3faf4084e3b1e95fd44c30746271b48723f7ea9c8be6a9b6b5408e7e6,
    0x4f511749bd4101266904288021211333fb0a514cb15381af087462fa46e6bd9,
    0x186f6dd1a6e79cb1b66d505574c349272cd35c07c223351a0990410798bb9d8]

/-- **The model reproduces the `(9, 11, 2)` vector** of starknet-types-core `1.0.0`
`src/hash/poseidon.rs:91-109` and lambdaworks-crypto `0.13.0` `src/hash/poseidon/mod.rs:107-135`. -/
theorem lambdaworks_vector : permutation lambdaworksInput = lambdaworksOutput :=
  permutation_eq_of_dense (by decide)

/-- The input `(1, 2, 3)` of cairo `v2.22.0` `corelib/src/test/hash_test.cairo:17`. -/
def corelibInput : State := ![1, 2, 3]

/-- Its expected output (cairo `v2.22.0` `corelib/src/test/hash_test.cairo:18-32`). -/
def corelibOutput : State :=
  ![442682200349489646213731521593476982257703159825582578145778919623645026501,
    2233832504250924383748553933071188903279928981104663696710686541536735838182,
    2512222140811166287287541003826449032093371832913959128171347018667852712082]

/-- **The model reproduces the Cairo corelib vector** (cairo `v2.22.0`
`corelib/src/test/hash_test.cairo:15-33`, the `hades_permutation` libfunc). -/
theorem corelib_vector : permutation corelibInput = corelibOutput :=
  permutation_eq_of_dense (by decide)

/-- The compressed schedule reproduces the three vectors as well (`compressedPermutation_eq`). -/
theorem compressed_vectors :
    compressedPermutation zeroInput = zeroOutput ∧
      compressedPermutation lambdaworksInput = lambdaworksOutput ∧
        compressedPermutation corelibInput = corelibOutput := by
  simp only [compressedPermutation_eq]
  exact ⟨zero_vector, lambdaworks_vector, corelib_vector⟩

/-! ### Negative controls -/

/-- **Negative control: the partial S-box on coordinate `0`.** -/
theorem zero_vector_fails_sbox_first : permutationWith mds {0} values zeroInput ≠ zeroOutput :=
  permutationWith_ne_of_dense dotMod_toState cubeFirst_toState (by decide)

theorem lambdaworks_vector_fails_sbox_first :
    permutationWith mds {0} values lambdaworksInput ≠ lambdaworksOutput :=
  permutationWith_ne_of_dense dotMod_toState cubeFirst_toState (by decide)

theorem corelib_vector_fails_sbox_first :
    permutationWith mds {0} values corelibInput ≠ corelibOutput :=
  permutationWith_ne_of_dense dotMod_toState cubeFirst_toState (by decide)

/-- The matrix with `+2` in its last entry, `[[3, 1, 1], [1, -1, 1], [1, 1, 2]]`, as the comments
at starknet-crypto `0.6.2` `src/poseidon_hash.rs:117` and pathfinder `00a1a74`
`crates/stark_poseidon/src/poseidon.rs:9` print it. Its determinant is `-8` and its inverse is
`-adj / 8`, `adj = [[-3, -1, 2], [-1, 5, -2], [2, -2, -4]]`. -/
def mdsPlusTwo : State ≃ₗ[F] State where
  toFun x := ![3 * x 0 + x 1 + x 2, x 0 - x 1 + x 2, x 0 + x 1 + 2 * x 2]
  invFun y := ![inv8 * (3 * y 0 + y 1 - 2 * y 2), inv8 * (y 0 - 5 * y 1 + 2 * y 2),
    inv8 * (-2 * y 0 + 2 * y 1 + 4 * y 2)]
  left_inv x := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (x 0) * eight_mul_inv8
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (x 1) * eight_mul_inv8
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (x 2) * eight_mul_inv8
  right_inv y := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (y 0) * eight_mul_inv8
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (y 1) * eight_mul_inv8
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination (y 2) * eight_mul_inv8
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- The `+2` matrix on runner states. -/
def dotModPlusTwo (x : Dense) : Dense :=
  ⟨3 * x.x0 + x.x1 + x.x2, x.x0 - x.x1 + x.x2, x.x0 + x.x1 + 2 * x.x2⟩

theorem dotModPlusTwo_toState (x : Dense) :
    (dotModPlusTwo x).toState = mdsPlusTwo x.toState := by
  funext i
  fin_cases i <;> rfl

/-- **Negative control: the `+2` matrix of the comments.** -/
theorem zero_vector_fails_plus_two :
    permutationWith mdsPlusTwo {2} values zeroInput ≠ zeroOutput :=
  permutationWith_ne_of_dense dotModPlusTwo_toState cubeLast_toState (by decide)

theorem lambdaworks_vector_fails_plus_two :
    permutationWith mdsPlusTwo {2} values lambdaworksInput ≠ lambdaworksOutput :=
  permutationWith_ne_of_dense dotModPlusTwo_toState cubeLast_toState (by decide)

theorem corelib_vector_fails_plus_two :
    permutationWith mdsPlusTwo {2} values corelibInput ≠ corelibOutput :=
  permutationWith_ne_of_dense dotModPlusTwo_toState cubeLast_toState (by decide)

/-- **Negative control: an extra initial `M`.** With `M` composed in front of the `91` rounds,
as Poseidon2 does, the `(9, 11, 2)` vector fails. -/
theorem lambdaworks_vector_fails_initial_layer :
    permutation (mds lambdaworksInput) ≠ lambdaworksOutput :=
  permutation_mds_ne_of_dense (by decide)

/-- The same control on the `(1, 2, 3)` vector. -/
theorem corelib_vector_fails_initial_layer : permutation (mds corelibInput) ≠ corelibOutput :=
  permutation_mds_ne_of_dense (by decide)

/-- **The zero vector cannot detect an initial layer**: `M 0 = 0`, so the permutation with an
extra `M` in front sends `(0, 0, 0)` to the same output. -/
theorem zero_vector_blind_to_initial_layer : permutation (mds zeroInput) = zeroOutput := by
  have h : zeroInput = 0 := by
    funext i
    fin_cases i <;> rfl
  rw [h, map_zero, ← h]
  exact zero_vector

/-- The unoptimised table with only the coordinate-`2` constant kept in the partial rounds. -/
def partialAtTwoOnly (n : ℕ) : State :=
  if 4 ≤ n ∧ n < 87 then ![0, 0, values n 2] else values n

/-- **Negative control: dropping the partial-round constants off coordinate `2`.** The
unoptimised table read as if partial rounds added their constant only at the S-box coordinate
fails the `(9, 11, 2)` vector. -/
theorem lambdaworks_vector_fails_partial_at_two_only :
    permutationWith mds {2} partialAtTwoOnly lambdaworksInput ≠ lambdaworksOutput :=
  permutationWith_ne_of_dense dotMod_toState cubeLast_toState (by decide)

/-- The table read column-major: entry `k = 3 n + j` of the flat table is taken as
`C[k % 91][k / 91]`. -/
def transposedValues (n : ℕ) : State := fun j =>
  if h : (3 * n + j.val) / 91 < 3 then values ((3 * n + j.val) % 91) ⟨(3 * n + j.val) / 91, h⟩
  else 0

/-- **Negative control: the table read column-major.** -/
theorem lambdaworks_vector_fails_transposed :
    permutationWith mds {2} transposedValues lambdaworksInput ≠ lambdaworksOutput :=
  permutationWith_ne_of_dense dotMod_toState cubeLast_toState (by decide)

/-! ### Exactness -/

/-- **`250` is the largest `d` with `2 * 2^d ≤ p`.** -/
theorem whole_bits_succ_fails : ¬ 2 * 2 ^ 251 ≤ Fintype.card F := by
  rw [field_card]
  decide

set_option exponentiation.threshold 5000 in
/-- The exact ratio for the `16` S-boxes of the full rounds gives `4000`:
`2^4000 * 2^16 ≤ p^16`. -/
theorem outer_sharp_exponent_bound :
    2 ^ 4000 * 2 ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2) := by
  decide

set_option exponentiation.threshold 5000 in
/-- **`4000` is the largest exponent the exact ratio gives for the full rounds**, the same as
the whole-bit charge of `independent_key_probability`. -/
theorem outer_sharp_exponent_succ_fails :
    ¬ 2 ^ 4001 * 2 ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2) := by
  decide

set_option exponentiation.threshold 11000 in
/-- **`10750` is the largest exponent the exact trail ratio gives.** `2^10751 * 2^43 ≤ p^43`
fails; with `sharp_exponent_bound`, `10750` is the largest `E` with `2^E * 2^43 ≤ p^43`, the
same as the whole-bit exponent of `independent_key_probability_with_partial`. -/
theorem sharp_exponent_succ_fails :
    ¬ 2 ^ 10751 * 2 ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 83 / 3)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 4 + 4 % 2 + 4 % 2 + 83 / 3) := by
  decide

set_option exponentiation.threshold 1000 in
/-- **`750` is the largest exponent the differential ratio gives.** `2^751 * 2^3 ≤ p^3` fails;
with `differential_sharp_exponent_bound`, `750` is the largest `E` with `2^E * 2^3 ≤ p^3`. -/
theorem differential_sharp_exponent_succ_fails : ¬ 2 ^ 751 * 2 ^ 3 ≤ modulus ^ 3 := by
  decide

/-- The linear layer sends `e_0` to the first column `(3, 1, 1)` of `M`. -/
theorem mds_unit : mds (Pi.single 0 1) = ![3, 1, 1] := by
  rw [mds_apply]
  decide

/-- **The bound `4` of `mds_branch` is attained**: `e_0` and its image have weight `1 + 3 = 4`. -/
theorem mds_not_branch_five : ¬ isBranchBound id mds 5 := by
  intro h
  have hw := h (Pi.single 0 1) (by decide)
  rw [mds_unit] at hw
  revert hw
  decide

/-- `M` over `ℤ`. -/
def mdsInt : Matrix (Fin 3) (Fin 3) ℤ := !![3, 1, 1; 1, -1, 1; 1, 1, -2]

/-- The `9` minors of size one of `M` over `ℤ` lie in `{-2, -1, 1, 3}`. -/
theorem mdsInt_minors_one : ∀ a b : Fin 1 → Fin 3,
    (mdsInt.submatrix a b).det ∈ [-2, -1, 1, 3] := by
  intro a b
  rw [Matrix.det_fin_one]
  revert a b
  decide

/-- The `9` minors of size two of `M` over `ℤ` (rows `a 0 < a 1`, columns `b 0 < b 1`) lie in
`{-7, -4, -3, 1, 2}`. -/
theorem mdsInt_minors_two : ∀ a b : Fin 2 → Fin 3, a 0 < a 1 → b 0 < b 1 →
    (mdsInt.submatrix a b).det ∈ [-7, -4, -3, 1, 2] := by
  intro a b
  rw [Matrix.det_fin_two]
  revert a b
  decide

/-- `det M = 8` over `ℤ`. -/
theorem mdsInt_det : mdsInt.det = 8 := by
  rw [Matrix.det_fin_three]
  decide

/-- **Two dimensions of differences stay inactive through one partial round.** -/
theorem finrank_inactive_one :
    Module.finrank F (Hades.inactiveSpace mds.toLinearMap ({2} : Finset (Fin 3)) 1) = 2 :=
  finrank_mds_inactive (by norm_num)

/-- **One dimension of differences stays inactive through two consecutive partial rounds.** -/
theorem finrank_inactive_two :
    Module.finrank F (Hades.inactiveSpace mds.toLinearMap ({2} : Finset (Fin 3)) 2) = 1 :=
  finrank_mds_inactive (by norm_num)

/-! ### Cross-checks -/

/-- None of the `273` round constants is zero. -/
theorem values_ne_zero : ∀ n : Fin 91, ∀ i : Fin 3, values n.val i ≠ 0 := by
  decide

/-- **The partial-round constants off coordinate `2` are nonzero**, so the analogue of
`Poseidon2.BN254.partial_constants_zero` is false for the unoptimised table. -/
theorem values_partial_ne_zero : ∀ n : Fin 83, ∀ i : Fin 3, i ≠ 2 → values (4 + n.val) i ≠ 0 :=
  fun n i _ => values_ne_zero ⟨4 + n.val, by omega⟩ i

/-- Row `0` of the table is the first-round key of the Starknet-layout STARK AIR (cairo-lang
`v0.14.0.1` `src/starkware/cairo/stark_verifier/air/layouts/starknet/autogenerated.cairo:1617-1639`,
`add_first_round_key0..2`). -/
theorem values_zero_eq_air : values 0 =
    ![2950795762459345168613727575620414179244544320470208355568817838579231751791,
      1587446564224215276866294500450702039420286416111469274423465069420553242820,
      1645965921169490687904413452218868659025437693527479459426157555728339600137] := by
  decide

/-- The constant `C[4][2]`, the coordinate-`2` constant of the first partial round, is the
constant of `margin_full_to_partial0` of the same AIR (`autogenerated.cairo:1728-1739`, at
`:1736`). -/
theorem values_four_two_eq_air :
    values 4 2 =
      2121140748740143694053732746913428481442990369183417228688865837805149503386 := by
  decide

/-- The modulus in hexadecimal. -/
theorem modulus_hex :
    modulus = 0x800000000000011000000000000000000000000000000000000000000000001 := by
  decide

/-- The inverse exponent is `(2 p - 1) / 3`. -/
theorem inverseExponent_eq : inverseExponent = (2 * modulus - 1) / 3 := by
  decide

/-- `p - 1 ≡ 1 (mod 3)`, so `gcd(3, p - 1) = 1` and `x ↦ x^3` is a permutation of `F`. -/
theorem modulus_sub_one_mod_three : (modulus - 1) % 3 = 1 ∧ Nat.gcd 3 (modulus - 1) = 1 := by
  decide

/-- `M` is symmetric, so reading it by rows or by columns gives the same layer; and the `+2`
control uses a different matrix. -/
theorem mdsMatrix_symmetric_ne :
    mdsMatrix.transpose = mdsMatrix ∧ mdsMatrix ≠ !![3, 1, 1; 1, -1, 1; 1, 1, 2] := by
  refine ⟨mdsMatrix_transpose, ?_⟩
  decide

end Poseidon.Starknet.Checks
