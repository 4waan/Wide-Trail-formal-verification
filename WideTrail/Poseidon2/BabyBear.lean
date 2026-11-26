/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.BabyBearPrimality
import WideTrail.Poseidon2.Plonky3
import WideTrail.Algebra.PowerSbox
import WideTrail.Differential.PowerMap

/-!
# A certificate for the SP1 `5.2.4` BabyBear Poseidon2 permutation

SP1 `5.2.4` builds its width-sixteen permutation in `poseidon2_init` (`sp1-primitives` `5.2.4`
`src/lib.rs:1106-1124`), of type
`Poseidon2<BabyBear, Poseidon2ExternalMatrixGeneral, DiffusionMatrixBabyBear, 16, 7>` with
`ROUNDS_F = 8` and `ROUNDS_P = 13` (lines 1108-1109); `inner_perm` returns it (`sp1-stark`
`5.2.4` `src/bb31_poseidon2.rs:50-52`). This file fixes every parameter of the generic model
`WideTrail.Poseidon2.Plonky3` to that instance and discharges every hypothesis there by
`decide`, so the theorems below have no remaining premises.

## Parameters

* **Field.** `F = ZMod modulus`, `modulus = 0x78000001 = 2013265921 = 2^31 - 2^27 + 1`
  (`p3-baby-bear` `0.2.3-succinct` `src/baby_bear.rs:16`), prime by the Lucas certificate of
  `WideTrail.Poseidon2.BabyBearPrimality`.
* **S-box.** `x ↦ x^7`: the `D = 7` of the type above, and `sbox_p` is `exp_const_u64::<D>`
  (`p3-poseidon2` `0.2.3-succinct` `src/lib.rs:120-125`). It is a bijection with inverse
  `x ↦ x^1725656503`, since `7 * 1725656503 = 6 (p - 1) + 1`; the code computes the same
  inverse power (`exp_1725656503`, "x^{1/7}", `p3-baby-bear` `src/baby_bear.rs:213-217`). Its
  differential uniformity is at most `6` (`Sbox.pow_seven_uniform`).
* **Schedule.** Width `16`; the initial external layer, four full rounds, thirteen partial
  rounds with the constant and the S-box on coordinate `0` only, four full rounds
  (`p3-poseidon2` `src/lib.rs:177-202`).
* **External layer.** `Plonky3.external`, the block circulant `circ(2 M4, M4, M4, M4)` with
  `M4 = circ(2, 3, 1, 1)`, which `Plonky3.external_eq_mdsLight` identifies with the code's
  `mds_light_permutation`. Its branch number is at least `8` (`external_isBranchBound`).
* **Internal layer.** `x_i ↦ R^{-1} (d_i x_i + ∑_j x_j)` with `R = 2^32`,
  `R^{-1} = 943718400` (`montyInverse`, the code's `MONTY_INVERSE`, `p3-baby-bear`
  `src/poseidon2.rs:27`) and `d = (-2, 1, 2, 4, …, 2^13, 2^15)` (`Plonky3.sp1Diag`;
  `src/poseidon2.rs:29-46`, shifts at lines 48-49). This is the field-level reading of the
  Montgomery code at `src/poseidon2.rs:85-103` given in `WideTrail.Poseidon2.Plonky3`; the
  Sherman–Morrison condition `81917 ≠ 0` holds by `decide`.
* **Round constants.** `roundConstants` lists rows `0` to `20` of `RC_16_30` (`sp1-primitives`
  `5.2.4` `src/lib.rs:18-559`), each raw entry reduced mod `p` (`from_wrapped_u32` is
  `to_monty`, `p3-baby-bear` `src/baby_bear.rs:158-160, 427-429`). The selection is the code's
  (`src/lib.rs:1110-1115`): `drain(4..17)` takes column `0` of rows `4` to `16` as the thirteen
  partial constants, and the eight full rounds read the first eight remaining rows, which are
  rows `0` to `3` and `17` to `20`. So round `n < 21` of the schedule reads row `n` of
  `RC_16_30`, only column `0` for the partial rounds `4 ≤ n < 17`. Columns `1` to `15` of rows
  `4` to `16` are nonzero in `RC_16_30` but never read; they are `0` here
  (`partialRowsAtZero`, by `decide`). With `externalConstants` (rows `0` to `3`, then `17` to
  `20`: the eight rows of the code's `external_round_constants` that the full-round loops read)
  and `internalConstants` (column `0` of rows `4` to `16`, the code's
  `internal_round_constants`), `values_eq_roundValues` shows `values = Plonky3.roundValues 13
  externalConstants internalConstants`, and `rounds_apply_prefix`, `rounds_apply_partial` and
  `rounds_apply_suffix` state each round as the code's round with those constants. After
  `drain(4..17)` the code's `external_round_constants` has `17` rows (rows `0` to `3`, then `17`
  to `29`); `Poseidon2::new` (`p3-poseidon2` `0.2.3-succinct` `src/lib.rs:62-79`) does not check
  its length, and rows `21` to `29` are never read. The values were checked against the crate
  source outside Lean (re-extracted from `src/lib.rs`, with the `drain` selection emulated);
  inside Lean, the table is only related to `externalConstants` and `internalConstants`, which
  are read off the same literals, and its unread entries are shown to vanish.

## Results

* `permutation_bijective`.
* `activity`: two distinct inputs incur at least `32` charged S-box applications, all counted
  in the eight full rounds. `activity_general` is the same for every round-constant table.
* `independent_key_probability`: for every nonzero trail, `keyCount * 2^896 ≤ |F^16|^21` in
  the model with an additional independent uniform key per round (`u = 6`,
  `6 * 2^28 ≤ p`, so `dd = 28`, and `28 * 32 = 896`, `probability_exponent`).
  `independent_key_probability_general` is the same for every round-constant table.
* **The partial rounds contribute nothing to this argument.** A nonzero space of differences,
  of dimension exactly `3` (`finrank_partial_inactive`; the lower bound
  `three_le_finrank_partial_inactive` is from rank–nullity), stays inactive through the thirteen
  consecutive partial rounds (`partial_inactive_ne_bot`); every window `w` for
  which `Plonky3.activity_with_middle` applies has `13 / w = 0`
  (`partial_window_term_eq_zero`); and there are distinct inputs whose actual difference
  charges no S-box in any of the thirteen partial rounds (`exists_pair_partial_free`).
  This is the expected consequence of having fewer partial rounds than the width: thirteen
  linear conditions on a sixteen-dimensional space always leave a nonzero solution. It is not
  an attack, and such pairs still incur the `32` charged S-boxes of the full rounds. The
  round-number comment in the source (`p3-poseidon2` `0.2.3-succinct`
  `src/round_numbers.rs:6-11`) states that, for these parameters, the statistical constraint
  it uses reduces to `RF ≥ 6`, a condition on the full rounds alone; that analysis is not
  checked here.
* `finrank_inactive_eq`: exactly `16 - r` dimensions of differences stay inactive through
  `r ≤ 16` consecutive partial rounds. For `r = 16` the space is `⊥`: `inactive_sixteen` for
  the code's layer, and `inactive_trivial_by_criterion` for `diag d + J`, which is the
  hypothesis of `Plonky3.activity_with_middle` with `w = 16`. The proofs use that the diagonal
  entries off coordinate `0` are pairwise distinct in `F` (`diag_injOn`, by `decide`) and the
  criterion `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff`; no Krylov table is used.

## What is not claimed

The activity counts are lower bounds on charged S-boxes for actual input pairs; they are not
claimed to be attained. The probability statements concern one trail in the model with an
additional independent uniform key per round; they are not statements about the permutation
with its fixed constants, and not about a differential. Nothing is said about subspace-trail
resistance beyond the inactive-space statements here, about algebraic attacks, about the
sponge, duplex or compression constructions built on the permutation, or about equivalence
with the Rust code or the AIR beyond the transcriptions in `WideTrail.Poseidon2.Plonky3` and
the round lemmas here.
-/

set_option autoImplicit false

namespace Poseidon2.BabyBear

open Plonky3

/-! ### The field -/

/-- The BabyBear prime `0x78000001` (`p3-baby-bear` `0.2.3-succinct` `src/baby_bear.rs:16`). -/
def modulus : ℕ := 2013265921

instance : Fact (Nat.Prime modulus) := ⟨prime_2013265921⟩

abbrev F := ZMod modulus
abbrev State := Fin 16 → F

theorem modulus_eq : modulus = 2 ^ 31 - 2 ^ 27 + 1 := by decide

theorem modulus_sub_one : modulus - 1 = 2 ^ 27 * 3 * 5 := by decide

theorem field_card : Fintype.card F = modulus := ZMod.card modulus

/-! ### The S-box -/

/-- The inverse exponent of `x ↦ x^7`: the code's `exp_1725656503`, "used to compute
x^{1/7}" (`p3-baby-bear` `0.2.3-succinct` `src/baby_bear.rs:213-217`). -/
def inverseExponent : ℕ := 1725656503

theorem inverseExponent_positive : 0 < inverseExponent := by decide

theorem seven_positive : 0 < (7 : ℕ) := by decide

theorem inverseExponent_equation : 7 * inverseExponent = (modulus - 1) * 6 + 1 := by decide

theorem fermat (x : F) (hx : x ≠ 0) : x ^ (modulus - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rw [field_card] at h
  exact h

/-- The S-box `x ↦ x^7` (`D = 7`, `sp1-primitives` `5.2.4` `src/lib.rs:1107`), with the
explicit inverse `x ↦ x^1725656503`. -/
def sbox : F ≃ F := Sbox.powerEquivOfFermat modulus 7 inverseExponent 6
  seven_positive inverseExponent_positive inverseExponent_equation fermat

theorem sbox_toFun : (sbox : F → F) = fun x => x ^ 7 := rfl

theorem sbox_symm_toFun : (sbox.symm : F → F) = fun x => x ^ inverseExponent := rfl

theorem seven_ne_zero : (7 : F) ≠ 0 := by decide

/-- The S-box has differential uniformity at most `6`. -/
theorem sbox_uniform : IsDiffUniform sbox 6 := by
  rw [sbox_toFun]
  exact Sbox.pow_seven_uniform seven_ne_zero

/-! ### The linear layers -/

/-- `R^{-1}` for the Montgomery radix `R = 2^32`: the element whose Montgomery representative
is `1`, the code's `MONTY_INVERSE` (`p3-baby-bear` `0.2.3-succinct` `src/poseidon2.rs:27`). -/
def montyInverse : F := 943718400

theorem montyInverse_mul : montyInverse * 2 ^ 32 = 1 := by decide

/-- Every field condition of the generic model, by `decide`: `35 ≠ 0`, `2 ≠ 0`, the
Sherman–Morrison condition `81917 ≠ 0`, and `R^{-1} ≠ 0`. -/
theorem conditions : Conditions montyInverse := ⟨by decide, by decide, by decide, by decide⟩

/-- `2, 3, 5, 7, 11, 17` are nonzero in `F`, so `M4` is MDS over `F` (`m4_isMDS`). -/
theorem m4Primes_ne_zero : ∀ p ∈ m4Primes, (p : F) ≠ 0 := by decide

/-- The first diagonal entry is the code's `BabyBear::ORDER_U32 - 2` (`p3-baby-bear`
`src/poseidon2.rs:30`). -/
theorem diag_zero : sp1Diag F 0 = 2013265919 := by decide

/-- The external layer `circ(2 M4, M4, M4, M4)` (`Plonky3.external`). -/
def external : State ≃ₗ[F] State := Plonky3.external conditions.thirtyFive

/-- The internal layer `x ↦ R^{-1} (diag d + J) x` (`Plonky3.internal`). -/
def internal : State ≃ₗ[F] State :=
  Plonky3.internal montyInverse conditions.scale conditions.two conditions.shermanMorrison

theorem external_eq_mdsLight (x : State) : external x = mdsLight x :=
  Plonky3.external_eq_mdsLight conditions.thirtyFive x

theorem internal_apply (x : State) (i : Fin 16) :
    internal x i = 943718400 * (sp1Diag F i * x i + ∑ j, x j) :=
  rfl

/-- **Branch number at least `8` for the external layer.** -/
theorem external_isBranchBound : isBranchBound id external 8 :=
  Plonky3.external_isBranchBound m4Primes_ne_zero conditions.thirtyFive

/-! ### The pinned round constants -/

/-- Rows `0` to `20` of `RC_16_30` (`sp1-primitives` `5.2.4` `src/lib.rs:18-559`), reduced mod
`p`, with columns `1` to `15` of rows `4` to `16` set to `0`. Round `n` of the schedule uses
row `n`: the full rounds read rows `0` to `3` and `17` to `20`, the partial rounds column `0`
of rows `4` to `16` (`src/lib.rs:1110-1115`). -/
def roundConstants : Fin 21 → State :=
  ![![96748292, 1951698684, 177396853, 719730562, 640767983, 1390633215, 1716033721,
      1606702601, 1746607367, 1466015491, 1498308946, 831109173, 1029197920, 1969905919,
      83412884, 1911782445],
    ![1693593583, 759122502, 1154399525, 1131812921, 1080754908, 53582651, 893583089, 6411452,
      1115338635, 580640471, 1264354339, 842931656, 548879852, 1595288793, 1562381995,
      81826002],
    ![262554421, 1563933798, 1440025885, 184445025, 585385439, 1396647410, 1575877922,
      1290587480, 137125468, 765010148, 633675867, 24537442, 560123907, 1895729703, 541515871,
      1783382863],
    ![628590563, 1022477421, 1659530405, 245668751, 12194511, 201609705, 286217151, 66943721,
      506306261, 1067433949, 748735911, 1244250808, 606038199, 1169474910, 73007766, 558938232],
    ![1196780786, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![36046858, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1492041470, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1864954859, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![883677154, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1765843422, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1418914503, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1404382774, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![859661334, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1548195514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![104929687, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![178643863, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1619872446, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![130182653, 742680828, 542600513, 802837101, 1931786340, 31204919, 1709908013, 925103122,
      1627133772, 1374470239, 177883755, 624229761, 209862198, 276092925, 1820102609,
      974546524],
    ![1293393192, 221548340, 1188782305, 223782844, 235714646, 296520220, 10135706,
      1265611492, 8872228, 575851471, 1612560780, 1913391015, 1305283056, 578597757,
      188109355, 191192067],
    ![1564209905, 140931974, 446421108, 857368568, 1375012945, 1529454825, 306140690,
      842312378, 1246997295, 1011032842, 1915270363, 1218245412, 466048099, 976561834,
      814378556, 13244079],
    ![1165280628, 1203983801, 1801474112, 1919627044, 600240215, 773269071, 486685186,
      227516968, 1415023565, 502840102, 199116516, 510217063, 166444818, 1430745893,
      1376516190, 1775891321]]

/-- The round-constant table as a schedule input: row `n` for `n < 21`, zero afterwards. -/
def values (n : ℕ) : State := if h : n < 21 then roundConstants ⟨n, h⟩ else 0

/-- **The partial rows vanish off coordinate `0`.** The code adds a partial-round constant to
`state[0]` only (`p3-poseidon2` `0.2.3-succinct` `src/lib.rs:191`). -/
theorem partialRowsAtZero : PartialRowsAtZero 13 values := by
  have h : ∀ j : Fin 13, ∀ i : Fin 16, i ≠ 0 → values (4 + j.val) i = 0 := by decide
  intro j hj i hi
  exact h ⟨j, hj⟩ i hi

/-- The eight rows of the code's `external_round_constants` that the full-round loops read.
That vector holds the rows of `RC_16_30` left after `drain(4..17)`; the two full-round loops
read its first eight, rows `0` to `3` and `17` to `20`
(`sp1-primitives` `5.2.4` `src/lib.rs:1110-1115`; `p3-poseidon2` `0.2.3-succinct`
`src/lib.rs:183-184`, `:197-198`). -/
def externalConstants (r : Fin 8) : State :=
  if h : r.val < 4 then roundConstants ⟨r.val, by omega⟩
  else roundConstants ⟨r.val + 13, by omega⟩

/-- The code's `internal_round_constants`: column `0` of rows `4` to `16` of `RC_16_30`, taken
by `drain(4..17).map(|vec| vec[0])` (`sp1-primitives` `5.2.4` `src/lib.rs:1113-1114`). -/
def internalConstants (j : Fin 13) : F := roundConstants ⟨j.val + 4, by omega⟩ 0

theorem values_eq_roundValues_lt : ∀ n : Fin 21, ∀ i : Fin 16,
    values n.val i = Plonky3.roundValues 13 externalConstants internalConstants n.val i := by
  decide

/-- **The table is built from the constants the code reads.** `values` is the table that
`Plonky3.roundValues` builds from the eight external rows the code reads and
`internal_round_constants`. -/
theorem values_eq_roundValues :
    values = Plonky3.roundValues 13 externalConstants internalConstants := by
  funext n i
  by_cases hn : n < 21
  · exact values_eq_roundValues_lt ⟨n, hn⟩ i
  · simp [values, Plonky3.roundValues, hn, show ¬n < 4 by omega, show ¬n < 4 + 13 by omega]

/-! ### The permutation -/

/-- The `21` rounds with the pinned constants: four full, thirteen partial and four full
(`ROUNDS_F = 8`, `ROUNDS_P = 13`, `sp1-primitives` `5.2.4` `src/lib.rs:1108-1109`). -/
def rounds : ℕ → Hades.RoundSpec (Fin 16) F := Plonky3.rounds conditions 13 sbox values

/-- **The permutation**: the initial external layer, then the `8 + 13` rounds. -/
def permutation (x : State) : State := Plonky3.permutation conditions 13 sbox values x

theorem permutation_eq (x : State) : permutation x = Hades.execute rounds (external x) 21 := rfl

theorem permutation_bijective : Function.Bijective permutation :=
  Plonky3.permutation_bijective conditions 13 sbox values

/-- A first-half full round is the code's round (`p3-poseidon2` `0.2.3-succinct`
`src/lib.rs:183-187`) with `external_constants[j]`. -/
theorem rounds_apply_prefix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds j).apply x =
      external (fun i => sbox (x i + externalConstants ⟨j, by omega⟩ i)) := by
  rw [rounds, Plonky3.rounds_apply_prefix conditions 13 sbox values hj x, values_eq_roundValues,
    Plonky3.roundValues_prefix 13 _ _ hj]
  rfl

/-- **A partial round is the code's round** (`p3-poseidon2` `0.2.3-succinct`
`src/lib.rs:190-194`): add `internal_constants[j]` to `state[0]`, apply the S-box to `state[0]`
only, then the internal layer. -/
theorem rounds_apply_partial {j : ℕ} (hj : j < 13) (x : State) :
    (rounds (4 + j)).apply x =
      internal (Function.update x 0 (sbox (x 0 + internalConstants ⟨j, hj⟩))) := by
  rw [rounds, values_eq_roundValues]
  exact Plonky3.rounds_roundValues_apply_middle conditions 13 sbox _ _ hj x

/-- A second-half full round is the code's round (`p3-poseidon2` `0.2.3-succinct`
`src/lib.rs:197-201`) with `external_constants[4 + j]`. -/
theorem rounds_apply_suffix {j : ℕ} (hj : j < 4) (x : State) :
    (rounds (17 + j)).apply x =
      external (fun i => sbox (x i + externalConstants ⟨4 + j, by omega⟩ i)) := by
  rw [show 17 + j = 4 + 13 + j by omega, rounds,
    Plonky3.rounds_apply_suffix conditions 13 sbox values hj x, values_eq_roundValues,
    Plonky3.roundValues_suffix 13 _ _ hj]
  rfl

/-! ### Activity -/

/-- **Thirty-two charged S-boxes, for every round-constant table.** Two distinct inputs incur
at least `32` charged S-box applications over the `8 + 13` rounds, all counted in the full
rounds. A lower bound; it is not claimed to be attained. -/
theorem activity_general (v : ℕ → Fin 16 → F) {x y : State} (hxy : x ≠ y) :
    32 ≤ Hades.scheduledWeight (Plonky3.rounds conditions 13 sbox v)
      (Hades.differenceTrace (Plonky3.rounds conditions 13 sbox v) (external x) (external y))
      0 (8 + 13) :=
  Plonky3.activity conditions m4Primes_ne_zero 13 sbox v hxy

/-- **Thirty-two charged S-boxes for the pinned permutation.** -/
theorem activity {x y : State} (hxy : x ≠ y) :
    32 ≤ Hades.scheduledWeight rounds
      (Hades.differenceTrace rounds (external x) (external y)) 0 (8 + 13) :=
  activity_general values hxy

/-! ### The partial rounds contribute nothing to this argument -/

/-- **Some nonzero difference stays inactive through the thirteen consecutive partial
rounds**, since `13 < 16` (`Hades.inactiveSpace_ne_bot`). -/
theorem partial_inactive_ne_bot :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 13 ≠ ⊥ :=
  inactiveSpace_internal_ne_bot _ _ _ _ (by norm_num)

/-- These differences form a space of dimension at least `16 - 13 = 3`. A lower bound only. -/
theorem three_le_finrank_partial_inactive :
    3 ≤ Module.finrank F
      (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 13) :=
  three_le_finrank_inactiveSpace_thirteen _ _ _ _

/-- **The middle term of `Plonky3.activity_with_middle` is zero here.** Whatever window `w`
satisfies its hypothesis, `13 / w = 0`, because such a `w` is at least `16`. -/
theorem partial_window_term_eq_zero {w : ℕ}
    (htriv : Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) ({0} : Finset (Fin 16)) w =
      ⊥) :
    13 / w = 0 :=
  middle_term_eq_zero (by norm_num) htriv

/-- **Some distinct inputs charge no S-box in the partial rounds**, for every round-constant
table. Take a nonzero difference `a` that stays inactive through thirteen consecutive partial
rounds; the first four rounds after the initial layer form a bijection, so some pair of inputs
reaches the states `a` and `0` at round `4`. Their difference then crosses all thirteen partial
rounds without reaching coordinate `0` (`Hades.IsTrail.free_window`). This is a structural
property of thirteen partial rounds at width sixteen, not an attack: such pairs still incur the
`32` charged S-boxes of `activity_general` in the full rounds. -/
theorem exists_pair_partial_free (v : ℕ → Fin 16 → F) :
    ∃ x y : State, x ≠ y ∧
      Hades.scheduledWeight (Plonky3.rounds conditions 13 sbox v)
        (Hades.differenceTrace (Plonky3.rounds conditions 13 sbox v) (external x) (external y))
        4 13 = 0 := by
  set R := Plonky3.rounds conditions 13 sbox v with hR
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp partial_inactive_ne_bot
  have hbij : Function.Bijective (fun z : State => Hades.execute R (external z) 4) :=
    (Hades.execute_bijective R 4).comp external.bijective
  obtain ⟨x, hx⟩ := hbij.surjective a
  obtain ⟨y, hy⟩ := hbij.surjective 0
  simp only at hx hy
  refine ⟨x, y, ?_, ?_⟩
  · rintro rfl
    exact ha0 (hx.symm.trans hy)
  · have hdiff : Hades.differenceTrace R (external x) (external y) 4 = a := by
      rw [Hades.differenceTrace, hx, hy, sub_zero]
    have hT := Hades.differenceTrace_isTrail R (external x) (external y) (8 + 13)
    have h := hT.free_window internal ({0} : Finset (Fin 16)) 4 13 (by norm_num)
      (fun j hj => linear_middle conditions 13 hj)
      (fun j hj => Hades.hadesMask_middle 4 13 4 _ hj) (by rw [hdiff]; exact ha)
    exact h.2

/-! ### The independent-key trail bound -/

/-- `u * 2^dd ≤ |F|` with `u = 6`, `dd = 28`. -/
theorem probability_margin : 6 * 2 ^ 28 ≤ Fintype.card F := by
  rw [field_card]
  decide

/-- **Trail bound for every round-constant table**, in the model with an additional
independent uniform key per round only: the number of key sequences realising a fixed nonzero
trail `T`, times `2^(28 * 32)`, is at most the number of all key sequences. The exponent keeps
its round arithmetic; `probability_exponent` evaluates it to `896`. This concerns one trail in
that model: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_general (v : ℕ → Fin 16 → F) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.rounds conditions 13 sbox v) (8 + 13) T x *
        2 ^ (28 * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) := by
  have h := Plonky3.independent_key_probability conditions m4Primes_ne_zero 13 sbox v sbox_uniform
    probability_margin h0 x
  rwa [show (28 : ℕ) * 32 = 28 * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) by norm_num] at h

/-- **Trail bound for the pinned constants**, in the additional-independent-key model only. -/
theorem independent_key_probability {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 13) T x * 2 ^ (28 * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2))
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_probability_general values h0 x

/-- The displayed bound's concrete exponent. -/
theorem probability_exponent : 28 * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) = 896 := by
  decide

end Poseidon2.BabyBear

/-! ### The exact ratio and the sharp exponent

`independent_key_probability` charges `28` bits per charged S-box, the largest `dd` with
`6 * 2^dd ≤ p`, so `896` bits over the `32` charged S-boxes of the full rounds. Keeping the
ratio `p / 6` exact (`independent_key_probability_exact`) gives `906` bits
(`independent_key_probability_sharp`), since `32 * log2 (p / 6) ≈ 906.3`. The `_general` forms
state the same for every round-constant table. The partial rounds still contribute nothing. The
sample space is the same: one trail, an additional independent uniform key per round. -/

namespace Poseidon2.BabyBear

/-- **Trail bound as an exact ratio, for every round-constant table**, in the model with an
additional independent uniform key per round: for every nonzero trail `T`, the number of key
sequences realising `T`, times `p^32` (`p = modulus`, `32 = (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2`),
is at most `6^32` times the number of all key sequences. Here `u = 6` (`sbox_uniform`), and the
`32` charged S-boxes are those of the full rounds, as in `activity_general`. This concerns one
trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_exact_general (v : ℕ → Fin 16 → F) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.rounds conditions 13 sbox v) (8 + 13) T x
        * modulus ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2)
      ≤ 6 ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) * Fintype.card (Fin 16 → F) ^ (8 + 13) := by
  have h := Plonky3.independent_key_probability_exact conditions m4Primes_ne_zero 13 sbox v
    sbox_uniform h0 x
  rw [field_card, show (32 : ℕ) = (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 by norm_num] at h
  exact h

/-- **Trail bound as an exact ratio** for the pinned constants, in the model with an additional
independent uniform key per round: for every nonzero trail `T`, the number of key sequences
realising `T`, times `p^32` (`p = modulus`, `32 = (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2`), is at
most `6^32` times the number of all key sequences. Here `u = 6` (`sbox_uniform`), and the `32`
charged S-boxes are those of the full rounds, as in `activity`. This concerns one trail in that
model only: not the permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_exact {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 13) T x * modulus ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2)
      ≤ 6 ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) * Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_probability_exact_general values h0 x

set_option exponentiation.threshold 1000 in
/-- `2^906 * 6^32 ≤ p^32`, by `decide`. `Checks/BabyBear.lean` shows that `2^907 * 6^32 ≤ p^32`
fails, so `906` is the largest such exponent. -/
theorem sharp_exponent_bound :
    2 ^ 906 * 6 ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2)
      ≤ modulus ^ ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2) := by
  decide

/-- **Trail bound with the sharp exponent, for every round-constant table**, in the same model:
for every nonzero trail `T`, the number of key sequences realising `T`, times `2^906`, is at
most the number of all key sequences. It follows from
`independent_key_probability_exact_general` and `sharp_exponent_bound`, and `906` is the largest
exponent that this arithmetic gives. This concerns one trail in that model only: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_sharp_general (v : ℕ → Fin 16 → F) {T : ℕ → State}
    (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount (Plonky3.rounds conditions 13 sbox v) (8 + 13) T x * 2 ^ 906
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  Hades.mul_le_of_ratio (independent_key_probability_exact_general v h0 x) sharp_exponent_bound
    (pow_pos (by norm_num) _)

/-- **Trail bound with the sharp exponent** for the pinned constants, in the same model: for
every nonzero trail `T`, the number of key sequences realising `T`, times `2^906`, is at most
the number of all key sequences. It follows from `independent_key_probability_exact` and
`sharp_exponent_bound`, and `906` is the largest exponent that this arithmetic gives. This
concerns one trail in that model only: not the permutation with its fixed constants, and not a
differential. -/
theorem independent_key_probability_sharp {T : ℕ → State} (h0 : T 0 ≠ 0) (x : State) :
    Hades.keyCount rounds (8 + 13) T x * 2 ^ 906 ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_probability_sharp_general values h0 x

end Poseidon2.BabyBear

/-! ### Exact inactive dimensions through the diagonal criterion

`three_le_finrank_partial_inactive` is a lower bound from rank–nullity. The fifteen diagonal
entries off coordinate `0`, namely `1, 2, 4, …, 2^13, 2^15`, are pairwise distinct in `F`
(`diag_injOn`, by `decide`), so the criterion `Hades.inactiveSpace_diagPlusOnes_card_eq_bot_iff`
makes it exact: the differences that stay inactive through the thirteen consecutive partial
rounds form a space of dimension exactly `3` (`finrank_partial_inactive`), and no nonzero
difference would stay inactive through sixteen (`inactive_sixteen`). For the unscaled layer
`diag d + J` this is `inactive_trivial_by_criterion`, the hypothesis of
`Plonky3.activity_with_middle` with `w = 16` over `F`; there `13 / 16 = 0`, as
`partial_window_term_eq_zero` states for every admissible `w`. No Krylov table is used here.

These are statements about inactive differences of the partial rounds only: they are the
linear-algebra fact behind "at most `15` consecutive partial rounds can be linearized", not a
proof of resistance to subspace trails in general, and they say nothing about the full
rounds. -/

namespace Poseidon2.BabyBear

open Plonky3

/-- The diagonal entries `d 1, …, d 15` are pairwise distinct in `F`, by `decide`. -/
theorem diag_injOn : Set.InjOn (sp1Diag F) {i | i ≠ 0} :=
  injOn_sp1Diag_of_forall (by decide)

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds**, for
the unscaled layer `diag d + J`, by the diagonal criterion. This is the hypothesis of
`Plonky3.activity_with_middle` with `w = 16` over `F`. -/
theorem inactive_trivial_by_criterion :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) ({0} : Finset (Fin 16)) 16 = ⊥ :=
  inactiveSpace_sixteen_eq_bot_iff.mpr diag_injOn

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds** of the
code's internal layer, by the diagonal criterion. BabyBear has only thirteen partial rounds. -/
theorem inactive_sixteen :
    Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 16 = ⊥ :=
  inactiveSpace_internal_sixteen_eq_bot _ _ _ _ diag_injOn

/-- **Exactly `16 - r` dimensions of differences stay inactive through `r` consecutive partial
rounds**, for `r ≤ 16`. -/
theorem finrank_inactive_eq {r : ℕ} (hr : r ≤ 16) :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) r) =
      16 - r :=
  finrank_inactiveSpace_internal_eq _ _ _ _ diag_injOn hr

/-- **Exactly three dimensions of differences stay inactive through the thirteen consecutive
partial rounds.** This makes `three_le_finrank_partial_inactive` exact. -/
theorem finrank_partial_inactive :
    Module.finrank F (Hades.inactiveSpace internal.toLinearMap ({0} : Finset (Fin 16)) 13) = 3 :=
  finrank_inactive_eq (by norm_num)

end Poseidon2.BabyBear

/-! ### The independent-key differential bound

The trail bounds above concern one trail. `independent_key_differential_exact` bounds a
differential, the sum over all trails from a nonzero input difference `a` to an output difference
`b`, in the same model with an additional independent uniform key per round
(`Plonky3.independent_key_differential_exact`). It charges `7` S-boxes of the first two full
rounds, one fewer than the branch number `8`, at the ratio `p / 6` each; the other rounds are not
charged. Since `7 * log2 (p / 6) ≈ 198.3`, the sharp exponent is `198`
(`independent_key_differential_sharp`). The `_general` forms state the same for every
round-constant table. Nothing here concerns the permutation with its fixed constants. -/

namespace Poseidon2.BabyBear

/-- **Differential bound as an exact ratio, for every round-constant table**, in the model with
an additional independent uniform key per round: for every nonzero input difference `a`, every
output difference `b` and every input `x`, the number of key sequences under which `(x, x + a)`
has output difference `b` after the `21` rounds, times `p^7` (`p = modulus`), is at most `6^7`
times the number of all key sequences. Here `u = 6` (`sbox_uniform`). This concerns the
key-averaged differential only: not the permutation with its fixed constants, and not any one
key. -/
theorem independent_key_differential_exact_general (v : ℕ → Fin 16 → F) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.rounds conditions 13 sbox v) (8 + 13) a b x * modulus ^ 7
      ≤ 6 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 13) := by
  have h := Plonky3.independent_key_differential_exact conditions m4Primes_ne_zero 13 sbox v
    sbox_uniform ha b x
  rw [field_card] at h
  exact h

/-- **Differential bound as an exact ratio** for the pinned constants, in the same model: for
every nonzero input difference `a`, the key count of the differential `(a, b)` times `p^7` is at
most `6^7` times the number of all key sequences. This concerns the key-averaged differential
only: not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_exact {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 13) a b x * modulus ^ 7
      ≤ 6 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_differential_exact_general values ha b x

/-- `2^198 * 6^7 ≤ p^7`, by `decide`. `Checks/BabyBear.lean` shows that `2^199 * 6^7 ≤ p^7`
fails, so `198` is the largest such exponent. -/
theorem differential_sharp_exponent_bound : 2 ^ 198 * 6 ^ 7 ≤ modulus ^ 7 := by
  decide

/-- **Differential bound with the sharp exponent, for every round-constant table**, in the same
model: for every nonzero input difference `a`, the key count of the differential `(a, b)`, times
`2^198`, is at most the number of all key sequences. It follows from
`independent_key_differential_exact_general` and `differential_sharp_exponent_bound`, and `198` is
the largest exponent that this arithmetic gives. This concerns the key-averaged differential
only: not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_sharp_general (v : ℕ → Fin 16 → F) {a : State} (ha : a ≠ 0)
    (b x : State) :
    Hades.diffKeyCount (Plonky3.rounds conditions 13 sbox v) (8 + 13) a b x * 2 ^ 198
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  Hades.mul_le_of_ratio (independent_key_differential_exact_general v ha b x)
    differential_sharp_exponent_bound (pow_pos (by norm_num) _)

/-- **Differential bound with the sharp exponent** for the pinned constants, in the same model:
for every nonzero input difference `a`, the key count of the differential `(a, b)`, times
`2^198`, is at most the number of all key sequences. This concerns the key-averaged differential
only: not the permutation with its fixed constants, and not any one key. -/
theorem independent_key_differential_sharp {a : State} (ha : a ≠ 0) (b x : State) :
    Hades.diffKeyCount rounds (8 + 13) a b x * 2 ^ 198 ≤ Fintype.card (Fin 16 → F) ^ (8 + 13) :=
  independent_key_differential_sharp_general values ha b x

end Poseidon2.BabyBear
