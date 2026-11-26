/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.Plonky3
import WideTrail.Algebra.PowerSbox
import WideTrail.Differential.PowerMap
import Mathlib.Tactic.IntervalCases

/-!
# Checks for the generic Plonky3 width-sixteen model

`WideTrail.Poseidon2.Plonky3` states its results over an arbitrary field under explicit
hypotheses. The checks below show, on small prime fields, that the hypotheses can all hold at
once; that the `m4Primes` hypothesis cannot be dropped from `external_isBranchBound`, whose
conclusion fails over `ZMod 17`; that the inactive-space hypothesis of `activity_with_middle` is
not implied by the others, since over `ZMod 23` it fails for every window while all the others
hold (this does not show that the conclusion of `activity_with_middle` fails over `ZMod 23`);
and that the external layer agrees with the code's evaluation order on concrete vectors. All
finite checks are kernel `decide`.

* **`ZMod 29`, everything holds.** `29` is none of `2, 3, 5, 7, 11, 17, 677`, the cube map is a
  permutation (`29 ≡ 2 mod 3`), and `20 = 2^{-32}` in `ZMod 29` (`toy_scale`) is the scale.
  A Krylov certificate (`toy_inactive`) shows that no nonzero difference stays inactive through
  sixteen consecutive partial rounds with `diag d + J`. With `rP = 20`, as for KoalaBear, the
  theorems give `33` charged S-boxes (`toy_activity`) and the trail exponent `3 * 33`
  (`toy_probability`), for every round-constant table. Some nonzero difference stays inactive
  through fifteen consecutive partial rounds (`toy_fifteen_ne_bot`).
* **An execution over `ZMod 29`.** With a constant table built by `roundValues`, the whole
  permutation on `(0, 1, …, 15)` is checked round by round against a trace computed outside
  Lean by an independent model of the code's loops (`toy_permutation`). This exercises the
  schedule, the masks, the partial-round constants at `state[0]` and the scaled internal layer.
  It does not pin the internal diagonal: in `ZMod 29`, `d_0 = -2 = 2^15 = d_15`, so the trace
  would be the same with those two entries exchanged. The diagonal is pinned by `sp1Diag_zero`,
  `sp1Diag_eq_pow` and `sp1Diag_fifteen`.
* **`ZMod 17`, the `m4Primes` hypothesis cannot be dropped from `external_isBranchBound`.**
  `Conditions` holds, so the permutation is defined and bijective (`seventeen_bijective`), and
  `1, …, 5` are nonzero, but `17 ∈ m4Primes` vanishes. The state with first block
  `(0, 1, 9, 5)` and all other blocks zero has `3` nonzero coordinates and an image with `4`:
  weight `7 < 8` (`seventeen_not_isBranchBound`).
* **`ZMod 23`, the inactive-space hypothesis of `activity_with_middle` is not implied by the
  others.** Every other hypothesis holds (`twentyThree_activity` uses them all), but `2^11 = 1`
  in `ZMod 23`, so the diagonal entries `d 1 = 1` and `d 12 = 2^11` coincide. The difference
  `e 12 - e 1` is then fixed by `diag d + J` and never reaches coordinate `0`, so the inactive
  space is nonzero for every window length (`twentyThree_inactive_ne_bot`), and
  `activity_with_middle` does not apply over that field for any window. This does not show that
  its conclusion fails there; it shows only that this route charges the partial rounds
  nothing.
* **The external layer against the code.** `toy_external` evaluates `external` on
  `(0, 1, …, 15)` over `ZMod 29`. `koalaBear_mdsLight_neg`, `koalaBear_mdsLight_cubic`,
  `babyBear_mdsLight_neg` and `babyBear_mdsLight_cubic` evaluate the code transcription
  `mdsLight` over `ZMod 2130706433` and `ZMod 2013265921`. The expected outputs were computed
  outside Lean by a model that emulates the Rust operation order on Montgomery representatives
  and reproduces the upstream known-answer tests. These are ring computations and use no
  primality; over a field, `external_eq_mdsLight` transfers them to `external`.
* **The SP1 fields, at the level of the ring.** For the KoalaBear prime `2130706433`
  (`p3-koala-bear` `0.4.3-succinct` `src/koala_bear.rs:19`) and the BabyBear prime
  `2013265921` (`p3-baby-bear` `0.2.3-succinct` `src/baby_bear.rs:16`), the integers `2`, `35`,
  `677` and `81917` are nonzero, and `1057030144`, resp. `943718400`, times `2^32` is `1`
  (`koalaBear_scalars`, `babyBear_scalars`). These are the canonical values of the code's
  `MONTY_INVERSE`, the element with Montgomery representative `1` (`p3-koala-bear`
  `src/poseidon2.rs:35`, `p3-baby-bear` `src/poseidon2.rs:27`). Primality of the two moduli is
  not proved here.

## What is not claimed

The execution over `ZMod 29` is compared with a second model computed outside Lean, not with the
Rust code. The `mdsLight` vectors over the SP1 fields are compared with an outside model that
reproduces the test vectors of the `p3-koala-bear` and `p3-baby-bear` crates; they are not
compared with SP1's AIR, the gnark circuit or a built binary. The counterexamples over `ZMod 17`
and `ZMod 23` concern those fields only. Nothing here strengthens the security claims of
`WideTrail.Poseidon2.Plonky3`.

The axiom footprints of the main results are pinned at the end of the file.
-/

set_option autoImplicit false

namespace Poseidon2.Plonky3.Checks

/-! ### `ZMod 29`: every hypothesis holds -/

instance fact_prime_twentyNine : Fact (Nat.Prime 29) := ⟨by decide⟩

abbrev F := ZMod 29

theorem toy_conditions : Conditions (20 : F) := ⟨by decide, by decide, by decide, by decide⟩

/-- `20` is `2^{-32}` in `ZMod 29`, the scale the code would use there. -/
theorem toy_scale : (20 : F) * 2 ^ 32 = 1 := by decide

theorem toy_primes : ∀ p ∈ m4Primes, (p : F) ≠ 0 := by decide

theorem toy_fermat (x : F) (hx : x ≠ 0) : x ^ (29 - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [ZMod.card] at h

/-- The cube map on `ZMod 29`, with inverse `x ↦ x ^ 19` (`3 * 19 = 2 * 28 + 1`). -/
def toySbox : F ≃ F :=
  Sbox.powerEquivOfFermat 29 3 19 2 (by decide) (by decide) (by decide) toy_fermat

theorem toySbox_uniform : IsDiffUniform toySbox 2 :=
  Sbox.pow_three_uniform (K := F) (by decide)

/-- Rows `e_0, A e_0, …, A^15 e_0` for `A = diag d + J` over `ZMod 29`. -/
def toyKrylov : Fin 16 → Fin 16 → F :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![28, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![16, 15, 16, 18, 22, 1, 17, 20, 26, 9, 4, 23, 3, 21, 28, 12],
    ![16, 5, 22, 4, 21, 6, 12, 23, 12, 3, 8, 23, 15, 21, 5, 24],
    ![14, 22, 3, 4, 11, 26, 24, 10, 16, 2, 24, 21, 26, 19, 0, 27],
    ![18, 10, 23, 4, 18, 27, 2, 19, 6, 7, 9, 3, 21, 5, 17, 21],
    ![0, 17, 24, 23, 6, 4, 13, 5, 21, 1, 4, 5, 8, 13, 13, 23],
    ![6, 23, 25, 11, 25, 12, 16, 7, 26, 1, 24, 22, 5, 10, 14, 18],
    ![1, 7, 5, 28, 10, 2, 3, 26, 6, 8, 5, 8, 16, 25, 6, 6],
    ![15, 24, 27, 13, 10, 20, 26, 28, 2, 6, 25, 2, 15, 18, 14, 5],
    ![17, 13, 14, 12, 11, 19, 9, 12, 13, 17, 0, 7, 27, 28, 11, 8],
    ![10, 28, 14, 5, 16, 0, 13, 0, 26, 17, 15, 20, 8, 8, 24, 28],
    ![9, 28, 28, 20, 12, 0, 10, 0, 22, 2, 24, 6, 28, 27, 17, 2],
    ![14, 2, 1, 25, 12, 3, 4, 3, 6, 22, 24, 28, 14, 18, 9, 28],
    ![11, 12, 12, 23, 19, 0, 22, 28, 24, 16, 2, 1, 1, 20, 20, 12],
    ![27, 3, 15, 25, 27, 20, 28, 14, 18, 27, 0, 0, 9, 15, 10, 25]]

/-- A left inverse of the matrix with rows `toyKrylov j`. -/
def toyKrylovInv : Fin 16 → Fin 16 → F :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![6, 11, 15, 5, 20, 0, 11, 1, 25, 2, 24, 1, 26, 12, 4, 6],
    ![10, 20, 1, 23, 14, 23, 23, 5, 21, 26, 7, 19, 4, 19, 13, 2],
    ![5, 16, 14, 22, 14, 26, 5, 27, 16, 19, 9, 10, 7, 3, 17, 2],
    ![4, 9, 25, 25, 12, 9, 26, 7, 10, 28, 17, 18, 11, 3, 7, 11],
    ![7, 3, 11, 9, 18, 25, 10, 18, 8, 14, 25, 6, 24, 28, 20, 13],
    ![7, 15, 4, 28, 8, 27, 28, 7, 6, 15, 14, 8, 23, 16, 17, 10],
    ![28, 4, 10, 17, 4, 12, 18, 28, 22, 8, 14, 26, 24, 10, 12, 26],
    ![7, 24, 8, 5, 6, 14, 8, 5, 5, 7, 7, 12, 24, 10, 13, 21],
    ![1, 28, 15, 18, 20, 9, 7, 8, 6, 21, 25, 23, 27, 24, 12, 5],
    ![13, 20, 16, 23, 13, 16, 16, 23, 10, 26, 21, 22, 3, 15, 6, 20],
    ![12, 12, 1, 9, 7, 25, 22, 21, 10, 28, 19, 0, 10, 20, 19, 10],
    ![1, 25, 10, 4, 16, 11, 11, 25, 16, 13, 7, 27, 9, 5, 4, 15],
    ![17, 8, 16, 19, 17, 11, 1, 21, 1, 10, 21, 17, 0, 6, 25, 11],
    ![22, 15, 8, 5, 2, 9, 14, 22, 10, 8, 19, 19, 11, 19, 2, 15],
    ![6, 23, 20, 20, 3, 15, 3, 14, 8, 7, 3, 24, 0, 13, 3, 7]]

/-- **No nonzero difference stays inactive through sixteen consecutive partial rounds over
`ZMod 29`.** -/
theorem toy_inactive :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) ({0} : Finset (Fin 16)) 16 = ⊥ :=
  Hades.inactiveSpace_diagPlusOnes_eq_bot one_ne_zero (sp1Diag F) 0 16 toyKrylov
    (by decide) (by decide) toyKrylovInv (by decide)

/-- Some nonzero difference stays inactive through fifteen consecutive partial rounds, so the
window `16` cannot be shortened. -/
theorem toy_fifteen_ne_bot :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) ({0} : Finset (Fin 16)) 15 ≠ ⊥ :=
  Hades.inactiveSpace_ne_bot _ _ 15 (by simp)

theorem toy_bijective (values : ℕ → Fin 16 → F) :
    Function.Bijective (permutation toy_conditions 20 toySbox values) :=
  permutation_bijective toy_conditions 20 toySbox values

/-- **`33` charged S-boxes over `ZMod 29` with twenty partial rounds**, for every constant
table: `32` from the full rounds and `20 / 16 = 1` from the partial rounds. -/
theorem toy_activity (values : ℕ → Fin 16 → F) {x y : Fin 16 → F} (hxy : x ≠ y) :
    33 ≤ Hades.scheduledWeight (rounds toy_conditions 20 toySbox values)
      (Hades.differenceTrace (rounds toy_conditions 20 toySbox values)
        (external toy_conditions.thirtyFive x) (external toy_conditions.thirtyFive y)) 0
      (8 + 20) :=
  activity_with_middle toy_conditions toy_primes 20 toySbox values toy_inactive hxy

/-- The trail bound over `ZMod 29`: `u = 2`, and `2 * 2^3 ≤ 29` gives `dd = 3`. -/
theorem toy_probability (values : ℕ → Fin 16 → F) {T : ℕ → Fin 16 → F} (h0 : T 0 ≠ 0)
    (x : Fin 16 → F) :
    Hades.keyCount (rounds toy_conditions 20 toySbox values) (8 + 20) T x * 2 ^ (3 * 33)
      ≤ Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_with_middle toy_conditions toy_primes 20 toySbox values
    toySbox_uniform (by rw [ZMod.card]; decide) toy_inactive h0 x

/-- The external layer on `(0, 1, …, 15)` over `ZMod 29`. -/
theorem toy_external :
    external toy_conditions.thirtyFive (fun i : Fin 16 => ((i : ℕ) : F)) =
      ![5, 20, 6, 10, 4, 19, 5, 9, 3, 18, 4, 8, 2, 17, 3, 7] := by
  decide

/-! ### An execution over `ZMod 29`, against an independent model -/

/-- A constant table built by `roundValues` from external rows `ext r i = r + i` and internal
scalars `int j = j + 1`. -/
def toyValues : ℕ → Fin 16 → F :=
  roundValues 20 (fun r i => ((r : ℕ) : F) + ((i : ℕ) : F)) (fun j => ((j : ℕ) : F) + 1)

/-- The states entering each of the `28` rounds, and the output, for the input
`(0, 1, …, 15)`. They were computed outside Lean by the round-by-round model of the code
(initial `mds_light`, `4` full rounds, `20` partial rounds with the constant and the S-box on
`state[0]` only and the internal layer scaled by `20`, `4` full rounds). -/
def toyTrace : Fin 29 → Fin 16 → F :=
  ![![5, 20, 6, 10, 4, 19, 5, 9, 3, 18, 4, 8, 2, 17, 3, 7],
    ![20, 7, 22, 19, 4, 14, 11, 7, 21, 7, 27, 8, 16, 18, 15, 25],
    ![28, 10, 25, 23, 25, 10, 14, 25, 24, 27, 13, 3, 27, 10, 26, 25],
    ![1, 11, 8, 23, 0, 23, 16, 1, 23, 2, 10, 10, 23, 2, 22, 24],
    ![10, 17, 5, 25, 6, 0, 13, 13, 22, 7, 5, 17, 25, 26, 16, 18],
    ![10, 27, 3, 5, 9, 6, 3, 0, 8, 2, 21, 21, 16, 21, 20, 11],
    ![17, 19, 5, 24, 20, 7, 7, 1, 7, 4, 6, 11, 19, 12, 4, 25],
    ![20, 8, 2, 11, 15, 12, 19, 9, 3, 11, 23, 13, 1, 3, 23, 20],
    ![15, 18, 25, 13, 25, 15, 12, 10, 27, 5, 14, 23, 15, 17, 5, 15],
    ![17, 14, 16, 27, 0, 17, 26, 13, 15, 24, 15, 24, 8, 4, 10, 11],
    ![13, 5, 17, 0, 15, 3, 9, 9, 19, 22, 2, 14, 24, 24, 2, 10],
    ![13, 11, 11, 27, 20, 1, 16, 5, 5, 2, 4, 24, 25, 23, 7, 4],
    ![20, 2, 19, 28, 24, 15, 17, 5, 25, 17, 26, 13, 24, 15, 2, 28],
    ![9, 20, 15, 16, 21, 24, 14, 0, 6, 20, 0, 0, 7, 21, 18, 20],
    ![28, 13, 10, 23, 15, 14, 18, 19, 9, 20, 19, 19, 16, 1, 13, 2],
    ![25, 4, 28, 18, 27, 19, 12, 23, 19, 6, 4, 3, 23, 0, 20, 12],
    ![7, 6, 2, 3, 12, 3, 8, 18, 20, 22, 25, 2, 28, 13, 16, 26],
    ![13, 2, 20, 6, 4, 1, 14, 12, 13, 2, 15, 10, 15, 20, 12, 2],
    ![17, 27, 4, 3, 18, 17, 15, 6, 4, 19, 3, 18, 22, 3, 12, 23],
    ![5, 1, 27, 20, 21, 0, 13, 7, 15, 26, 21, 4, 15, 26, 8, 20],
    ![17, 2, 18, 16, 7, 11, 8, 10, 15, 21, 16, 6, 17, 26, 18, 23],
    ![11, 5, 18, 27, 12, 5, 10, 5, 27, 11, 13, 1, 24, 9, 17, 2],
    ![8, 21, 3, 22, 14, 13, 28, 28, 21, 10, 18, 14, 6, 21, 12, 15],
    ![5, 18, 8, 24, 11, 17, 2, 0, 27, 19, 0, 1, 18, 15, 0, 13],
    ![13, 17, 6, 11, 25, 22, 9, 5, 18, 19, 5, 11, 18, 17, 5, 7],
    ![20, 28, 15, 27, 19, 26, 20, 18, 3, 25, 19, 12, 24, 0, 11, 19],
    ![6, 21, 14, 26, 23, 24, 4, 6, 8, 13, 27, 17, 2, 21, 26, 0],
    ![7, 24, 3, 7, 2, 20, 16, 23, 21, 18, 5, 5, 21, 17, 14, 1],
    ![3, 6, 24, 26, 1, 24, 15, 6, 11, 2, 0, 22, 24, 19, 28, 17]]

def toyTraceAt (n : ℕ) : Fin 16 → F := if h : n < 29 then toyTrace ⟨n, h⟩ else 0

theorem toyTrace_start :
    toyTraceAt 0 = external toy_conditions.thirtyFive (fun i : Fin 16 => ((i : ℕ) : F)) := by
  decide

set_option maxHeartbeats 4000000 in
-- Kernel evaluation of twenty-eight rounds exceeds the default limit.
/-- Each of the `28` rounds is checked once, on literal states. -/
theorem toyTrace_step : ∀ n : Fin 28,
    (rounds toy_conditions 20 toySbox toyValues n.val).apply (toyTraceAt n.val) =
      toyTraceAt (n.val + 1) := by
  decide

theorem toy_execute (n : ℕ) (hn : n ≤ 28) :
    Hades.execute (rounds toy_conditions 20 toySbox toyValues)
      (external toy_conditions.thirtyFive (fun i : Fin 16 => ((i : ℕ) : F))) n = toyTraceAt n := by
  induction n with
  | zero => exact toyTrace_start.symm
  | succ n ih =>
    rw [Hades.execute_succ, ih (by omega)]
    exact toyTrace_step ⟨n, by omega⟩

/-- **The model agrees with the independent round-by-round model on a full execution.** -/
theorem toy_permutation :
    permutation toy_conditions 20 toySbox toyValues (fun i : Fin 16 => ((i : ℕ) : F)) =
      ![3, 6, 24, 26, 1, 24, 15, 6, 11, 2, 0, 22, 24, 19, 28, 17] := by
  unfold permutation
  rw [toy_execute (8 + 20) (by decide)]
  decide

/-! ### `ZMod 17`: the `m4Primes` hypothesis cannot be dropped -/

instance fact_prime_seventeen : Fact (Nat.Prime 17) := ⟨by decide⟩

theorem seventeen_conditions : Conditions (1 : ZMod 17) :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem seventeen_not_primes : ¬ ∀ p ∈ m4Primes, (p : ZMod 17) ≠ 0 := by decide

theorem seventeen_le_five : ∀ n : ℕ, 1 ≤ n → n ≤ 5 → (n : ZMod 17) ≠ 0 := by
  intro n h1 h5
  interval_cases n <;> decide

/-- The permutation is still defined and bijective over `ZMod 17`, for any S-box and table. -/
theorem seventeen_bijective (rP : ℕ) (sbox : ZMod 17 ≃ ZMod 17)
    (values : ℕ → Fin 16 → ZMod 17) :
    Function.Bijective (permutation seventeen_conditions rP sbox values) :=
  permutation_bijective seventeen_conditions rP sbox values

/-- First block `(0, 1, 9, 5)`, all other blocks zero. The block sum is the first block, whose
image under `m4` is `(0, 0, 0, 3)`. -/
def seventeenWitness : Fin 16 → ZMod 17 := ![0, 1, 9, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem seventeen_external :
    external seventeen_conditions.thirtyFive seventeenWitness =
      ![0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3] := by
  decide

theorem seventeen_weight :
    weight seventeenWitness + weight (external seventeen_conditions.thirtyFive seventeenWitness)
      = 7 := by
  decide

/-- **Branch number below `8` over `ZMod 17`.** Every other hypothesis of
`external_isBranchBound` holds there. -/
theorem seventeen_not_isBranchBound :
    ¬ isBranchBound id (external seventeen_conditions.thirtyFive) 8 := by
  intro h
  have hw := h seventeenWitness (by decide)
  rw [colWeight_id, colWeight_id, seventeen_weight] at hw
  omega

/-! ### `ZMod 23`: the inactive-space hypothesis can fail for every window -/

instance fact_prime_twentyThree : Fact (Nat.Prime 23) := ⟨by decide⟩

theorem twentyThree_conditions : Conditions (1 : ZMod 23) :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem twentyThree_primes : ∀ p ∈ m4Primes, (p : ZMod 23) ≠ 0 := by decide

/-- The outer bound holds over `ZMod 23`, for any S-box, number of partial rounds and table. -/
theorem twentyThree_activity (rP : ℕ) (sbox : ZMod 23 ≃ ZMod 23)
    (values : ℕ → Fin 16 → ZMod 23) {x y : Fin 16 → ZMod 23} (hxy : x ≠ y) :
    32 ≤ Hades.scheduledWeight (rounds twentyThree_conditions rP sbox values)
      (Hades.differenceTrace (rounds twentyThree_conditions rP sbox values)
        (external twentyThree_conditions.thirtyFive x)
        (external twentyThree_conditions.thirtyFive y)) 0 (8 + rP) :=
  activity twentyThree_conditions twentyThree_primes rP sbox values hxy

/-- `e 12 - e 1`. -/
def twentyThreeWitness : Fin 16 → ZMod 23 := ![0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

/-- `d 1 = 1` and `d 12 = 2^11 = 1` in `ZMod 23`, and the witness sums to zero, so
`diag d + J` fixes it. -/
theorem twentyThree_fixed :
    diagPlusOnes (1 : ZMod 23) (sp1Diag (ZMod 23)) twentyThreeWitness = twentyThreeWitness := by
  decide

/-- **No window length works over `ZMod 23`.** The fixed difference `e 12 - e 1` has zero at
coordinate `0`, so it stays inactive through any number of consecutive partial rounds. -/
theorem twentyThree_inactive_ne_bot (w : ℕ) :
    Hades.inactiveSpace (diagPlusOnes (1 : ZMod 23) (sp1Diag (ZMod 23)))
      ({0} : Finset (Fin 16)) w ≠ ⊥ := by
  have hpow : ∀ j : ℕ, (diagPlusOnes (1 : ZMod 23) (sp1Diag (ZMod 23)) ^ j) twentyThreeWitness =
      twentyThreeWitness := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, twentyThree_fixed]
  intro hbot
  have hmem : twentyThreeWitness ∈ Hades.inactiveSpace
      (diagPlusOnes (1 : ZMod 23) (sp1Diag (ZMod 23))) ({0} : Finset (Fin 16)) w := by
    intro j _ i hi
    rw [Finset.mem_singleton.mp hi, hpow j]
    decide
  rw [hbot, Submodule.mem_bot] at hmem
  exact absurd hmem (by decide)

/-! ### The external layer against the code, on the SP1 fields -/

/-- KoalaBear (`2130706433`): the input `(-1, -2, …, -16)`. -/
theorem koalaBear_mdsLight_neg :
    mdsLight (R := ZMod 2130706433)
      ![2130706432, 2130706431, 2130706430, 2130706429, 2130706428, 2130706427, 2130706426,
        2130706425, 2130706424, 2130706423, 2130706422, 2130706421, 2130706420, 2130706419,
        2130706418, 2130706417] =
      ![2130706190, 2130706175, 2130706160, 2130706185, 2130706162, 2130706147, 2130706132,
        2130706157, 2130706134, 2130706119, 2130706104, 2130706129, 2130706106, 2130706091,
        2130706076, 2130706101] := by
  decide

/-- KoalaBear: the input `i ↦ (1000003 i^3 + 7 i) mod p`. -/
theorem koalaBear_mdsLight_cubic :
    mdsLight (R := ZMod 2130706433)
      ![0, 1000010, 8000038, 27000102, 64000220, 125000410, 216000690, 343001078, 512001592,
        729002250, 1000003070, 1331004070, 1728005268, 66300249, 613301897, 1244303797] =
      ![1539005664, 2003307121, 918903891, 709303169, 432302499, 1124604640, 340202310,
        1865306833, 650903269, 1859206958, 1662806392, 181201854, 621403172, 503002840,
        1182604902, 475702729] := by
  decide

/-- BabyBear (`2013265921`): the input `(-1, -2, …, -16)`. -/
theorem babyBear_mdsLight_neg :
    mdsLight (R := ZMod 2013265921)
      ![2013265920, 2013265919, 2013265918, 2013265917, 2013265916, 2013265915, 2013265914,
        2013265913, 2013265912, 2013265911, 2013265910, 2013265909, 2013265908, 2013265907,
        2013265906, 2013265905] =
      ![2013265678, 2013265663, 2013265648, 2013265673, 2013265650, 2013265635, 2013265620,
        2013265645, 2013265622, 2013265607, 2013265592, 2013265617, 2013265594, 2013265579,
        2013265564, 2013265589] := by
  decide

/-- BabyBear: the input `i ↦ (1000003 i^3 + 7 i) mod p`. -/
theorem babyBear_mdsLight_cubic :
    mdsLight (R := ZMod 2013265921)
      ![0, 1000010, 8000038, 27000102, 64000220, 125000410, 216000690, 343001078, 512001592,
        729002250, 1000003070, 1331004070, 1728005268, 183740761, 730742409, 1361744309] =
      ![700144863, 1281886832, 432364626, 2001148801, 1724148131, 520624863, 1984369478,
        1143886544, 164364004, 1490108205, 1528588663, 1825369022, 722066467, 838547159,
        1753030245, 693806536] := by
  decide

/-! ### The SP1 fields, at the level of the ring -/

/-- KoalaBear: `2`, `35`, `677`, `81917` are nonzero, and `R^{-1} = 1057030144` satisfies
`R^{-1} * 2^32 = 1`. -/
theorem koalaBear_scalars :
    (2 : ZMod 2130706433) ≠ 0 ∧ (35 : ZMod 2130706433) ≠ 0 ∧ (677 : ZMod 2130706433) ≠ 0 ∧
      (81917 : ZMod 2130706433) ≠ 0 ∧ (1057030144 : ZMod 2130706433) * 2 ^ 32 = 1 := by
  decide

/-- BabyBear: `2`, `35`, `677`, `81917` are nonzero, and `R^{-1} = 943718400` satisfies
`R^{-1} * 2^32 = 1`. -/
theorem babyBear_scalars :
    (2 : ZMod 2013265921) ≠ 0 ∧ (35 : ZMod 2013265921) ≠ 0 ∧ (677 : ZMod 2013265921) ≠ 0 ∧
      (81917 : ZMod 2013265921) ≠ 0 ∧ (943718400 : ZMod 2013265921) * 2 ^ 32 = 1 := by
  decide

end Poseidon2.Plonky3.Checks

/-- info: 'BlockCirculant.blockMix_apply_eq_add_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlockCirculant.blockMix_apply_eq_add_sum

/-- info: 'Poseidon2.m4_natCast_ne_zero_of_le_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.m4_natCast_ne_zero_of_le_five

/-- info: 'Hades.card_sub_le_finrank_inactiveSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.card_sub_le_finrank_inactiveSpace

/-- info: 'Poseidon2.Plonky3.blockIndex_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.blockIndex_val

/-- info: 'Poseidon2.Plonky3.mdsLight_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.mdsLight_apply

/-- info: 'Poseidon2.Plonky3.external_apply_blockIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_apply_blockIndex

/-- info: 'Poseidon2.Plonky3.external_eq_mdsLight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_eq_mdsLight

/-- info: 'Poseidon2.Plonky3.one_add_sum_inv_sp1Diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.one_add_sum_inv_sp1Diag

/-- info: 'Poseidon2.Plonky3.internal_injective_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.internal_injective_iff

/-- info: 'Poseidon2.Plonky3.inactiveSpace_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.inactiveSpace_internal

/-- info: 'Poseidon2.Plonky3.finrank_inactiveSpace_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.finrank_inactiveSpace_internal

/-- info: 'Poseidon2.Plonky3.middle_term_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.middle_term_eq_zero

/-- info: 'Poseidon2.Plonky3.Conditions.of_primes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Conditions.of_primes

/-- info: 'Poseidon2.Plonky3.permutation_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.permutation_bijective

/-- info: 'Poseidon2.Plonky3.rounds_apply_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.rounds_apply_prefix

/-- info: 'Poseidon2.Plonky3.rounds_apply_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.rounds_apply_middle

/-- info: 'Poseidon2.Plonky3.rounds_apply_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.rounds_apply_suffix

/-- info: 'Poseidon2.Plonky3.roundValues_partialRowsAtZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.roundValues_partialRowsAtZero

/-- info: 'Poseidon2.Plonky3.external_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_isBranchBound

/-- info: 'Poseidon2.Plonky3.activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.activity

/-- info: 'Poseidon2.Plonky3.activity_with_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.activity_with_middle

/-- info: 'Poseidon2.Plonky3.independent_key_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.independent_key_probability

/-- info: 'Poseidon2.Plonky3.independent_key_probability_with_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.independent_key_probability_with_middle

/-- info: 'Poseidon2.Plonky3.Checks.toy_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_inactive

/-- info: 'Poseidon2.Plonky3.Checks.toy_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_activity

/-- info: 'Poseidon2.Plonky3.Checks.toy_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_probability

/-- info: 'Poseidon2.Plonky3.Checks.toy_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_external

/-- info: 'Poseidon2.Plonky3.Checks.seventeen_not_isBranchBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.seventeen_not_isBranchBound

/-- info: 'Poseidon2.Plonky3.Checks.twentyThree_inactive_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.twentyThree_inactive_ne_bot

/-- info: 'Poseidon2.Plonky3.Checks.koalaBear_mdsLight_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.koalaBear_mdsLight_neg

/-- info: 'Poseidon2.Plonky3.Checks.babyBear_mdsLight_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.babyBear_mdsLight_neg

/-- info: 'Poseidon2.Plonky3.Checks.koalaBear_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.koalaBear_scalars

/-- info: 'Poseidon2.Plonky3.Checks.babyBear_scalars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.babyBear_scalars

/-- info: 'Poseidon2.Plonky3.Checks.toy_permutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_permutation

/-! ### The exact ratio over `ZMod 29` -/

namespace Poseidon2.Plonky3.Checks

/-- The exact-ratio trail bound over `ZMod 29`, for every round-constant table: `u = 2` and
`33` charged S-boxes, so `keyCount * 29^33 ≤ 2^33 * |F^16|^28`. -/
theorem toy_probability_exact (values : ℕ → Fin 16 → F) {T : ℕ → Fin 16 → F} (h0 : T 0 ≠ 0)
    (x : Fin 16 → F) :
    Hades.keyCount (rounds toy_conditions 20 toySbox values) (8 + 20) T x
        * Fintype.card F ^ (32 + 20 / 16)
      ≤ 2 ^ (32 + 20 / 16) * Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_probability_with_middle_exact toy_conditions toy_primes 20 toySbox values
    toySbox_uniform toy_inactive h0 x

end Poseidon2.Plonky3.Checks

/-- info: 'Poseidon2.Plonky3.independent_key_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.independent_key_probability_exact

/--
info: 'Poseidon2.Plonky3.independent_key_probability_with_middle_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.Plonky3.independent_key_probability_with_middle_exact

/-- info: 'Poseidon2.Plonky3.Checks.toy_probability_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_probability_exact

/-! ### The diagonal criterion over `ZMod 29` and `ZMod 23`

`Plonky3.inactiveSpace_sixteen_eq_bot_iff` reduces the inactive-space hypothesis of
`activity_with_middle` with `w = 16` to the distinctness of the diagonal entries off
coordinate `0`. Over `ZMod 29` they are distinct (`2` has order `28` there), which gives a
second proof of `toy_inactive`, without the Krylov tables. Over `ZMod 23`, `d 1 = 1 = 2^11 =
d 12`, so the criterion says that the inactive space for sixteen consecutive partial rounds is
nonzero, in agreement with `twentyThree_inactive_ne_bot`. -/

namespace Poseidon2.Plonky3.Checks

/-- The diagonal entries off coordinate `0` are pairwise distinct in `ZMod 29`. -/
theorem toy_injOn : Set.InjOn (sp1Diag F) {i | i ≠ 0} :=
  injOn_sp1Diag_of_forall (by decide)

/-- **`toy_inactive` by the diagonal criterion**, without the Krylov tables. -/
theorem toy_inactive_by_criterion :
    Hades.inactiveSpace (diagPlusOnes (1 : F) (sp1Diag F)) ({0} : Finset (Fin 16)) 16 = ⊥ :=
  inactiveSpace_sixteen_eq_bot_iff.mpr toy_injOn

/-- In `ZMod 23`, `d 1 = 1` and `d 12 = 2^11 = 1` coincide. -/
theorem twentyThree_not_injOn : ¬ Set.InjOn (sp1Diag (ZMod 23)) {i | i ≠ 0} := by
  intro h
  have h112 : (1 : Fin 16) = 12 := h (by decide) (by decide) (by decide)
  exact absurd h112 (by decide)

/-- **The criterion agrees with `twentyThree_inactive_ne_bot`**: over `ZMod 23` some nonzero
difference stays inactive through sixteen consecutive partial rounds. -/
theorem twentyThree_inactive_ne_bot_by_criterion :
    Hades.inactiveSpace (diagPlusOnes (1 : ZMod 23) (sp1Diag (ZMod 23)))
      ({0} : Finset (Fin 16)) 16 ≠ ⊥ :=
  fun h => twentyThree_not_injOn (inactiveSpace_sixteen_eq_bot_iff.mp h)

end Poseidon2.Plonky3.Checks

/-- info: 'Poseidon2.Plonky3.inactiveSpace_sixteen_eq_bot_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.inactiveSpace_sixteen_eq_bot_iff

/-- info: 'Poseidon2.Plonky3.inactiveSpace_internal_sixteen_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.inactiveSpace_internal_sixteen_eq_bot

/-- info: 'Poseidon2.Plonky3.finrank_inactiveSpace_internal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.finrank_inactiveSpace_internal_eq

/-- info: 'Poseidon2.Plonky3.Checks.toy_inactive_by_criterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_inactive_by_criterion

/--
info: 'Poseidon2.Plonky3.Checks.twentyThree_inactive_ne_bot_by_criterion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.twentyThree_inactive_ne_bot_by_criterion

/-! ### The differential bound over `ZMod 29` -/

namespace Poseidon2.Plonky3.Checks

/-- The differential bound over `ZMod 29`, for every round-constant table: `u = 2` and branch
number `8`, so for `a ≠ 0`, `diffKeyCount * 29^7 ≤ 2^7 * |F^16|^28`. -/
theorem toy_differential_exact (values : ℕ → Fin 16 → F) {a : Fin 16 → F} (ha : a ≠ 0)
    (b x : Fin 16 → F) :
    Hades.diffKeyCount (rounds toy_conditions 20 toySbox values) (8 + 20) a b x
        * Fintype.card F ^ 7
      ≤ 2 ^ 7 * Fintype.card (Fin 16 → F) ^ (8 + 20) :=
  independent_key_differential_exact toy_conditions toy_primes 20 toySbox values toySbox_uniform
    ha b x

end Poseidon2.Plonky3.Checks

/-- info: 'Hades.roundGamma_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.roundGamma_bijective

/-- info: 'Hades.diffCount_roundGamma_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.diffCount_roundGamma_of_full

/-- info: 'Hades.diffKeyCount_bound_of_two_full_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.diffKeyCount_bound_of_two_full_rounds

/-- info: 'Hades.hades_differential_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hades.hades_differential_bound

/-- info: 'Poseidon2.Plonky3.independent_key_differential_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.independent_key_differential_exact

/-- info: 'Poseidon2.Plonky3.Checks.toy_differential_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_differential_exact

/-! ### States whose four blocks sum to zero

Concrete instances of the results on `blockSumZeroFlat`.

* Over `ZMod 29`, the state with blocks `(1, 2, 3, 4)`, `(5, 6, 7, 8)`, `(9, 10, 11, 12)` and
  `(14, 11, 8, 5)` has zero position sums. The external layer sends it to `M4` applied to each
  block, `mat4Blocks`, with the values computed outside Lean (`toy_zeroSum_external`). The input
  `(0, 1, …, 15)` of `toy_external` has nonzero position sums, and there the external layer is
  not `mat4Blocks` (`toy_external_ne_mat4Blocks`).
* Over the KoalaBear modulus `2130706433`, at the level of the ring, the state whose first three
  blocks are `i ↦ (1000003 i^3 + 7 i) mod p` and whose last block is minus their sum has zero
  position sums, and the code transcription `mdsLight` returns `mat4Blocks` of it
  (`koalaBear_zeroSum_mdsLight`). No primality is used.
* The subspace has dimension `12` over `ZMod 29` (`toy_finrank_blockSumZeroFlat`).

All finite checks are kernel `decide`. -/

namespace Poseidon2.Plonky3.Checks

/-- Blocks `(1, 2, 3, 4)`, `(5, 6, 7, 8)`, `(9, 10, 11, 12)`, `(14, 11, 8, 5)` over `ZMod 29`. -/
def toyZeroSum : Fin 16 → F := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 11, 8, 5]

theorem toyZeroSum_mem : toyZeroSum ∈ blockSumZeroFlat := mem_blockSumZeroFlat.mpr (by decide)

/-- **The blockwise form over `ZMod 29`.** The external layer sends `toyZeroSum` to `M4` applied
to each block, `mat4Blocks toyZeroSum`, whose value is given explicitly. -/
theorem toy_zeroSum_external :
    external toy_conditions.thirtyFive toyZeroSum =
        ![15, 18, 21, 16, 14, 17, 20, 15, 13, 16, 19, 14, 16, 7, 27, 13] ∧
      external toy_conditions.thirtyFive toyZeroSum = mat4Blocks toyZeroSum := by
  decide

/-- Outside the subspace the blockwise form fails: on `(0, 1, …, 15)` the external layer is not
`mat4Blocks`. -/
theorem toy_external_ne_mat4Blocks :
    (fun i : Fin 16 => ((i : ℕ) : F)) ∉ blockSumZeroFlat ∧
      external toy_conditions.thirtyFive (fun i : Fin 16 => ((i : ℕ) : F)) ≠
        mat4Blocks (fun i : Fin 16 => ((i : ℕ) : F)) := by
  rw [mem_blockSumZeroFlat]
  decide

/-- The subspace has dimension `12` over `ZMod 29`. -/
theorem toy_finrank_blockSumZeroFlat : Module.finrank F (blockSumZeroFlat (K := F)) = 12 :=
  finrank_blockSumZeroFlat

/-- **The blockwise form over the KoalaBear modulus**, at the level of the ring: a state with zero
position sums, and `mdsLight` of it equal to `mat4Blocks` of it, with the value given
explicitly. -/
theorem koalaBear_zeroSum_mdsLight :
    positionSums (R := ZMod 2130706433)
        ![0, 1000010, 8000038, 27000102, 64000220, 125000410, 216000690, 343001078, 512001592,
          729002250, 1000003070, 1331004070, 1554704621, 1275703763, 906702635, 429701183] = 0 ∧
      mdsLight (R := ZMod 2130706433)
        ![0, 1000010, 8000038, 27000102, 64000220, 125000410, 216000690, 343001078, 512001592,
          729002250, 1000003070, 1331004070, 1554704621, 1275703763, 906702635, 429701183] =
        ![38000170, 53000236, 98000392, 63000252, 1062003438, 1305004188, 1650005244,
          1219003916, 1280604208, 2039606506, 841902893, 1665605370, 1880805050, 863801936,
          1671504337, 1313803328] ∧
      mdsLight (R := ZMod 2130706433)
        ![0, 1000010, 8000038, 27000102, 64000220, 125000410, 216000690, 343001078, 512001592,
          729002250, 1000003070, 1331004070, 1554704621, 1275703763, 906702635, 429701183] =
        mat4Blocks
          ![0, 1000010, 8000038, 27000102, 64000220, 125000410, 216000690, 343001078, 512001592,
            729002250, 1000003070, 1331004070, 1554704621, 1275703763, 906702635, 429701183] := by
  decide

end Poseidon2.Plonky3.Checks

/-- info: 'Poseidon2.Plonky3.mdsLight_eq_mat4Blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.mdsLight_eq_mat4Blocks

/-- info: 'Poseidon2.Plonky3.positionSums_mdsLight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.positionSums_mdsLight

/-- info: 'Poseidon2.Plonky3.finrank_blockSumZeroFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.finrank_blockSumZeroFlat

/-- info: 'Poseidon2.Plonky3.blockOf_external_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.blockOf_external_of_mem

/-- info: 'Poseidon2.Plonky3.external_mem_blockSumZeroFlat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.external_mem_blockSumZeroFlat_iff

/-- info: 'Poseidon2.Plonky3.Checks.toy_zeroSum_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.toy_zeroSum_external

/-- info: 'Poseidon2.Plonky3.Checks.koalaBear_zeroSum_mdsLight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Poseidon2.Plonky3.Checks.koalaBear_zeroSum_mdsLight
