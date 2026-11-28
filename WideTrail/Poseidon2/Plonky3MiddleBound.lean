/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon2.Plonky3
import WideTrail.Hades.MiddleBound

/-!
# The width-sixteen Plonky3 permutation with a middle bound

`WideTrail.Poseidon2.Plonky3` charges the `rP` partial rounds of `Diag.rounds` through windows:
`Diag.activity_with_middle` adds `rP / w` to the `32` S-boxes of the full rounds when no nonzero
difference stays inactive through `w` consecutive partial rounds. This file states the same
results with any middle bound (`Hades.MiddleBound`, `WideTrail.Hades.MiddleBound`) for the
unscaled internal layer `diag d + J` in place of `rP / w`.

## Results, for every diagonal `d`, scale `c` and round-constant table

* `Diag.middleBound_internal`: for `c ≠ 0`, a middle bound holds for the internal layer
  `c • (diag d + J)` exactly when it holds for `diag d + J`. So a bound for `diag d + J` (for a
  concrete field, a certificate that does not mention `c`) applies to the code's layer with its
  Montgomery factor.
* `Diag.activity_with_middle_bound`: if every trail through `rP` consecutive partial rounds with
  `diag d + J`, from a nonzero difference, charges at least `μ` S-boxes, then two distinct inputs
  incur at least `32 + μ` charged S-box applications over the `8 + rP` rounds.
* `Diag.independent_key_probability_with_middle_bound`,
  `Diag.independent_key_probability_with_middle_bound_exact`,
  `Diag.independent_key_probability_with_middle_bound_sharp`: under the same hypothesis, if `sbox`
  has differential uniformity at most `u`, then for every nonzero trail `T`,
  `keyCount * 2^(dd (32 + μ)) ≤ |K^16|^(8 + rP)` when `u * 2^dd ≤ |K|`,
  `keyCount * |K|^(32 + μ) ≤ u^(32 + μ) * |K^16|^(8 + rP)` with no relation between `u` and `|K|`,
  and `keyCount * 2^e ≤ |K^16|^(8 + rP)` whenever `2^e u^(32 + μ) ≤ |K|^(32 + μ)` and `0 < u`.

With `μ = rP / w` from `Hades.MiddleBound.of_inactiveSpace` these are the `_with_middle` results
of `WideTrail.Poseidon2.Plonky3`. The SP1 schedule `Plonky3.rounds hK` is `Diag.rounds hK.toDiag`
by `rfl`, so the results apply to it with `d = sp1Diag K`.

## What is not claimed

No middle bound is proved here: `μ` is a hypothesis, to be discharged for a concrete field and
diagonal. The activity counts are lower bounds on charged S-boxes for actual input pairs, not
claimed to be attained. The probability statements concern one trail in the model with an
additional independent uniform key per round: not the permutation with its fixed constants, not a
differential, and not any one key.
-/

set_option autoImplicit false

namespace Poseidon2.Plonky3.Diag

variable {K : Type*} [Field K] [DecidableEq K]

/-- **The scale is invisible to middle bounds**, for every diagonal: for `c ≠ 0`, a middle bound
holds for the internal layer `c • (diag d + J)` exactly when it holds for `diag d + J`. -/
theorem middleBound_internal (d : Fin 16 → K) (c : K) (hc : c ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hs : 1 + ∑ i, (d i)⁻¹ ≠ 0) (mask : Finset (Fin 16)) (m μ : ℕ) :
    Hades.MiddleBound (internal d c hc hd hs).toLinearMap mask m μ ↔
      Hades.MiddleBound (diagPlusOnes (1 : K) d) mask m μ := by
  rw [internal_toLinearMap, diagPlusOnes_eq_smul, Hades.MiddleBound.smul_iff hc]

variable {d : Fin 16 → K} {c : K}

omit [DecidableEq K] in
/-- The partial rounds of `Diag.rounds` have the internal layer `c • (diag d + J)` as their
linear map. -/
theorem rounds_lin_middle (hD : Conditions d c) (rP : ℕ) (sbox : K ≃ K)
    (values : ℕ → Fin 16 → K) {j : ℕ} (hj : j < rP) :
    ((rounds hD rP sbox values (4 + j)).lin : Module.End K (Fin 16 → K)) = diagPlusOnes c d :=
  congrArg LinearEquiv.toLinearMap (linear_middle hD rP hj)

/-- **The full rounds and a middle bound, for every diagonal.** If every trail through `rP`
consecutive partial rounds with the unscaled layer `diag d + J`, starting from a nonzero
difference, charges at least `μ` S-boxes (`hμ`), then for every S-box, scale and constant table,
two distinct inputs incur at least `32 + μ` charged S-box applications over the `8 + rP` rounds:
`8` for each of the two pairs of full rounds on each side, and `μ` in the partial rounds. A lower
bound; it is not claimed to be attained. -/
theorem activity_with_middle_bound (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {μ : ℕ} (hμ : Hades.MiddleBound (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) rP μ)
    {x y : Fin 16 → K} (hxy : x ≠ y) :
    32 + μ ≤ Hades.scheduledWeight (rounds hD rP sbox values)
      (Hades.differenceTrace (rounds hD rP sbox values)
        (external hD.thirtyFive x) (external hD.thirtyFive y)) 0 (8 + rP) := by
  have h := Hades.outer_middle_bound_of (rounds hD rP sbox values)
    (fun h => hxy ((external hD.thirtyFive).injective h)) 4 rP 4 8 μ
    (fun j hj => Hades.hadesMask_prefix 4 rP 4 _ hj)
    (fun j hj => Hades.hadesMask_suffix 4 rP 4 _ hj)
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP)
    (diagPlusOnes c d) {0} (fun j hj => rounds_lin_middle hD rP sbox values hj)
    (fun j hj => Hades.hadesMask_middle 4 rP 4 _ hj) (hμ.diagPlusOnes hD.scale)
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact le_trans (le_of_eq (by norm_num)) h

variable [Fintype K]

/-- **Trail bound with a middle bound, for every diagonal.** If `sbox` has differential
uniformity at most `u` and `u * 2^dd ≤ |K|`, then under the middle-bound hypothesis of
`Diag.activity_with_middle_bound`, for every nonzero trail `T`, the number of key sequences
realising `T`, times `2^(dd (32 + μ))`, is at most the number of all key sequences. This concerns
one trail in the model with an additional independent uniform key per round: not the permutation
with its fixed constants, and not a differential. -/
theorem independent_key_probability_with_middle_bound (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u dd μ : ℕ} (hu : IsDiffUniform sbox u) (hd : u * 2 ^ dd ≤ Fintype.card K)
    (hμ : Hades.MiddleBound (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) rP μ)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * 2 ^ (dd * (32 + μ))
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have h := Hades.hades_probability_with_middle_bound (Idx := Fin 16) (K := K) (u := u)
    (d := dd) 4 rP 4 8 μ {0} (fun _ _ => sbox) (linear hD rP) values (fun _ _ _ => hu) hd
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP) (diagPlusOnes c d)
    (fun j hj => congrArg LinearEquiv.toLinearMap (linear_middle hD rP hj))
    (hμ.diagPlusOnes hD.scale) h0 x
  rw [show dd * ((4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 + μ) = dd * (32 + μ) by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

/-- **Trail bound with a middle bound, as an exact ratio, for every diagonal.** If `sbox` has
differential uniformity at most `u`, then under the middle-bound hypothesis of
`Diag.activity_with_middle_bound`, for every nonzero trail `T`, the number of key sequences
realising `T`, times `|K|^(32 + μ)`, is at most `u^(32 + μ)` times the number of all key
sequences. No relation between `u` and `|K|` is assumed. This concerns one trail in the model with
an additional independent uniform key per round: not the permutation with its fixed constants,
and not a differential. -/
theorem independent_key_probability_with_middle_bound_exact (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u μ : ℕ} (hu : IsDiffUniform sbox u)
    (hμ : Hades.MiddleBound (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) rP μ)
    {T : ℕ → Fin 16 → K} (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * Fintype.card K ^ (32 + μ)
      ≤ u ^ (32 + μ) * Fintype.card (Fin 16 → K) ^ (8 + rP) := by
  have h := Hades.hades_probability_with_middle_bound_exact (Idx := Fin 16) (K := K) (u := u)
    4 rP 4 8 μ {0} (fun _ _ => sbox) (linear hD rP) values (fun _ _ _ => hu)
    (full_prefix hD hprimes rP) (full_suffix hD hprimes rP) (diagPlusOnes c d)
    (fun j hj => congrArg LinearEquiv.toLinearMap (linear_middle hD rP hj))
    (hμ.diagPlusOnes hD.scale) h0 x
  rw [show (4 / 2 + 4 / 2) * 8 + 4 % 2 + 4 % 2 + μ = 32 + μ by norm_num] at h
  rw [show 8 + rP = 4 + rP + 4 by omega]
  exact h

/-- **Trail bound with a middle bound and a power of two, for every diagonal.** If `sbox` has
differential uniformity at most `u`, `0 < u`, and `2^e u^(32 + μ) ≤ |K|^(32 + μ)`, then under the
middle-bound hypothesis of `Diag.activity_with_middle_bound`, for every nonzero trail `T`, the
number of key sequences realising `T`, times `2^e`, is at most the number of all key sequences.
It follows from `Diag.independent_key_probability_with_middle_bound_exact` by
`Hades.mul_le_of_ratio`; for a concrete field the hypothesis on `e` is closed by `decide`. This
concerns one trail in the model with an additional independent uniform key per round: not the
permutation with its fixed constants, and not a differential. -/
theorem independent_key_probability_with_middle_bound_sharp (hD : Conditions d c)
    (hprimes : ∀ p ∈ m4Primes, (p : K) ≠ 0) (rP : ℕ) (sbox : K ≃ K) (values : ℕ → Fin 16 → K)
    {u μ e : ℕ} (hu : IsDiffUniform sbox u) (hu0 : 0 < u)
    (hμ : Hades.MiddleBound (diagPlusOnes (1 : K) d) ({0} : Finset (Fin 16)) rP μ)
    (he : 2 ^ e * u ^ (32 + μ) ≤ Fintype.card K ^ (32 + μ)) {T : ℕ → Fin 16 → K}
    (h0 : T 0 ≠ 0) (x : Fin 16 → K) :
    Hades.keyCount (rounds hD rP sbox values) (8 + rP) T x * 2 ^ e
      ≤ Fintype.card (Fin 16 → K) ^ (8 + rP) :=
  Hades.mul_le_of_ratio
    (independent_key_probability_with_middle_bound_exact hD hprimes rP sbox values hu hμ h0 x) he
    (pow_pos hu0 _)

end Poseidon2.Plonky3.Diag
