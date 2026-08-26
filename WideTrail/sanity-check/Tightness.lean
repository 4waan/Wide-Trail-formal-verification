/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.«sanity-check».Verification

/-!
# How much slack is in the bounds

A lower bound that is far below the truth is still a true theorem and still a useless
one. This file measures the gap on the one cipher small enough to search exhaustively:
`toySpec`, a `2 × 2` state over `GF(2)` with `B = 2`, whose whole difference space is 16
patterns. The kernel enumerates all of them.

The result splits:

* the two-round bound is exactly tight. Theorem 1 promises `B = 2` active S-boxes and a
  real trail achieves `2`, so nothing was lost between the branch number and the theorem.
* the four-round bound is loose here. Theorem 3 promises `B² = 4` and the true minimum
  over all trails is `6`.

The four-round gap is expected rather than a defect. `B²` comes from multiplying two
independent worst cases: Lemma 2 supplies `B` active columns in the middle, and Lemma 1
charges `B` bundles to each of them. On a `2 × 2` state those two worst cases cannot be
realised by the same trail, so no trail pays only `B²`. The theorem is a bound over all
wide-trail ciphers of this shape, not a prediction for one of them.

What the measurement does rule out is the failure mode where a proof is accidentally
about a different, weaker quantity than the one named in the statement. The numbers here
are computed from `WideTrailSpec.trail`, the same definition the theorems quantify over.
-/

set_option autoImplicit false

-- The kernel enumerates all 16 difference patterns and unfolds four rounds on each,
-- which needs more than the default recursion budget.
set_option maxRecDepth 4000

/-! ### Two rounds: the bound is met exactly -/

/-- Every nonzero two-round trail of `toySpec` activates at least `2` S-boxes. This is
`WideTrailSpec.two_round` for this cipher, recomputed by exhaustive search instead of
derived, so the two routes have to agree. -/
theorem toy_two_round_ge_two : ∀ a : SquareIdx 2 → Fin 2, a ≠ 0 →
    2 ≤ weight (toySpec.trail a 0) + weight (toySpec.trail a 1) := by decide

/-- Some trail activates exactly `2`, so `B = 2` cannot be raised. The two-round bound is
tight. -/
theorem toy_two_round_not_three : ¬ ∀ a : SquareIdx 2 → Fin 2, a ≠ 0 →
    3 ≤ weight (toySpec.trail a 0) + weight (toySpec.trail a 1) := by decide

/-! ### Four rounds: the bound holds with slack -/

/-- The promised four-round bound for this cipher. -/
example : toySpec.fourRoundBound = 4 := rfl

/-- The true four-round minimum is `6`, comfortably above the promised `4`. Theorem 3 is
therefore sound on this cipher, and not tight on it. -/
theorem toy_four_round_ge_six : ∀ a : SquareIdx 2 → Fin 2, a ≠ 0 →
    6 ≤ weight (toySpec.trail a 0) + weight (toySpec.trail a 1)
      + weight (toySpec.trail a 2) + weight (toySpec.trail a 3) := by decide

/-- And `6` is exactly the minimum, not a bound that happens to hold. So the slack in
Theorem 3 on this cipher is exactly `2` active S-boxes, measured rather than guessed. -/
theorem toy_four_round_not_seven : ¬ ∀ a : SquareIdx 2 → Fin 2, a ≠ 0 →
    7 ≤ weight (toySpec.trail a 0) + weight (toySpec.trail a 1)
      + weight (toySpec.trail a 2) + weight (toySpec.trail a 3) := by decide
