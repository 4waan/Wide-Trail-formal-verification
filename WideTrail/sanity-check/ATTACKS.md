# Oracle pass: attacks on the formalisation

A Lean proof that compiles tells you one thing only: the term you wrote elaborates and
the kernel accepts it. It does not tell you that the statement means what you wanted, or
that the hypotheses are satisfiable, or that any of them is doing work. Those are
separate claims, and each one can be attacked.

This folder is the record of attacking them. The rule used throughout: an attack is not
an opinion about the code, it is a Lean declaration that either compiles or does not. If
the formalisation were broken in the way an attack describes, that declaration would
compile and the build would still be green, and the attack would have landed.

Everything below is in `Verification.lean`, `Tightness.lean` and `Axioms.lean` in this
folder. All of it is checked by the kernel, none of it by `native_decide`.

---

## Attack 1: the theorems are vacuous

**The failure being hunted.** `WideTrailSpec` bundles four hypotheses at once: the S-box
layer preserves support, the transposition is diffusion-optimal, the column map has
branch number `B`, and the column map is non-degenerate. If no single object satisfies all of
them together, then every theorem about a `WideTrailSpec` is true for the boring reason
and proves nothing. Nothing in the build would notice. Lean is perfectly happy to prove
theorems about structures that have no instances.

**What was run.** Construct one. `toySpec` is a `2 x 2` state over `GF(2)` with column
map `(x, y) -> (x + y, x)`, ShiftRows as its transposition, identity as its S-box layer.
Every field is discharged, the two about the column map by kernel `decide`
over the full 16-pattern difference space.

**Result.** It typechecks, so the hypothesis bundle has a model and the vacuity failure
is ruled out. `toySpec.fourRoundBound = 4` reduces by `rfl`.

**Where.** `Verification.lean`, `toySpec`.

---

## Attack 2: the branch number hypothesis is weaker than it looks

**The failure being hunted.** `toySpec` proves `IsColBranchBound (sqCol 2) toyMix 2`.
Suppose `IsColBranchBound` were malformed in a way that made it hold for any `B`
whatsoever. Attack 1 would still pass, the whole development would still compile, and the
number `B` in every statement would be meaningless.

**What was run.** Ask for one more. `IsColBranchBound (sqCol 2) toyMix 3`.

**Result.** It is refutable, by `decide`. So the predicate distinguishes `2` from `3` on
this cipher, `B = 2` is the exact branch number rather than a number the definition
accepts by accident, and the specification is not accidentally stronger than it claims.

**Where.** `Verification.lean`, `toyMix_branch_not_three`.

---

## Attack 3: diffusion optimality is inert

**The failure being hunted.** This is the sharpest one. `four_round_identical` takes
`DiffusionOptimal col p` as a hypothesis. A hypothesis that is never used is invisible:
the proof compiles, the statement looks strong, and the theorem is secretly a weaker
theorem wearing a stronger signature. Nothing in Lean flags an unused hypothesis in a
term-mode proof.

**What was run.** Build a cipher that satisfies every other hypothesis of
`four_round_identical` and violates its conclusion. Give the state a single column
holding all four bundles, so no transposition can be diffusion-optimal at all: two
bundles of that column have nowhere else to go. Use `M = I + J` over `GF(2)` as the
column map. Its bundle branch number is `4`, because if `w(x)` is even then `Mx = x` and
the total is `2 w(x) >= 4`, and if `w(x)` is odd then `Mx` is the complement of `x` and
the total is exactly `4`. `M` is an involution, so `e0 -> Me0 -> e0 -> Me0` is a real
four-round trail.

**Result.** That trail activates `1 + 3 + 1 + 3 = 8` S-boxes. Theorem 3 with this branch
number would promise `B^2 = 16`. The counterexample is stated as a single conjunction:
every hypothesis except diffusion optimality, all satisfied, and the negated conclusion,
all in one theorem. It compiles. Diffusion optimality therefore cannot be dropped, and
the proof of Theorem 3 genuinely consumes it.

**Where.** `Verification.lean`, `four_round_fails_without_dispersion` and
`noPi_trail_weight`.

---

## Attack 4: the two four-round theorems disagree

**The failure being hunted.** There are two four-round results here. Theorem 2 covers the
construction with two alternating round transformations, and gets `B(theta) * B(Theta)`.
Theorem 3 covers the single-round-transformation construction that AES actually uses, and
gets `B^2`. The paper asserts these achieve the same bound. Theorem 3 was proved directly
rather than by the paper's regrouping argument, because that regrouping produces the
round order `rho_b, rho_a, rho_b, rho_a` reading from the input while Theorem 2 is stated
for a trail starting with `rho_a`. A direct proof is a place for a constant to drift
without anything complaining.

**What was run.** Reach the same constant along the other route. Instantiate Theorem 2
with `Theta = pi . theta . pi`, feeding it the branch number that Lemma 2 supplies for
that composite, and see what constant comes out.

**Result.** `B * B`, the same constant Theorem 3 produces directly, with the same
hypotheses. The two routes agree, so the `B^2` in Theorem 3 is not an artefact of how it
was set up.

**Where.** `Verification.lean`, `thetaTheta_bound_matches`.

---

## Attack 5: the bound is not about the trail it claims to be about

**The failure being hunted.** The abstract theorems quantify over `WideTrailSpec.trail`.
A proof can be correct about a quantity subtly different from the one named in the
statement, and no amount of rereading the proof reliably catches that. The independent
check is to compute the real numbers from the same definition and compare.

**What was run.** Exhaustive search over all 16 difference patterns of `toySpec`,
unfolding `WideTrailSpec.trail` directly, for both the two-round and four-round windows,
bracketing the minimum from both sides.

**Result.**

| window | theorem promises | true minimum | verdict |
| --- | --- | --- | --- |
| 2 rounds | `B = 2` | exactly `2` | sound and tight |
| 4 rounds | `B^2 = 4` | exactly `6` | sound, loose by `2` |

The two-round bound is met exactly, so nothing is lost between the branch number and
Theorem 1. The four-round bound holds with slack, which is expected rather than a defect:
`B^2` multiplies two independent worst cases, Lemma 2 supplying `B` active columns in the
middle and Lemma 1 charging `B` bundles to each, and on a `2 x 2` state no single trail
realises both at once. What matters for this attack is the direction of the gap. A
computed minimum below the promised bound would have been a refutation.

**Where.** `Tightness.lean`.

---

## Attack 6: the kernel is not actually checking this

**The failure being hunted.** Two ways a green build stops meaning anything. A `sorry`
anywhere in the dependency graph, which surfaces as `sorryAx`. Or a `native_decide`,
which surfaces as `Lean.ofReduceBool` and moves the finite checks out of the kernel and
into the compiler plus whichever machine happened to run it. The second is a live risk
here, because this development leans on `decide` for the AES ShiftRows check and for
every toy cipher, and `native_decide` is the usual reflex when `decide` is slow.

**What was run.** `#print axioms` on all fifteen headline results, including every
`decide`-backed one, each wrapped in `#guard_msgs`.

**Result.** All fifteen report exactly `[propext, Classical.choice, Quot.sound]`. No
`sorryAx`, no `Lean.ofReduceBool`. Wrapping them in `#guard_msgs` converts the audit from
a claim into a regression test: if a later edit introduces a `sorry` or swaps a `decide`
for a `native_decide`, the reported axiom list changes and this file stops compiling.

**Where.** `Axioms.lean`.

---

## One attack that failed to land, and why that mattered

The first attempt at Attack 3 reused the `2 x 2` toy cipher and simply removed the
transposition. Measured minimum over four rounds: `6` with ShiftRows, `5` without it,
against a promised `B^2 = 4`. Both above the bound. The counterexample did not exist.

That is not evidence that diffusion optimality is inert. It is evidence that the state
was too small to express the failure. With two columns of two bundles, a single active
bundle cannot avoid spreading. The failure needs a state where activity can stay confined
to one column across rounds, and one column of four bundles is the smallest such state,
which is why Attack 3 above abandons the square shape entirely and uses `Fin 4` with the
trivial column map.

Worth recording because a failed attack reads exactly like a passed test, and the
difference between "no counterexample exists" and "my search space could not contain one"
is the whole value of the exercise.

---

## What is still assumed

These are not attacks that failed. They are places the formalisation stops, stated so
nobody reads the AES numbers as more than they are.

**MixColumns being MDS is a hypothesis, not a theorem.** `aesSpec` takes
`IsColBranchBound (sqCol 4) mix 5` as an argument. Nothing in this repo proves that the
actual AES MixColumns matrix over `GF(2^8)` has branch number `5`. That is a real
theorem about a specific MDS matrix and it is not done here. Every AES number, the `25`
over four rounds and the `50` over ten, is conditional on the caller supplying it.

**Active S-box counts are not probabilities.** The theorems count active S-boxes. Turning
`25` into a bound like `2^-150` needs the maximum differential probability of the AES
S-box, which is `2^-6`, plus the standard assumption that trail probabilities multiply
across rounds. That assumption is a heuristic about independence, it is not proved here,
and it is not a theorem in general.

**A trail is not a differential.** These bounds constrain a single trail. Many trails can
share the same input and output difference and their probabilities add, which is trail
clustering. Nothing here bounds a differential, only each trail in it.

**Single key only.** Every theorem is about one trail through the round function, with
the round keys absorbed into the S-box layer by `PreserveSupport`. That absorption is
exactly what makes related-key analysis out of scope: in the related-key setting the key
schedule injects differences, and no theorem here says anything about it.

**Ten rounds gives `50`, not the best possible.** `aes128_ten_round` chains two disjoint
four-round blocks and discards the remaining two rounds. It is a lower bound on a lower
bound.

---

## Reproducing

```
lake build
```

Every attack in this folder is part of the default build target. A regression in any of
them fails the build rather than printing a warning.
