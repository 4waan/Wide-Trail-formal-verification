# Oracle pass: attacks on Differential layer

Same rule as [`Propagation/Checks/ATTACKS.md`](../../Propagation/Checks/ATTACKS.md): an
attack is not an opinion, it is a Lean declaration that either compiles or does not. All of
it is checked by the kernel, none of it by `native_decide`.

Differential layer is where the numbers stop being combinatorics and start being probabilities, which
is where a formalisation is most likely to be quietly assuming its conclusion. Three of the
four attacks below are aimed at the hypotheses rather than the theorems.

The declarations live in `Toy.lean` and `Axioms.lean` in this folder, on a two-bundle state
over `ZMod 4`, sixteen states in all, which the kernel enumerates in full.

---

## Attack 1: the differential uniformity constant is unattainable

**The failure being hunted.** `IsDiffUniform F u` is a hypothesis. If the toy S-box's true
uniformity were `4` and the file claimed `2`, every bound derived from it would be false but
nothing would fail to compile, because the hypothesis would simply never be discharged
anywhere the kernel could see.

**What was run.** `toy_diffUniform : IsDiffUniform sb 2` and
`toy_not_diffUniform_one : ¬ IsDiffUniform sb 1`, both by `decide`. The constant is attained
and cannot be lowered, so the bound is being fed a value the S-box actually meets and not a
value it beats by a mile.

**Verdict.** Survives. The uniformity is exactly `2` out of `4`.

---

## Attack 2: the product over bundles is not the product it claims

**The failure being hunted.** `diffCount_bricklayer` says a bricklayer's differential count is
`∏ i, diffCount (s i) (a i) (b i)`. A proof of this shape can go through while quietly being
about a different indexing, a different set, or a vacuous product.

**What was run.** `toy_bricklayer_factors` computes both sides on a concrete pair by
independent routes: the left by scanning all `16` states of the two-bundle space, the right by
two scans of the `4` states of one bundle. `decide` settles the equality of the two numbers.

**Verdict.** Survives.

---

## Attack 3: the Markov theorem is about something other than what it says

**The failure being hunted.** `trailKeyCount_eq_prod` is the load-bearing theorem of the
layer. It is proved by an induction that peels one round, and inductions that peel rounds are
exactly where an off-by-one in the trail indexing hides. Such an error produces a true theorem
about a shifted trail, and the build stays green.

**What was run.** `toy_trailKeyCount` enumerates all `16² = 256` round-key vectors of a
concrete two-round trail and reports `4`. `toy_trail_prod` multiplies the two per-round
differential counts and reports `4`. `toy_markov_matches` puts them together. The two numbers
come from computations with nothing in common except the theorem that relates them.

`toy_trailKeyCount_other` additionally recomputes the count from a different starting input
and gets the same `4`, which is the content of `trailKeyCount_const`.

**Verdict.** Survives.

---

## Attack 4: the Markov hypothesis is decorative

**The failure being hunted.** This is the important one. The whole layer is stated over
round-key vectors rather than over inputs, which is a strong modelling choice, and a reader is
entitled to ask whether it buys anything or whether the same result would hold for a fixed
key. If it would, the averaging is dead weight dressed up as rigour.

**What was run.** `toy_fixedKeyCount_zero`: under the all-zero round keys, **no** input pair
follows the trail whose key-averaged count is `4`. `toy_fixed_key_fails_markov` states the
consequence as an inequality the kernel checks: the fixed-key product formula would force
`0 · 16² = 16 · 4`, and it does not.

**Verdict.** The hypothesis is load-bearing. It cannot be dropped, and the theorem cannot be
restated for a fixed key.

There is a second, sharper reason, which is not formalised because it is an argument about
what *could* be formalised rather than a declaration. Assume the fixed-key product formula for
ten-round AES. Every nonzero trail has at least `55` active S-boxes
(`Propagation.aes128_ten_round`), so each would be followed by at most `2¹²⁸ · 2⁻³³⁰ < 1` inputs,
that is, by none. But for a fixed key every input pair follows some trail, so the counts must
sum to `2¹²⁸`. The fixed-key assumption is therefore inconsistent at that round count, and
anything proved from it would be vacuous. Differential layer avoids this by counting key vectors, which
makes the denominator `2¹²⁸ · 2¹²⁸⁰` instead of `2¹²⁸` and leaves the bound satisfiable.

---

## Attack 5: the trail bound is being sold as a differential bound

**The failure being hunted.** Every headline number in this project is about one trail. What
an attacker uses is a differential, and a differential is a sum over trails. If that gap is
mentioned in prose and nowhere else, a reader has no way to see how large it is.

**What was run.** `diffCount_comp` states the identity unconditionally: the differential count
of a composition is the sum over intermediate differences of the counts along each route. No
independence, no keys, no hypotheses. Then `toy_hull_total`, `toy_hull_split` and
`toy_hull_gap` exhibit a concrete instance: a two-round differential realised by `8` of the
`16` inputs, split as `4 + 4` across two intermediate differences. The best single trail
accounts for half of it.

**Verdict.** The gap is real and it is a factor of two on the smallest cipher that shows it.
Nothing in Layers 1 to 3 closes it. That is the honest status of every wide-trail figure in
the literature, and it is stated here as a compiled theorem rather than as a footnote.

---

## Attack 6: the finite checks moved trust out of the kernel

**The failure being hunted.** Differential layer's content is arithmetic on counts, and the toy checks
enumerate `256` round-key vectors. `native_decide` would make all of them faster and would
move the evidence to the compiler and the machine that ran it.

**What was run.** `Axioms.lean` reports the axiom footprint of all twenty-six headline results
under `#guard_msgs`, so a later edit that introduces a `sorry` or swaps a `decide` for a
`native_decide` stops the build rather than passing quietly. Every one reports
`[propext, Classical.choice, Quot.sound]`.

`Classical.choice` enters through Mathlib's `Finset` API and, additionally, through
`linAddEquiv`, which inverts a finite injective additive map with `Equiv.ofBijective`. That is
a construction of an inverse, not an assumption about a cipher.

**Verdict.** Survives.

---

## What is still assumed

* **The AES S-box's differential uniformity is `4`.** A hypothesis, exactly as
  `IsColBranchBound` was a hypothesis in Propagation layer, and unlike that one it is not discharged.
  A kernel `decide` over the difference distribution table is `256 · 256` differentials each
  scanning `256` inputs, and `Algebra/GF256.lean` records that enumerations of that size do not
  finish. Closing it is a separate piece of work about inversion in `GF(2⁸)`.
* **Round keys are independent and uniform.** Attack 4. Real AES has a key schedule.
* **The cipher is round-uniform.** The same `θ ∘ π` in every round; real AES omits
  `MixColumns` in the last one. The count is over the inputs to rounds `0 … r-1`, so the last
  round's linear layer is not what the bound rests on, but the statement is about the uniform
  cipher.
* **One trail, not one differential.** Attack 5.
* **The bound is not claimed to be tight.** `toy_bound_holds` promises `2⁻³` on a trail whose
  true key-averaged probability is `2⁻⁶`, because the toy S-box's actual differential counts
  are `1` where its uniformity allows `2`. A lower bound on a lower bound, as in Propagation layer.
