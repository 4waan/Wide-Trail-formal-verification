# Mechanics of Differential layer

How `WideTrail/Differential/` actually works. Layers 1 and 2 end with a number of active S-boxes.
Differential layer turns that number into a probability, and the interesting part is not the
arithmetic, it is which step needs an assumption and what the assumption costs.

## 1. Probability without division

A differential of `F` is a pair `(a, b)` of input and output difference, and its probability
is the fraction of inputs realising it. The file keeps the numerator:

```
diffSet   F a b = {x : F (x + a) - F x = b}     -- a Finset
diffCount F a b = |diffSet F a b|               -- a Nat
```

`DP = diffCount / |X|` is never formed. A claim of the form `DP ≤ 2⁻ᵈ` is written

```
diffCount * 2 ^ d ≤ |X|
```

which is exact `ℕ` arithmetic and, crucially, *decidable*: on a small cipher the kernel can
recompute the whole thing by enumeration, which is what
`Differential/Checks/Toy.lean` does. Reaching for `MeasureTheory` or `ℚ` would have bought
nothing and lost that.

Two facts about `diffCount` set up everything else.

**`diffCount F 0 b = |X|` if `b = 0`, and `0` otherwise.** A zero input difference always
gives a zero output difference. This is the `DP = 1` that lets an inactive bundle drop out of
a product.

**`∑ b, diffCount F a b = |X|`.** Each input realises exactly one output difference, so a row
of the difference distribution table sums to the size of the input space. This is
"probabilities add to one", proved by `Finset.card_eq_sum_card_fiberwise` on the map
`x ↦ F (x + a) - F x`. It is also the reason a bound on one differential is never a bound on
the family.

## 2. The join: `weight` becomes an exponent

`bricklayer s` applies `s i` independently in bundle `i`. Its differential set is a product:

```
diffSet (bricklayer s) a b = piFinset (fun i => diffSet (s i) (a i) (b i))
```

which is an `ext` plus `funext_iff`, and `Fintype.card_piFinset` turns it into

```
diffCount (bricklayer s) a b = ∏ i, diffCount (s i) (a i) (b i)
```

Now split the product over `activePattern a` and its complement, which is exactly Propagation layer's
support. On the support, each factor is at most the differential uniformity `u`, because
`a i ≠ 0`. Off it, each factor is at most `|K|`. So

```
diffCount (bricklayer s) a b ≤ u ^ weight a * |K| ^ (|Idx| - weight a)
```

Propagation layer's `weight` appears in a probability bound with no translation step at all. It was
defined as the size of the support, and the support is precisely the set of factors that are
not the whole of `|K|`. That is the entire content of "each active S-box costs a factor".

## 3. `PreserveSupport`, demoted from hypothesis to theorem

Propagation layer asks a `WideTrailSpec` for `PreserveSupport sbox`: the S-box layer moves no activity.
Read literally, that is a claim about a function on differences, and a real S-box layer has
no such function. Given an input difference it fixes only the *support* of the output
difference; which output difference actually occurs depends on the input.

`activePattern_eq_of_diffCount_ne_zero` states the honest version. If
`diffCount (bricklayer s) a b ≠ 0`, that is, if `b` is an output difference the layer can
actually produce from `a`, and if every `s i` is injective, then
`activePattern b = activePattern a`. The proof picks one `x` from the nonempty differential
set and reads it off coordinatewise: `a i = 0` forces `b i = 0`, and `a i ≠ 0` forces
`x i + a i ≠ x i`, so injectivity forces `b i ≠ 0`.

To let Propagation layer consume that, Propagation layer was generalised rather than worked around.
`lemma_two_pattern`, `two_round_pattern` and `four_round_pattern` take the intermediate
patterns `bᵢ` explicitly, constrained only by `activePattern bᵢ = activePattern aᵢ`, and
`WideTrailSpec.IsTrail` is the resulting multi-round hypothesis:

```
IsTrail S T r  =  ∀ n < r, ∃ b, activePattern b = activePattern (T n) ∧ T (n+1) = S.lin b
```

The functional trail is one instance of this (`isTrail_trail`, taking `b = S.sbox (T n)`), so
`trailWeight_bound_rounds` and everything downstream are corollaries of the general statement
rather than a parallel development. Nothing about the earlier statements changed.

## 4. Multiplying rounds, and where the assumption lives

The remaining step is that the trail's probability is the product of the per-round
probabilities. That is where independence enters, and it is worth being exact about what
goes wrong if it is assumed carelessly.

Suppose one assumed the product formula for a **fixed** key. Every ten-round AES trail out of
a nonzero difference has at least `55` active S-boxes, so its probability would be at most
`2⁻³³⁰`, so out of `2¹²⁸` inputs the number following it would be at most `2⁻²⁰²`, that is,
zero. But for a fixed key every input pair follows *some* trail, so the counts over all
trails must sum to `2¹²⁸`. A sum of zeros is not `2¹²⁸`. The fixed-key product formula is
inconsistent at this round count: any theorem proved from it would be vacuous.

So the model is not "assume probabilities multiply". The model is that the round keys are
independent and uniform, and the object counted is a pair of an input and a **round-key
vector**:

```
Follows lam γ r k T x   -- x and x + T 0 exhibit the differences T 0 … T r under keys k
trailKeyCount lam γ r T x = |{k : Fin r → X | Follows lam γ r k T x}|
```

The round-key space has `|X| ^ r` elements, so `trailKeyCount / |X| ^ r` is the trail's
probability averaged over independent round keys. With the model stated this way, the product
formula is a **theorem**:

```
trailKeyCount lam γ r T x = ∏ n < r, diffCount γ (T n) (lam⁻¹ (T (n+1)))
```

The mechanism is a change of variables. Write `yₙ = xₙ + kₙ` for the input to the S-box layer
in round `n`. Since `xₙ` depends only on `k₀ … kₙ₋₁`, the map `k ↦ y` is triangular, hence
bijective, and in the `y` coordinates the `r` conditions become `r` *independent* constraints,
one per coordinate. In Lean this is done by peeling the first round: `Follows` at `r+1` is
a condition on `k 0` conjoined with `Follows` at `r` on `Fin.tail k`, `card_filter_cons`
splits the count over `k 0` using `Fin.cons`/`Fin.tail` as mutually inverse maps, and
`Finset.prod_range_succ'` peels the matching factor off the product. The condition on `k 0`
is membership of `x + k 0` in a differential set, which is where `diffCount_addKey` (the key
is a bijection of the inputs) and `diffCount_addEquiv` (the linear layer relabels output
differences) do their work. Those two lemmas are the differential-probability form of Layer
1's remark that keys never appear in a wide-trail statement, and here it is a computation
rather than a hypothesis.

`Toy.lean` exhibits a cipher, a trail and a key where the key-averaged count is `4` and the
fixed-key count is `0`, so the averaging is not a technicality that could be removed later.

## 5. The arithmetic, once

Write `q = |K|`, `m = |Idx|`, `W = patternWeight T r`. The product formula and the bundle
bound give

```
trailKeyCount ≤ u ^ W * q ^ (r·m - W)
```

where `∑ (m - wₙ) = r·m - W` needs `wₙ ≤ m` because `ℕ` subtraction truncates
(`sum_sub_of_le`). If the uniformity clears a factor, `u · 2ᵈ ≤ q`, then

```
trailKeyCount · 2 ^ (d·W) ≤ (u·2ᵈ)^W · q^(r·m - W) ≤ q^W · q^(r·m - W) = q^(r·m) = |X|^r
```

and `W` is replaced by Propagation layer's lower bound by monotonicity of `2 ^ ·`. That is
`trailKeyCount_le_of_spec`, and every concrete number is that theorem at a numeral.

For AES: `q = 256`, `m = 16`, `u = 4`, and `4 · 2⁶ = 256`, so `d = 6`. Ten rounds, `55` active
S-boxes, `6 · 55 = 330`:

```
trailKeyCount aesLin (bricklayer s) 10 T x * 2 ^ 330 ≤ |X| ^ 10 = 2 ^ 1280
```

## 6. What is still assumed, and what is still open

**Discharged for AES: the concrete S-box obligations.** The generic `AESProb.lean`
API retains its explicit hypotheses. `Algebra/AESSbox.lean` defines the actual AES
byte substitution and its inverse. `Differential/Polynomial.lean` bounds inversion
by a quadratic root count plus two exceptional inputs. `AESConcrete.lean` moves
that bound through the additive affine equivalence and proves that four is attained.
Its concrete probability wrappers require no S-box hypotheses.

**Assumed: independent round keys.** Discussed above. Real AES has a key schedule.

**Open: the hull.** `diffCount_comp` is an unconditional identity: the differential count of
`G ∘ H` is the sum, over intermediate differences, of the counts along each route. A
wide-trail theorem bounds one summand. `Toy.lean` exhibits a two-round differential realised
by `8` inputs and split evenly between two intermediate differences accounting for `4` each,
so the best single trail is off by a factor of two on a cipher small enough to check by hand.
Nothing in Layers 1 to 3 bounds the sum, and that is the standard caveat on every wide-trail
figure in the literature, stated here as a theorem rather than as a remark.

**Modelled: a round-uniform cipher.** The same `λ = θ ∘ π` in every round. Real AES omits
`MixColumns` in the last round.
