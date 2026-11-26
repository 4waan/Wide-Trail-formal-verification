# How the HADES activity proof works

The result concerns two distinct inputs executed with the same fixed round
additions. A round first adds its value, applies coordinate S-boxes at its mask,
and applies its invertible linear map. The initial difference is nonzero.

`RoundSpec` carries inverses for both layers. Composition gives an inverse for
each finite execution, so distinct inputs remain distinct at every boundary.
This is the only property required from the middle rounds by the outer bound.

Write `T n` for the difference at the input of round `n`. Adding the same value
to both executions cancels in the difference. `nonlinearDifference` records the
actual difference after that round's masked S-box layer. It depends on the two
inputs, not just on `T n`.

Injectivity gives equality of supports before and after each coordinate layer:
equal inputs give equal outputs, and unequal inputs give unequal outputs. At
coordinates outside the mask the map is the identity, so even the difference
value is unchanged. Mixing gives the exact next-step equation:

```text
T (n + 1) = (rounds n).lin (nonlinearDifference rounds x y n)
```

The distinction between activity and charged activity is essential.
`weight (T n)` counts every nonzero word. `sboxWeight mask (T n)` counts only
nonzero words in the mask. A full round charges the whole support, while a
partial round may charge zero despite a nonzero state difference.

For two adjacent full rounds, the first input and nonlinear output have the
same weight. Apply the branch bound to that nonlinear output and its mixed
image. It follows that the two round inputs together charge at least `B`.
The second round's mixing is not needed for this pair.

`pair_sum_bound` tiles a full-round window with disjoint adjacent pairs. Each
pair costs `B`. If one round remains, its input difference is nonzero, so its
full mask charges at least one. A window of length `l` therefore costs
`(l / 2) * B + l % 2`.

For a prefix of `r` full rounds and a suffix of `s` full rounds, apply the window
theorem twice. The suffix starts at `r + m`; its initial difference is nonzero
because the entire preceding execution is injective. Sum decomposition keeps
the windows disjoint and leaves the middle's nonnegative charged count:

```text
(r / 2 + s / 2) * B + r % 2 + s % 2
  <= scheduledWeight rounds T 0 (r + m + s)
```

No adjacent pair jumps across the middle. There is no claim that inserting
arbitrary rounds improves security. The statement is an activity bound under
the named branch and bijectivity assumptions.

For an MDS matrix acting on `Fin t -> K`, the algebra layer proves `B = t + 1`.
The `hades_mds_bound` corollary uses that existing theorem. Its matrix agreement
conditions apply only inside the outer blocks, so internal matrices may differ
and the final mixing can be omitted.

The toy cipher uses `F_5`, cubing, matrix `[[1,1],[1,2]]`, and masks full, full,
`{0}`, full, full. Its minimum charged count is six. A separate pair has charged
count seven and ordinary activity eight, exposing the extra identity coordinate
that an unmasked count would incorrectly charge. Replacing mixing with the
identity gives only four; collapsing the middle makes the suffix difference
zero. The counterexamples make both assumptions observable.

The probability extension is implemented in `Counting.lean`, `Probability.lean`,
and `Differential/Scheduled.lean`. It counts an additional independent uniform
key per round. Fixed round additions are not independent random round keys,
and a trail bound still concerns one summand of a differential hull; the last section
below bounds the whole sum over two full rounds, in the same model. Polynomial degree,
subspace trails, sponge security, and implementation equivalence need separate
statements.

## Partial rounds

A difference is inactive in a round when it vanishes on every S-box coordinate of
that round's mask. An inactive round sends the difference through its linear map
and nothing else: the S-box coordinates carry zero in and zero out, and the other
coordinates are untouched (`IsTrail.succ_of_inactive`). A run of inactive rounds
sharing one linear map `L` is therefore a run of multiplications by `L`, and the
differences that survive `r` such rounds form the subspace

```text
inactiveSpace L mask r = { a | (L ^ j) a i = 0 for all j < r and i in mask }.
```

If that subspace is `⊥`, no nonzero difference crosses `r` middle rounds without
an active S-box (`IsTrail.active_in_window`). Tiling `m` middle rounds with
disjoint windows of length `r` gives `m / r` more (`IsTrail.middle_bound`), and
the three blocks add:

```text
(r / 2 + s / 2) * B + r % 2 + s % 2 + m / w
  <= scheduledWeight rounds T 0 (r + m + s)
```

The other direction is `IsTrail.free_window`: a difference inside the inactive
space crosses its window with no charge, whatever the S-boxes and constants are.
`inactiveSpace_ne_bot` shows by rank-nullity that `r` rounds with
`r * mask.card < width` always leave such a difference. For one S-box coordinate
the space is the kernel of a Krylov matrix, so a window can only be useful once it
is at least as long as the width.

`hades_probability_with_middle` carries the extra `m / w` into the
independent-key trail count. The sample space and its caveats are unchanged.

## Exact ratios

`hades_probability` charges a whole number `d` of bits per charged S-box, from
`u * 2^d <= card K`. Rounding `card K / u` down to a power of two loses up to one bit
per S-box. The trail count is a product of per-round masked counts
(`keyCount_eq_prod`). Each charged coordinate contributes at most `u` and every other
coordinate at most `card K`, so with `W = scheduledWeight rounds T 0 R`
(`keyCount_weight_bound_exact`):

```text
keyCount * card K ^ W <= u ^ W * card (Idx -> K) ^ R
```

The activity theorems give only a lower bound `A <= W`.
`keyCount_weight_bound_exact_of_le` replaces `W` by `A`: if `u <= card K`, each surplus
charged S-box multiplies the left side by `card K` and the right side by at most that;
otherwise the trail count is at most the number of key sequences
(`keyCount_le_card_pow`). `hades_probability_exact` and
`hades_probability_with_middle_exact` are the outer and the outer-plus-middle counts in
this form. No relation between `u` and `card K` is assumed.

A power of two is recovered at the end. `mul_le_of_ratio` turns `n * q <= v * N` and
`e * v <= q` into `n * e <= N`. With `q = p ^ A`, `v = u ^ A` and `e = 2 ^ E`, what remains
is the closed inequality `2 ^ E * u ^ A <= p ^ A`, which the kernel decides. For the pinned
instances the largest such `E` is 989 for KoalaBear (`A = 33`, `u = 2`), 906 for BabyBear
(`A = 32`, `u = 6`) and 8554 for BN254 (`A = 34`, `u = 4`); each certificate's checks show
that `E + 1` fails. Rounding to whole bits per S-box gives the weaker 957, 896 and 8534,
which the earlier theorems state. All of these are bounds on one trail with an additional
independent uniform key per round.

## Exact dimensions, and a criterion for `diag d + J`

Rank-nullity says that `r` partial rounds with one S-box coordinate leave at least
`width - r` dimensions of inactive differences. `Dimension.lean` shows when that is exact.

The spaces form a decreasing chain with the recurrence

```text
inactiveSpace L mask (r + 1) = inactiveSpace L mask 1 ⊓ comap L (inactiveSpace L mask r)
```

(`inactiveSpace_succ`): a difference stays inactive through `r + 1` consecutive partial
rounds exactly when it is inactive in the first and its image under `L` stays inactive
through the next `r`. Once two consecutive spaces agree, every later one agrees
(`inactiveSpace_eq_of_succ_eq`). Each strict step lowers the dimension by at least one, so
the chain is constant from `width` rounds on (`inactiveSpace_eq_card`). That last space
`V` is invariant under `L` and contains every `L`-invariant subspace of differences that
are inactive in one round (`le_inactiveSpace_of_invariant`). Membership in `V` is
inactivity for every number of rounds, so `V = ⊥` exactly when no nonzero difference
stays inactive forever (`no_infinite_inactive_trail`).

In the other direction, one more round adds the `mask.card` conditions
`(L ^ r) a i = 0`, so it removes at most `mask.card` dimensions
(`finrank_inactiveSpace_sub_succ_le`). With one S-box coordinate and `V = ⊥`, the lower
bound `width - r` and the upper bound from the `width - r` further rounds that reach `⊥`
meet: the dimension is exactly `width - r` for `r <= width`
(`finrank_inactiveSpace_singleton`). With a larger mask one round can remove more than one
dimension; `Checks/Dimension.lean` shows it on a four-coordinate swap.

For the Poseidon2 internal layer `c • (diag d + J)` with `c ≠ 0`, whether `V = ⊥` at
coordinate `i0` depends only on the diagonal (`inactiveSpace_diagPlusOnes_card_eq_bot_iff`):
it holds exactly when the entries `d i`, `i ≠ i0`, are pairwise distinct. If
`d i = d j` for distinct `i, j ≠ i0`, the difference `e_i - e_j` has coordinate sum zero,
so the layer only scales it, and it never reaches `i0`. Conversely, on `V` the coordinate
sum vanishes, so the layer acts there as `c • diag d`, and multiplying by the factors
`d k - d l` for `l ≠ i0, k` isolates coordinate `k`. The entry `d i0` plays no role, and
no entry needs to be nonzero. Under the criterion the dimensions are exactly `width - r`
(`finrank_inactiveSpace_diagPlusOnes`).

This replaces a Krylov table by a handful of inequalities between diagonal entries. Over
the KoalaBear and BabyBear fields the entries `1, 2, 4, …, 2^13, 2^15` are pairwise
distinct (`diag_injOn`, by `decide`), so exactly `16 - r` dimensions stay inactive through
`r <= 16` consecutive partial rounds (`finrank_inactive_eq`), and BabyBear's thirteen
partial rounds leave exactly three (`finrank_partial_inactive`). BN254's internal matrix
is `diag (1, 1, 2) + J`, which gives `3 - r` (`finrank_internal_inactive`). Over
`ZMod 23`, `2^11 = 1` makes two entries coincide, and the criterion leaves a nonzero
difference inactive through sixteen consecutive partial rounds
(`Plonky3.Checks.twentyThree_inactive_ne_bot_by_criterion`), hence forever
(`no_infinite_inactive_trail`). These statements concern the differences that avoid the
partial-round S-boxes only, not subspace trails in general.

## The differential over two full rounds

A trail bound charges one summand of a differential. `Differential/Hull.lean` and
`Hull.lean` bound the sum, in the same additional-independent-key model.

Round `n` maps `z` to `lin n (γ n (z + k n))`, and `diffKeyCount` counts the key vectors
under which `(x, x + a)` ends at the difference `b`. Peeling the first key shows that the
count does not depend on `x` (`Scheduled.diffKeyCount_const`), and it composes as a sum
over the difference in between (`Scheduled.diffKeyCount_add`). Over two rounds, with
`β = (lin 1)⁻¹ b`:

```text
diffKeyCount 2 a b = Σ c, diffCount (γ 0) a c * diffCount (γ 1) (lin 0 c) β
```

For bricklayer rounds each factor is a product over coordinates. A nonzero term needs
`supp c = supp a` and `supp (lin 0 c) = supp β`, so `(c, lin 0 c)` is a nonzero codeword
of weight at least `B` supported on the `weight a + weight β` positions `S` of those two
supports. Fix `B - 1` positions `D` of `S`. Two such `c` that agree on `S \ D` differ by a
codeword supported on `D`, of weight below `B`, so they are equal. The factors on `D` are
at most `u` each. The factors on `S \ D` are summed over all values, by row sums on the
input side and column sums on the output side, which needs bijective S-boxes. Every factor
outside `S` is `diffCount 0 0 = card K`. The result is
(`Scheduled.diffKeyCount_two_round_bound`)

```text
diffKeyCount 2 a b * card K ^ (B - 1) <= u ^ (B - 1) * card (Idx -> K) ^ 2
```

In a longer schedule the other rounds are only required to be bijective
(`Scheduled.diffKeyCount_window_bound`). Rounds before the window keep the difference
nonzero and their rows sum to `card (Idx -> K)` per round; rounds after it have columns
that sum to the same. `diffKeyCount_bound_of_two_full_rounds` applies this to two adjacent
full HADES rounds, whose fixed constants `diffCount_addKey` absorbs, and
`hades_differential_bound` charges rounds `0` and `1` of a schedule.

The bound averages over the keys. `Differential/Checks/Hull.lean` takes a two-round cipher
over `ZMod 5` where the bound allows `100` of `625` key pairs and the maximum is `85`; with
both keys fixed to zero, one differential is realised by `5` of the `25` inputs, above the
bound (`Scheduled.HullChecks.toy_fixed_exceeds`). Only two rounds are charged, so for the
Poseidon2 instances the exponents are far below the trail exponents: 209 for KoalaBear,
198 for BabyBear and 754 for BN254, each the largest that the ratio allows. They do not
establish, for the permutation with its fixed constants, the designers' criterion that
every differential has probability at most `p ^ (-t)`.

The pinned BN254 width-three Poseidon2 certificate and the two SP1 width-sixteen
certificates use these results. See [the certificate](PRODUCTION_CERTIFICATE.md) for
their exact scope and source pins.
