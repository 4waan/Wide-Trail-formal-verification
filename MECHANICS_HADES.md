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
and a trail bound still concerns one summand of a differential hull. Polynomial degree, subspace trails, sponge
security, and implementation equivalence need separate statements.

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

The pinned BN254 width-three Poseidon2 certificate uses these results. See
[the certificate](PRODUCTION_CERTIFICATE.md) for its exact scope and source pin.
