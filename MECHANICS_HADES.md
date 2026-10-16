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

The probability extension is a later job. In particular, fixed round additions
are not independent random round keys, and a trail bound would still concern
one summand of a differential hull. Polynomial degree, subspace trails, sponge
security, and implementation equivalence need separate statements.
