# Next job: scheduled HADES rounds and an outer-round activity bound

Prepared 2026-10-16 after landing Differential layer at `42df69c`.

## Deliverable

Build an executable model with full and partial S-box rounds. Prove a lower bound
on the number of active S-box applications in the full-round blocks surrounding
the partial rounds. Connect that theorem to actual executions on two distinct
inputs, and check it on a small nonvacuous instance.

This is the first HADES milestone. Its result is a combinatorial theorem about
executions, with explicit assumptions. A later job can add the probability
theorems for an independently keyed model and concrete Poseidon2 parameters.

## Paper and study provenance

Primary paper: Grassi, Luftenegger, Rechberger, Rotaru, Schofnegger,
*On a Generalization of Substitution-Permutation Networks: The HADES Design
Strategy*, EUROCRYPT 2020, DOI `10.1007/978-3-030-45724-2_23`.

Sources checked:

- [Published conference text, 30 PDF pages](https://iacr.org/archive/eurocrypt2020/12105229/12105229.pdf).
  Read the construction, differential argument, algebraic analysis, parameter
  selection, and implementation discussion. The immediate proof target comes
  from Section 4.2, PDF pages 14 and 15, including footnote 12.
- [ePrint record and revision notice](https://eprint.iacr.org/2019/1107).
  The latest listed revision is 2020-07-14. It generalizes the power S-box and
  strengthens the linear-layer specification after subsequent cryptanalysis.
- [Updated ePrint text](https://eprint.iacr.org/2019/1107.pdf).
  Indexed excerpts of Section 3.1 and Supplementary Material A were accessible.
  Direct full-PDF retrieval returned HTTP 403. The entire revised supplementary
  material has therefore not been checked in this study. Before implementing a
  concrete matrix-selection criterion, obtain and pin the revised text and study
  the referenced matrix-screening algorithms in full.

Relevant reading conclusions: Section 2 gives the full/partial/full schedule;
Section 3.1 fixes concrete round conventions; Section 4.2 counts adjacent full
rounds separately on each side of the middle. Section 4.3 uses algebraic-degree
and attack-cost estimates. Those estimates are separate obligations from the
activity theorem. The revised matrix requirements also belong to a later
subspace-trail milestone.

## What must change in our model

The current `weight a` counts every nonzero coordinate. A partial round applies
an S-box only at selected coordinates. An identity coordinate can carry a nonzero
difference without contributing an S-box application. Preserve `weight` and
introduce a separate quantity:

```text
activeSboxes mask a = mask intersect activePattern a
sboxWeight mask a = card (activeSboxes mask a)
scheduledWeight masks T R = sum over n < R of sboxWeight (masks n) (T n)
```

For a full mask, `sboxWeight` must reduce to `weight`. For an empty mask it must
be zero. For a singleton mask it must be either zero or one.

This distinction also matters to Differential layer. Feeding an identity map into
`diffCount_bricklayer_le` with the nonlinear S-box's uniformity constant is
invalid: its nonzero-input differential can have the entire field as its count.
A future probability proof must charge only active coordinates in the mask.

The current `WideTrailSpec` also describes one repeated linear layer and uses a
column partition and dispersion. HADES's whole-state matrix does not need that
column structure. Put the new development beside the existing layers and reuse
the small support and branch lemmas. Avoid forcing a flat matrix into an AES
grid specification.

## Mathematical target

Let `X = Fin t -> K`. Consider a concrete execution with:

- `r` full rounds at the beginning;
- `m` bijective partial rounds in the middle;
- `s` full rounds at the end;
- bijective coordinate S-boxes and invertible linear layers;
- a branch bound `B` for every linear transition joining two adjacent full rounds
  within either outer block;
- any fixed round additions, applied equally to both executions.

For distinct inputs, let `T n` be the input difference before the S-box layer of
round `n`. The target theorem is:

```text
((r / 2) + (s / 2)) * B + (r % 2) + (s % 2)
  <= scheduledWeight masks T (r + m + s)
```

For a whole-state MDS matrix, instantiate `B = t + 1` using the existing
`isMDS_branch_bound`. For `r = s = 2`, the result is `2 * (t + 1)` even when
the middle contributes zero charged S-boxes.

Proof construction:

1. Each round is injective. Distinct inputs remain distinct, so every round-input
   difference is nonzero, including at the beginning of the suffix.
2. An injective coordinate layer preserves the support of a realizable difference.
   Outside the mask it also preserves the difference value exactly.
3. Each adjacent pair of full rounds costs at least `B` by the branch bound.
4. Tile each outer block into disjoint pairs. If the block has odd length, its
   remaining nonzero input costs at least one active S-box.
5. Add the two block bounds. All charged activity in the middle is nonnegative.

Never pair the last full round of the prefix with the first full round of the
suffix. They are separated by the middle computation. The proof does not need
to replace the middle with a linear map or claim that arbitrary insertions
monotonically improve security. It uses injectivity to establish the nonzero
entry difference for the second block.

An optional corollary can abstract the entire middle computation as `X equiv X`.
That abstraction must preserve the explicit execution boundary between blocks.

## Proposed files and interfaces

Create `WideTrail/Hades/` rather than renaming existing layers. The names below
are proposed interfaces, not declarations already implemented.

### `Masked.lean`

- Define `maskedBricklayer` through the existing `bricklayer`, using the S-box at
  mask coordinates and `id` elsewhere.
- Define `activeSboxes` and `sboxWeight`.
- Prove full-mask, empty-mask, singleton-mask, and weight upper-bound lemmas.
- Package bijective coordinate S-boxes as equivalences where that makes inverses
  executable. Prove masked-layer bijectivity and support preservation.
- Prove exact equality of input and output differences outside the mask.

Keep these definitions generic in the coordinate type. Arithmetic for actual
differences needs an additive group; counting activity needs much less. Finite
field cardinalities should enter only where a theorem actually needs them.

### `Schedule.lean`

- Define a round-indexed record carrying a mask, coordinate S-boxes, an invertible
  linear map, and an additive round value. Use a `LinearEquiv` for the linear map
  in the field-based execution model.
- Choose and document one execution convention, preferably
  `round n x = lin n (maskedBricklayer n (x + c n))`, matching Differential layer.
- Define finite execution, actual two-input difference traces, and total charged
  activity. Fix indexing so the count charges S-box inputs at rounds `0` through
  `R - 1`; the final output difference is available at index `R`.
- Define a schedule constructor from explicit prefix, middle, and suffix lengths.
  Prove its mask membership and boundary cases. Do not make the first core
  theorem depend on truncated `RF / 2` arithmetic or assume evenness silently.
- Prove execution bijectivity and nonzero differences for distinct inputs.

Round values are deterministic parameters here. They may later represent keys
or public constants. No distribution is attached to them by the execution API.

The paper presents both pre-addition and post-addition descriptions. Do not
identify their individual round functions with the same key. If both APIs are
introduced, prove the complete-cipher correspondence with explicit initial
whitening, final addition, and the correct reindexing of round values. The first
job can instead expose only the documented pre-addition convention.

Allow the final linear layer to be the identity. The full-round activity bound
needs branch assumptions only on transitions inside counted pairs, so it need
not require a final MixLayer that the model then omits.

### `Bounds.lean`

- Prove the adjacent-full-round branch lemma.
- Prove a shifted full-window bound
  `(length / 2) * B + length % 2 <= windowWeight`.
- Prove the two-block theorem above for actual executions.
- Supply an MDS corollary for `Fin t -> K` and the symmetric HADES schedule.

Reuse `weight_congr`, the support lemmas, `two_round_pattern` where suitable,
`isMDS_branch_bound`, and `isMDS_injective`. Reuse arithmetic decomposition ideas
from `Cipher.lean`, while keeping the new count and schedule explicit.

If an abstract trail relation helps the proof, relate successive patterns using
an explicit intermediate difference. Include both support preservation and exact
identity-coordinate propagation. Prove that actual executions satisfy the
relation before using it for the headline result. Do not define a nonlinear
S-box as a deterministic function on input differences.

### `Checks/Toy.lean` and `Checks/Axioms.lean`

Use a tiny prime-field instance to exhibit actual executions and challenge the
assumptions. The toy is a proof test, not a proposed cryptographic parameter set.

An independent Python enumeration performed while preparing this plan used:

```text
field: F_5
width: 2
S-box: x^3
matrix: [[1, 1], [1, 2]]
masks: full, full, {0}, full, full
pre-addition values: (0,1), (1,3), (2,0), (3,2), (4,4)
```

Across all 600 ordered distinct input pairs, the minimum masked count was `6`.
The pair `(0,0)` and `(1,0)` attained it. For `(0,0)` and `(0,1)`, masked counting
gave `7` while unmasked counting gave `8`.

During implementation, independently reconstruct that reference computation
and compare it with the Lean execution convention. Then kernel-check the
selected witnesses and, if measured to be practical, the finite universal bound.
Do not copy an expected answer into a test that calls only the bound theorem.

Additional adversarial checks:

- Use an invertible identity mixing layer to refute an unjustified MDS-sized
  bound when the branch assumption is removed.
- Use a singular middle map to show why the suffix's nonzero-entry condition
  needs injectivity.
- Cover zero-length middle, odd outer-block lengths, and schedule boundaries.
- Audit new headline declarations with the project's allowed axiom baseline.

## Implementation order and commit boundaries

1. `feat(hades): define masked S-box layers and charged activity`
   Add `Masked.lean` with its support and counting facts.
2. `feat(hades): model scheduled rounds and difference traces`
   Add `Schedule.lean`, fixed-value execution, and the schedule boundary proofs.
3. `feat(hades): prove activity bounds for full outer rounds`
   Add `Bounds.lean`, shifted windows, and MDS specializations.
4. `test(hades): check toy executions and audit proof axioms`
   Add the small examples and counterexamples, wire imports into `WideTrail.lean`,
   and document the result and its scope in `README.md`.

Each commit should compile independently. Add the corresponding imports as each
file lands so the default build checks the development throughout. Use no
co-author trailers.

## Completion criteria

- The generic scheduled execution and the main activity theorem compile without
  `sorry`, extra axioms, `native_decide`, or an axiom-producing decision fallback.
- `lake build` passes, including all existing guards and the new HADES guards.
- Check the transitive axiom footprint of all project declarations by their
  defining module, including declarations in the root namespace. The allowed
  baseline is `propext`, `Classical.choice`, and `Quot.sound`.
- Actual distinct-input executions satisfy the theorem's trace assumptions.
- The two toy counting witnesses match the independent reference, and the
  missing-assumption counterexamples compile.
- Existing Propagation layer to Differential layer results retain their statements and behavior.
- Documentation names the result as an active-S-box bound and states exactly
  which branch and bijectivity assumptions it consumes.

## Follow-on jobs, outside this implementation

After this milestone, generalize `Markov.lean` to round-indexed linear and masked
nonlinear layers. Prove the product formula in the explicitly independent-key
model and derive the masked count inequality using natural-number numerators.
Recover the current uniform/full-round theorem as a specialization. Keep this
separate from claims about fixed public constants.

A power-S-box job can discharge invertibility under the correct coprimality
condition and bound differential counts through polynomial root counting. An
upper bound on polynomial degree is not a lower bound on attack complexity.
Exact degree growth, cancellation, density, and solving-degree assumptions need
their own statements and evidence.

A matrix job should first finish checking the revised HADES source and the
referenced subspace-trail work. Its theorem must name the precise class of
subspace trails it excludes; MDS alone is only the branch-bound input used here.
The relevant follow-on primary source is
[Proving Resistance Against Infinitely Long Subspace Trails](https://doi.org/10.46586/tosc.v2021.i2.314-352).

Then study and pin the exact
[Poseidon2 specification](https://eprint.iacr.org/2023/323), including its initial
linear transformation and distinct external/internal layers, before selecting
production parameters. A later implementation-equivalence proof can target a
pinned Rust permutation or its constraints. The generic API permits varying
linear layers; it does not certify a Poseidon2 matrix in advance.

Sponge indifferentiability remains a separate roadmap branch. The existing AES
S-box uniformity gap also remains recorded in Differential layer and is not a dependency of
this activity theorem. This job makes no fixed-key probability, differential
hull, algebraic-attack resistance, sponge-security, or zkVM-soundness claim.
