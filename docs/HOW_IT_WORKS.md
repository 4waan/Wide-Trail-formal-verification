[WideTrail](../README.md) › [Documentation](README.md) › How it works

# How it works

The library turns a cipher's design into a few numbers, each a lower bound on the number of
S-boxes that every trail activates, and proves each bound in Lean.

## The shape of a round

An AES-like round has three steps: an S-box layer γ, a shuffle π and a mixing layer θ, one
after another. HADES partial rounds apply the S-box to one coordinate only.

```mermaid
flowchart LR
    A["state a"] --> S["γ: S-box layer\n(scrambles bytes, keeps zero/nonzero pattern)"]
    S --> P["π: shuffle layer\n(moves bytes between columns)"]
    P --> M["θ: mixing layer\n(spreads activity within a column)"]
    M --> B["state a′ (next round's input)"]
```

γ keeps the pattern of nonzero positions, and π only moves positions. So θ is the only step
that changes how many positions are active, and its branch number bounds from below the active
positions at its input and output together. A lower bound for θ is therefore a lower bound for
the whole round.

## The AES proof chain

The files build the proof up in layers, each one feeding the next:

```mermaid
flowchart TD
    L1["Lemma 1 (Columns.lean)\nactive columns -> B times as many active bytes"]
    L2["Lemma 2 (Dispersion.lean)\nbyte-level guarantee -> column-level guarantee, via a good shuffle"]
    T1["Theorem 1 (Activity.lean)\n2 rounds >= B active bytes"]
    T4["Theorems 2 & 3 (FourRound.lean)\n4 rounds >= B^2 active bytes"]
    SPEC["WideTrailSpec (Cipher.lean)\nn rounds >= floor(n/4) * B^2 + B if 2 rounds left over"]
    GRID["Grid.lean\nrows x cols state; diffusion optimal <-> offsets injective"]
    AES["AES.lean\nconditional on hmix: B=5 -> 25 per 4 rounds, 55 over AES-128"]
    RIJ["Rijndael.lean\nNb = 4, 6, 8; what Definition 5 does and does not decide"]
    GFMDS["Algebra layer: GF256.lean + MDS.lean\nbuild GF(2^8), prove MDS -> branch B"]
    AESMIX["Algebra layer: AESMix.lean\nthe real MixColumns matrix is MDS"]
    CONCRETE["AESMix.lean\nunconditional: 25 per 4 rounds, 55 over AES-128"]
    DIFF["Differential layer: Counts.lean\nDP as a Nat count; hull identity"]
    BRICK["Differential layer: Bricklayer.lean\nDP factors over bundles; exponent = weight"]
    MARKOV["Differential layer: Markov.lean\ncount round-key vectors -> rounds multiply"]
    TPROB["Differential layer: TrailProb.lean\ncount * 2^(d*W) <= |X|^r"]
    AESPROB["Differential layer: AESProb.lean\n2^-150 per 4 rounds, 2^-330 over AES-128"]
    LTRAIL["Linear layer: Character.lean + Trail.lean\nWalsh values; fixed-key sum over trails"]
    LHULL["Linear layer: Hull.lean\ntwo-round hull, independent keys"]
    LSBOX["Linear layer: AESSbox.lean\nS-box |correlation| <= 2^-3 (trace pairing)"]
    LAES["Linear layer: AES.lean\n4-round trail |correlation| <= 2^-75; ELP <= 2^-24"]

    L1 --> T1
    L1 --> T4
    L2 --> T4
    T1 --> T4
    T4 --> SPEC
    SPEC --> GRID
    GRID --> AES
    GRID --> RIJ
    GFMDS --> AESMIX
    AES --> CONCRETE
    AESMIX --> CONCRETE
    DIFF --> BRICK
    DIFF --> MARKOV
    BRICK --> TPROB
    MARKOV --> TPROB
    SPEC --> TPROB
    TPROB --> AESPROB
    CONCRETE --> AESPROB
    SPEC --> LTRAIL
    BRICK --> LTRAIL
    TPROB --> LTRAIL
    LTRAIL --> LHULL
    LHULL --> LAES
    LSBOX --> LAES
    AESMIX --> LAES
    AESPROB --> LAES
```

[`WideTrail/Propagation/Checks/`](../WideTrail/Propagation/Checks/),
[`WideTrail/Differential/Checks/`](../WideTrail/Differential/Checks/) and
[`WideTrail/Linear/Checks/`](../WideTrail/Linear/Checks/) sit beside this chain. They add no
theorem about the ciphers. They test the theorems above on small hand-built examples, measure
how tight the bounds are, and pin the axioms that the results depend on.

## The Poseidon2 and Poseidon proof chain

The HADES layer charges full and partial rounds separately. Each deployed instance then fixes
its field, matrices and constants and discharges every hypothesis. An arrow means that the
first box feeds the second.

```mermaid
flowchart TD
    MASK["Hades/Masked.lean, Schedule.lean<br/>masked S-boxes, full and partial rounds"]
    HB["Hades/Bounds.lean<br/>full rounds: B per pair of full rounds"]
    PROB["Hades/Counting.lean, Probability.lean<br/>count to trail bound, independent round keys"]
    WIN["Hades/Subspace.lean<br/>windows: m / w from the partial rounds"]
    CERT["Hades/WindowRelation.lean, Automaton.lean<br/>certificates, checked by decide +kernel"]
    MB["Hades/MiddleBound.lean<br/>any proved bound μ on the partial rounds"]
    HULL["Hades/Hull.lean<br/>two-round differential, independent keys"]
    INST["Poseidon2/, Poseidon/<br/>pinned field, matrices and constants,<br/>counts and exponents per instance"]
    KAT["Checks/ of each layer<br/>known-answer vectors, negative controls, exactness"]
    LIN["Linear/Hades.lean, Poseidon2.lean, Poseidon.lean<br/>the same counts for linear trails"]

    MASK --> HB
    MASK --> PROB
    HB --> PROB
    PROB --> WIN
    WIN --> MB
    CERT --> MB
    MB --> INST
    PROB --> HULL
    HULL --> INST
    INST --> KAT
    INST --> LIN
```

- **Full rounds.** `outerRound_bound` charges `(r / 2 + s / 2) * B + r % 2 + s % 2` S-boxes for
  `r` full rounds before and `s` after the partial rounds, with `B` a branch number of the
  full-round linear layer.
- **Partial rounds.** Windows give `m / w` (`outer_middle_bound`). Window relations and
  forward-space automata give larger bounds for a concrete matrix; the kernel checks them by
  `decide +kernel`, and `MiddleBound` adds any such bound to the count.
- **Pinning.** The instance files fix the parameters of a pinned source, and the `Checks/`
  files reproduce the upstream known-answer vectors. See
  [PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md).

## Why this is useful

Bounding what differential cryptanalysis can do against a cipher normally means checking or
searching large numbers of trails by hand or by program, one cipher at a time. This project
instead proves an activity bound that holds for a whole *family* of designs at once, AES
included, as long as the design has the wide-trail shape: an S-box layer, a mixing layer with
a known branch number, and a shuffle that spreads columns well. The differential layer turns
such counts into trail bounds, and bounds two-round differentials from the branch number
directly, in a model with independent round keys. The linear layer does the same for
correlations: the same activity counts bound the correlation of one linear trail, the cipher's
correlation under a fixed key is shown to be a sum over trails with key-dependent phases (signs
in the binary case), and a two-round linear hull is bounded in the independent-key model. Apart
from the toy ciphers of the checks, concrete linear trail and hull bounds are proved for AES
only, under the trace pairing; for the Poseidon and Poseidon2 instances only the linear
activity counts are unconditional (for Poseidon2, over the rounds after the initial external
layer), since no S-box correlation bound over a prime field is proved.

Two properties make the bounds useful:

- **Kernel-checked.** Lean's kernel, a small program, checks every proof step. If the project
  builds and the axiom audits pass, every theorem follows from its definitions with no
  unproved step. Whether a theorem says what you need depends on its statement and
  definitions. Read them, and see
  [What is proved and what is not](../README.md#what-is-proved-and-what-is-not).
- **Parametric.** The branch number, the state shape and the mixing layer are parameters. A
  new design with the same round structure needs only its own branch number and S-box facts
  proved; the counting argument is reused.

Activity counts become trail bounds once the S-box's differential uniformity is known, in the
model with an independent uniform key per round. A differential sums many trails, and fixed
public constants do not provide independent keys. `Differential/Hull.lean` and
`Hades/Hull.lean` bound a differential, the sum over all trails, but only over two full rounds
and only averaged over independent keys. Nothing here bounds a differential of a permutation
with fixed constants or under one fixed key.

Next: [LAYERS.md](LAYERS.md) for what each layer proves; then, for cryptographers,
[MECHANICS_HADES.md](../MECHANICS_HADES.md) and the other mechanics documents, and for zk
engineers, your instance in [PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md).
