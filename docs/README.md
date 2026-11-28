[WideTrail](../README.md) › Documentation

# Documentation

WideTrail proves, in Lean 4, lower bounds on the number of active S-boxes in every
differential and linear trail of AES and of deployed Poseidon2 and Poseidon permutations, and
from them bounds on trail probabilities (one trail, independent uniform round keys) and, for
AES, on the correlation of one linear trail. Every claim in these pages about AES or a
deployed permutation names the Lean theorem that proves it, or says that it was checked
outside Lean; [PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md) is the reference for
the concrete claims. Memory and disk figures are measurements, not theorems.
[INTRODUCTION.md](INTRODUCTION.md) is informal background, and its numbers are illustrations.

## Start here

| You are | Read, in order |
|---|---|
| A cryptographer | the README's [results](../README.md#results-at-a-glance) → [HOW_IT_WORKS.md](HOW_IT_WORKS.md) → [MECHANICS_HADES.md](../MECHANICS_HADES.md), [MECHANICS_DIFFERENTIAL.md](../MECHANICS_DIFFERENTIAL.md), [MECHANICS_LINEAR.md](../MECHANICS_LINEAR.md) → [PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md) |
| A zk engineer | the README's [Poseidon2 and Poseidon table](../README.md#deployed-poseidon2-and-poseidon-permutations) → your instance's section of [PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md) (its sources, parameters, certified claims and known-answer vectors) → [Boundary of the certificate](../PRODUCTION_CERTIFICATE.md#boundary-of-the-certificate) |
| An auditor | the README's [What is proved and what is not](../README.md#what-is-proved-and-what-is-not) → [BUILDING.md](BUILDING.md) (the commands CI runs) → [Boundary of the certificate](../PRODUCTION_CERTIFICATE.md#boundary-of-the-certificate) → the `Checks/` directories ([FILES.md](FILES.md)) → [Independent implementation checks](../PRODUCTION_CERTIFICATE.md#independent-implementation-checks) |
| A Lean user | the README's [Use it in your own Lean project](../README.md#use-it-in-your-own-lean-project) → [BUILDING.md](BUILDING.md#using-widetrail-as-a-dependency) → [FILES.md](FILES.md) → [LAYERS.md](LAYERS.md) |
| New to differential cryptanalysis | [INTRODUCTION.md](INTRODUCTION.md) → [GLOSSARY.md](GLOSSARY.md) → [HOW_IT_WORKS.md](HOW_IT_WORKS.md) |

## All documents

### Results and scope

- [PRODUCTION_CERTIFICATE.md](../PRODUCTION_CERTIFICATE.md): every concrete claim about AES
  and the deployed permutations, with its sources, parameters, known-answer vectors and
  boundary. Its sections:
  [AES S-box](../PRODUCTION_CERTIFICATE.md#aes-s-box),
  [AES linear trails and hull](../PRODUCTION_CERTIFICATE.md#aes-linear-trails-and-hull),
  [HADES connection](../PRODUCTION_CERTIFICATE.md#hades-connection),
  [Pinned BN254 instance](../PRODUCTION_CERTIFICATE.md#pinned-bn254-instance),
  [SP1 width-sixteen instances](../PRODUCTION_CERTIFICATE.md#sp1-width-sixteen-instances),
  [Pico and OpenVM width-sixteen instances](../PRODUCTION_CERTIFICATE.md#pico-and-openvm-width-sixteen-instances),
  [Aztec and Noir BN254 width-four instance](../PRODUCTION_CERTIFICATE.md#aztec-and-noir-bn254-width-four-instance),
  [Starknet's Poseidon (HADES) instance](../PRODUCTION_CERTIFICATE.md#starknets-poseidon-hades-instance),
  [Counting more partial rounds](../PRODUCTION_CERTIFICATE.md#counting-more-partial-rounds),
  [Linear activity of the HADES instances](../PRODUCTION_CERTIFICATE.md#linear-activity-of-the-hades-instances),
  [Boundary of the certificate](../PRODUCTION_CERTIFICATE.md#boundary-of-the-certificate),
  [Independent implementation checks](../PRODUCTION_CERTIFICATE.md#independent-implementation-checks).

### How the proofs work

- [HOW_IT_WORKS.md](HOW_IT_WORKS.md): the shape of a round, the AES proof chain and the
  Poseidon2 and Poseidon proof chain as diagrams, and why the approach is useful.
- [LAYERS.md](LAYERS.md): what each of the eight proof layers proves, with the numbers and
  the theorem names.
- [MECHANICS_PROPAGATION.md](../MECHANICS_PROPAGATION.md): why the activity bound is a counting
  argument on supports; branch numbers, Lemma 1 and Lemma 2, chaining blocks, and Definition 5
  in closed form.
- [MECHANICS_ALGEBRA.md](../MECHANICS_ALGEBRA.md): how `GF(2⁸)` is built, why MDS implies the
  branch number, and why the concrete matrix needed 64 cases.
- [MECHANICS_DIFFERENTIAL.md](../MECHANICS_DIFFERENTIAL.md): probability without division,
  the weight as an exponent, where the independent-key assumption lives, and the two-round
  differential bound.
- [MECHANICS_HADES.md](../MECHANICS_HADES.md): the outer-round argument, partial rounds, exact
  ratios and dimensions, the two-round differential, and counting more partial rounds with
  certificates.
- [MECHANICS_LINEAR.md](../MECHANICS_LINEAR.md): correlations without division, the pairing as
  part of each statement, masks moving forward, how the key enters a trail, the AES S-box
  spectrum, the hull, HADES rounds over prime fields, and what is and is not claimed.

### The code and the build

- [FILES.md](FILES.md): the Lean files, one by one, layer by layer.
- [BUILDING.md](BUILDING.md): requirements, the two libraries, checking one result, depending
  on WideTrail, CI, API documentation, releases and troubleshooting.
- [CONTRIBUTING.md](../CONTRIBUTING.md): the checks a change must pass and the rules every
  proof follows.
- [`scripts/AuditAxioms.lean`](../scripts/AuditAxioms.lean) and
  [`scripts/AuditAxiomsHeavy.lean`](../scripts/AuditAxiomsHeavy.lean): the axiom audits of
  the default and the heavy library.
- [`scripts/check_imports.py`](../scripts/check_imports.py): fails if a Lean file is not
  reachable from a library root.
- [`.github/workflows/ci.yml`](../.github/workflows/ci.yml): the correctness gate;
  [`docs.yml`](../.github/workflows/docs.yml): the API documentation;
  [`release.yml`](../.github/workflows/release.yml): releases, which Zenodo archives once its
  integration is enabled. [BUILDING.md](BUILDING.md#continuous-integration) describes each.

### Background

- [INTRODUCTION.md](INTRODUCTION.md): an informal introduction to differential cryptanalysis.
  Nothing in it is checked by Lean, and its numbers are illustrations.
- [GLOSSARY.md](GLOSSARY.md): the terms these documents use.
- [paper/README.md](../paper/README.md): the paper this library formalises, by reference; it is
  not redistributed. [paper/deviation/deviation.txt](../paper/deviation/deviation.txt): where
  the proof of Theorem 3 departs from the paper's.

### Plans and history

- [HADES_PLAN.md](../HADES_PLAN.md): the HADES milestone contract and the status of its
  follow-on work.
- [STANDARDS_AND_DESIGNS_PLAN.md](../STANDARDS_AND_DESIGNS_PLAN.md): the plan for
  Rijndael-256 and FIPS 197, SKINNY and GIFT, AES-in-circuit gadgets for zkTLS, a design kit
  for new hashes, and Keccak and Ascon trail bounds.
- [WideTrail/Algebra/MDS_HYPOTHESIS_BUILD.md](../WideTrail/Algebra/MDS_HYPOTHESIS_BUILD.md): the
  build log of the Algebra layer: what was tried, what failed, and why.
- [research/standards-and-designs/](../research/standards-and-designs/README.md): the SHA-256
  manifests of the research material behind the standards and designs plan.
