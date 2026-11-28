# Contributing to WideTrail

Contributions are welcome: new certificates for deployed permutations, new checks, fixes, and
documentation. This page gives the checks every change must pass and the rules the proofs
follow. Today these rules are otherwise spread over the comments of
[`ci.yml`](.github/workflows/ci.yml), [`lakefile.toml`](lakefile.toml) and
[`WideTrailHeavy.lean`](WideTrailHeavy.lean).

## Scope

The library proves bounds on differential and linear trails, and certifies deployed
permutations against pinned sources. Good contributions:

- a certificate for another deployed Poseidon2 or Poseidon permutation (see
  [Adding a deployed instance](#adding-a-deployed-instance));
- a larger count for the partial rounds of an instance already covered;
- checks that show a hypothesis cannot be dropped, or that a bound is attained;
- corrections to the documentation.

New designs and standards are planned in
[STANDARDS_AND_DESIGNS_PLAN.md](STANDARDS_AND_DESIGNS_PLAN.md). Please open an issue before
starting a new instance or a new layer, so that the scope and the sources can be agreed first.

## Build

[docs/BUILDING.md](docs/BUILDING.md) has the full instructions. In short:

```bash
lake exe cache get                         # prebuilt Mathlib files
lake build                                 # the default library WideTrail
lake env lean scripts/AuditAxioms.lean     # only propext, Classical.choice, Quot.sound
python3 scripts/check_imports.py           # every module is reachable from a library root
```

## The checks a change must pass

CI runs these commands, in this order, on every push and pull request
([`ci.yml`](.github/workflows/ci.yml)). All of them must pass:

```bash
lake build
lake build WideTrail.Poseidon2.Checks.KoalaBear
lake build WideTrail.Poseidon2.Checks.BabyBear
lake build WideTrail.Poseidon2.Checks.Plonky3
lake build WideTrailHeavy
lake env lean scripts/AuditAxioms.lean
lake env lean scripts/AuditAxiomsHeavy.lean
python3 scripts/check_imports.py
```

Between the builds and the audit scripts, CI also runs the axiom audit of
`leanprover/lean-action` with the allow list `propext,Classical.choice,Quot.sound`. The heavy
modules need 7 to 12 GB of memory each, so build them one at a time, in the order above. If
your machine cannot build them, say so in the pull request; CI builds them.

## Proof rules

- No `sorry` and no `admit`. They appear as the axiom `sorryAx`, and the audits fail.
- No `native_decide`. It appears as the axiom `Lean.ofReduceBool` and moves the evidence out
  of the kernel. No `bv_decide` fallback axiom either.
- No new `axiom`. Every declaration may depend on `propext`, `Classical.choice` and
  `Quot.sound` only.
- Finite checks run in the kernel, by `decide` or `decide +kernel`.
- Pin the `#print axioms` footprint of every named result in the `Checks/` axioms file of its
  layer (for example [`WideTrail/Poseidon/Checks/Axioms.lean`](WideTrail/Poseidon/Checks/Axioms.lean)),
  with `#guard_msgs`.
- A premise of a generic theorem is not a discharged property of an instance. Discharge it
  for the instance, or state the premise in the result.
- State lower bounds as lower bounds. Do not claim that a count is attained unless a check
  exhibits a trail or an input pair that attains it.
- Probability statements concern one trail, or a differential, with an additional independent
  uniform key per round. Say so in the docstring.

## Modules and imports

Every module must be reachable from [`WideTrail.lean`](WideTrail.lean) or
[`WideTrailHeavy.lean`](WideTrailHeavy.lean), normally through its layer file
`WideTrail/<Layer>.lean`; `scripts/check_imports.py` fails otherwise. A new layer is imported
by `WideTrail.lean`. Each layer keeps its examples, exactness checks, negative
controls and axiom pins in its own `Checks/` directory.

## Memory

The default library must build on a laptop.

- A module of the default library should need no more memory to elaborate than the recorded
  peaks of the existing modules, about 3.3 to 3.4 GB.
- A heavier module goes to `WideTrailHeavy`, and gets its own line in the one-at-a-time step
  of `ci.yml`.
- The default library does not import `Mathlib.Analysis`. `Linear/Field.lean`, the one module
  that needs it, is in `WideTrailHeavy`.

Measure the peak memory of a new module, for example with GNU `time -v` around
`lake env lean <file>`, and record it in the docstring of its layer file or module, as most
existing layer files do. The Rijndael layer has no recorded measurement yet.

## Adding a deployed instance

1. Pin the source: a tag and its commit, and the SHA-256 of each file read, or of each
   `.crate` archive.
2. Copy every constant literally, in the source's layout.
3. Prove each round equal to the code's round, or define the model directly from the pinned
   parameters, as for the HorizenLabs BN254 instance.
4. Add a materialised runner that follows the code's loop, and prove it equal to the
   specification for every input.
5. Prove the upstream known-answer vectors with the deployed constants, by `decide` on the
   runner. Add negative controls: changed models that fail the vectors.
6. Show that each sharp exponent plus one fails.
7. Give `_general` forms, for every round-constant table, of the activity, trail and
   differential statements.
8. Document the instance in [PRODUCTION_CERTIFICATE.md](PRODUCTION_CERTIFICATE.md), with the
   subsections Sources, Parameters, Certified claims and Execution checks. Add a row to the
   [Poseidon2 and Poseidon table](README.md#deployed-poseidon2-and-poseidon-permutations) of the
   README, and add the files to [docs/FILES.md](docs/FILES.md).

## Writing documentation

- Plain, precise English, in short sentences.
- Numbers and theorem names exactly as in the Lean files.
- Lower bounds stay lower bounds: write "at least".
- Every probability statement says what it concerns: one trail, independent uniform round
  keys.
- No superlatives.
- Say what is checked outside Lean, and what is not proved.
- Keep a relative link working when you move or rename a section.
- The README badges for Lean and Mathlib are static. Update them when `lean-toolchain` or the
  Mathlib version in `lakefile.toml` changes.

## Commits

Use the prefixes of the history: `feat(<layer>):`, `fix(<layer>):`, `test(<layer>):`,
`refactor(<layer>):`, `docs:` or `docs(<layer>):`, `build:`, `ci:` or `ci(<area>):`, `chore:`. For example `feat(hades): add the MiddleBound
interface for the partial rounds`. Do not commit scratch files or `.lake/`.

## License

WideTrail is under the Apache License 2.0. Contributions are accepted under the same license
([LICENSE](LICENSE), section 5). New Lean files must start with this license header, with
your name in the copyright and `Authors` lines:

```lean
/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
```
