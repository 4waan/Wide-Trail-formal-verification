[WideTrail](../README.md) › [Documentation](README.md) › Building and checking

# Building and checking

How to build the two libraries, run the checks that CI runs, check one result, depend on
WideTrail from another Lean project, and what each GitHub workflow does. The short version is
the [Quick start](../README.md#quick-start) of the README.

## Requirements

You need [elan](https://github.com/leanprover/elan), the Lean toolchain manager, and git.
elan also installs Lake, Lean's build tool. To install elan:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

The toolchain is pinned in [`lean-toolchain`](../lean-toolchain) (Lean `v4.33.1`) and Mathlib in
[`lakefile.toml`](../lakefile.toml) (`v4.33.1`); elan and Lake fetch both.

The import check, `scripts/check_imports.py`, also needs Python 3.

Expect about 8 GB of disk, mostly Mathlib's prebuilt files: `.lake/packages` measured 7.6 GB.
CI's GitHub-hosted runner, with 16 GB of memory, builds both libraries.

## The default library

```bash
git clone https://github.com/4waan/Wide-Trail-formal-verification.git
cd Wide-Trail-formal-verification
lake exe cache get    # prebuilt Mathlib files, instead of compiling Mathlib
lake build            # the default library WideTrail
```

A successful `lake build` means every theorem in the default library has been checked by
Lean's kernel. Two further checks run in CI:

```bash
lake env lean scripts/AuditAxioms.lean   # only propext, Classical.choice, Quot.sound
python3 scripts/check_imports.py         # every module is reachable from a library root
```

## The heavy library

The default library leaves out three check modules that evaluate whole width-16 Poseidon2
permutations in the kernel. Each needs 7 to 12 GB of memory to elaborate, so they live in a
separate library, `WideTrailHeavy`. That library also holds `Linear/Field.lean`, the one module
that imports `Mathlib.Analysis` (about 3.4 GB, almost all of it that import). Lake builds independent modules in parallel, so build
them one at a time:

```bash
lake build WideTrail.Poseidon2.Checks.KoalaBear   # about 12 GB
lake build WideTrail.Poseidon2.Checks.BabyBear    # about 7 GB
lake build WideTrail.Poseidon2.Checks.Plonky3     # about 7 GB
lake build WideTrailHeavy
lake env lean scripts/AuditAxiomsHeavy.lean      # the audit with these checks included
```

No module of the default library measured above about 3.3 GB; the largest are
`Poseidon/StarknetCompressed.lean` and the Aztec automaton certificate
(`Poseidon2/Certificates/AztecBN254Automaton.lean`), at about 3.2 GB each. The docstring of
[`WideTrail/Poseidon.lean`](../WideTrail/Poseidon.lean) and the certificate's Starknet section
give a looser figure for the Poseidon layer, at most about 3.4 GB. These measurements predate
the Rijndael layer; its modules have no recorded measurement. Lake runs one Lean process per
core, so the peak of the default build grows with the number of cores.

## Checking one module or theorem

`lake build` followed by a module name builds that module and the modules it imports, and
nothing else:

```bash
lake build WideTrail.Poseidon.StarknetMiddle
```

`lake env lean <file>` runs Lean with the build directory of this project on its search path,
so a scratch file can import any module that has been built and ask about one theorem:

```bash
printf 'import WideTrail.Poseidon.StarknetMiddle\n#print axioms Poseidon.Starknet.activity_middle\n' > /tmp/Check.lean
lake env lean /tmp/Check.lean
```

It prints the axioms the theorem depends on. For every theorem of the library that list is
`[propext, Classical.choice, Quot.sound]` or a part of it. The audits below check this for
every declaration at once. Keep scratch files outside the repository, or delete them: they
must not be committed.

## Using WideTrail as a dependency

A project that depends on WideTrail must use the same toolchain,
`leanprover/lean4:v4.33.1`, in its `lean-toolchain`. In its `lakefile.toml`:

```toml
[[require]]
name = "WideTrail"
git = "https://github.com/4waan/Wide-Trail-formal-verification.git"
rev = "main"    # better: a commit hash, or a release tag once one is published
```

or, in `lakefile.lean`:

```lean
require WideTrail from git
  "https://github.com/4waan/Wide-Trail-formal-verification.git" @ "main"
```

The name must be `WideTrail`, the package name in this repository's `lakefile.toml`. Lake
fetches Mathlib `v4.33.1` with it; a project that also requires Mathlib must require the same
version. Then run `lake update WideTrail`, `lake exe cache get` for the prebuilt Mathlib
files, and `lake build`. WideTrail itself publishes no prebuilt files, so Lake compiles the
WideTrail modules that the project imports.

What to import:

- `import WideTrail` loads the whole default library.
- `import WideTrail.Hades` (or `Propagation`, `Algebra`, `Differential`, `Poseidon2`,
  `Poseidon`, `Linear`, `Rijndael`) loads one layer and the layers it builds on.
- `import WideTrail.Poseidon.StarknetMiddle` loads one module and its imports. This compiles
  the least. [FILES.md](FILES.md) says which module holds which result.
- `import WideTrailHeavy` adds the memory-heavy check modules and `Linear/Field.lean`. Build
  them one at a time first, as above.

No release tag exists yet, so the examples use `main`. Pin a commit hash for a reproducible
build.

The README has [an example that compiles](../README.md#use-it-in-your-own-lean-project).

## Continuous integration

[`.github/workflows/ci.yml`](../.github/workflows/ci.yml) is the correctness gate. It runs on
every push, on every pull request and on manual dispatch, and a new run on the same branch
cancels the one it supersedes. It does not touch GitHub Pages. Its steps, in order:

1. Install the toolchain and fetch the prebuilt Mathlib files (`leanprover/lean-action`, with
   `use-mathlib-cache: true` and no build).
2. `lake build`: the default library.
3. The memory-heavy check modules, one at a time, then the heavy library:
   `lake build WideTrail.Poseidon2.Checks.KoalaBear`,
   `lake build WideTrail.Poseidon2.Checks.BabyBear`,
   `lake build WideTrail.Poseidon2.Checks.Plonky3`, `lake build WideTrailHeavy`. Together they
   would exceed the runner's 16 GB.
4. The axiom audit of `leanprover/lean-action` over the namespaces of the default library,
   with `axiom-audit-allow: propext,Classical.choice,Quot.sound`. Any other axiom fails the
   run: `sorry` and `admit` (which appear as `sorryAx`), `native_decide` (which appears as
   `Lean.ofReduceBool`), and any axiom declared in the project or reached through an import.
5. `lake env lean scripts/AuditAxioms.lean`: every declaration of the default library, found
   by its defining module, so names in the root namespace are included.
6. `lake env lean scripts/AuditAxiomsHeavy.lean`: the same for `WideTrailHeavy`, which
   includes all of `WideTrail`.
7. `python3 scripts/check_imports.py`: every Lean file under `WideTrail/` is reachable from
   `WideTrail.lean` or `WideTrailHeavy.lean`. A file that nothing imports would be neither
   compiled nor audited.

A pull request is ready when all seven steps pass. [CONTRIBUTING.md](../CONTRIBUTING.md) has
the rules the proofs follow.

## API documentation

[`.github/workflows/docs.yml`](../.github/workflows/docs.yml) builds the API documentation of
the default library `WideTrail` with doc-gen4, on every push to `main` and on manual
dispatch. It builds in a separate package, `docbuild/`, that requires WideTrail and doc-gen4,
so doc-gen4 never becomes a dependency of the library. The memory-heavy modules of
`WideTrailHeavy` are not documented.

The workflow publishes the result to GitHub Pages when Pages is enabled for the repository.
On `main`, if Pages is not enabled, the run fails with the message "GitHub Pages is not
enabled" after the documentation is built. To publish: Settings, then Pages, then set Source
to GitHub Actions. Until then the API documentation has no public address, and the README
does not link to one.

## Releases

[`.github/workflows/release.yml`](../.github/workflows/release.yml) runs when a tag of the
form `vX.Y.Z` is pushed. It first checks that [`CITATION.cff`](../CITATION.cff) says
`version: X.Y.Z` and fails otherwise, then creates the GitHub release for the tag. When the
repository is enabled in Zenodo's GitHub integration, Zenodo archives every published
release and mints a DOI for it, reading `CITATION.cff` for the metadata. No release tag
exists yet, and no DOI has been minted.

[`.github/workflows/create-release.yml`](../.github/workflows/create-release.yml) runs when a
push to `main` or `master` changes `lean-toolchain`. It calls
`leanprover-community/lean-release-tag`, which tags the first commit that moves to each new Lean
version, and, with `do-release: true`, creates a GitHub release for that tag. It skips the push
that first creates the branch.

[`.github/workflows/update.yml`](../.github/workflows/update.yml) runs
`leanprover-community/mathlib-update-action` on manual dispatch (its schedule is commented
out). When a newer Mathlib is available it tries the update, opens a pull request if the
update builds, and opens an issue if it does not.

## Troubleshooting

- **Mathlib compiles from source.** Run `lake exe cache get` before `lake build`. It fetches
  prebuilt files for the Mathlib version in `lake-manifest.json`.
- **The build runs out of memory.** Build the heavy modules one at a time, as above; never
  `lake build WideTrailHeavy` first. The default library needs no more than about 3.3 to
  3.4 GB per measured module, but Lake runs one Lean process per core. On a machine with many cores and little
  memory, a smaller target, such as one layer at a time (`lake build WideTrail.Propagation`,
  then `lake build WideTrail.Algebra`, and so on), leaves Lake fewer modules to build at once.
- **Lean reports a different version.** elan reads [`lean-toolchain`](../lean-toolchain).
  Run the commands from the repository root, and give a project that depends on WideTrail the
  same `lean-toolchain`.
- **A scratch file cannot find a module.** `lake env lean` reads built files only. Build the
  module first, with `lake build` and the module name.

Next: [FILES.md](FILES.md) (Lean users), or
[Boundary of the certificate](../PRODUCTION_CERTIFICATE.md#boundary-of-the-certificate)
(auditors). To contribute: [CONTRIBUTING.md](../CONTRIBUTING.md).
