# Building Layer 2: discharging the MixColumns MDS hypothesis

This is the build log for `WideTrail/Layer2/`, in the order things actually happened. Layer 1
(`WideTrail/Layer1/`) proves `aes_four_round` and `aes128_ten_round` as an *implication*: given
`hmix : IsColBranchBound (sqCol 4) mix 5`, the bound follows. That hypothesis was left as a
named argument rather than proved, because proving it needs a concrete field and a minor
enumeration that were deliberately out of scope for the first pass. Layer 2 closes that gap:
it builds `GF(2⁸)` from scratch, proves the general "MDS matrix ⟹ optimal branch number"
theorem (which Mathlib has no vocabulary for at all), and instantiates both against the real
AES `MixColumns` matrix, turning the two headline theorems unconditional.

Nothing here was obvious on the first attempt. The rest of this document is what was tried,
what failed, why, and what actually worked — the general lessons (not tied to this specific
proof) are split out into the `lean4-decide-pitfalls` skill; this document is the specific
narrative of *this* proof.

## Starting constraints

Two decisions were fixed before writing any Lean, both explicit user calls rather than
defaults:

1. **No brute force over the definition itself.** `IsColBranchBound` quantifies over all
   `2^32` possible byte-patterns of a `4×4` state — checking it directly is exactly the
   brute force the whole project exists to avoid. The only tractable route is the classical
   equivalence: branch number `5` for a `4×4` matrix `M` holds iff every square submatrix of
   `M` is nonsingular (`16 + 36 + 16 + 1 = 69` determinants), which is finite and small enough
   to check directly.
2. **Pure kernel proof, no `native_decide`/`bv_decide` fallback.** This was a genuine fork
   with a real cost: `bv_decide` can discharge some of the GF(2⁸) field-axiom goals directly
   from the fully-unrolled recursive definition in seconds, but *which* goals stay inside the
   trusted kernel baseline versus silently pull in a fresh, proof-specific axiom (trusting a
   compiled SAT/LRAT check, same trust category as `native_decide`) is not predictable from
   the goal's size or shape — confirmed by testing the same-looking goal both ways and getting
   different axiom lists. Given this project's explicit goal is kernel-checked bounds, the
   slower, fully-structural route was chosen deliberately over the faster one. Every theorem
   in Layer 2 was checked with `#print axioms` at the end; all of them depend on nothing
   beyond the standard `propext, Classical.choice, Quot.sound` baseline.

## Part 1: `GF256.lean` — the field

Mathlib's `GaloisField p n` is a `SplittingField` inside a `noncomputable section`, so
`decide` can never reduce it — unusable as a computational vehicle for the minor enumeration.
`GF(2⁸)` had to be built by hand as `BitVec 8` under xor (addition) and a standard
shift-and-reduce carry-less multiplication (`xtime`, doubling by the primitive element `X`,
reducing by `0x1B` when the top bit overflows).

**The associativity/commutativity wall.** The natural first instinct — enumerate all triples
and `decide` — was tried and measured directly before being ruled out: even the *pairwise*
commutativity check (`256² = 65536` cases) was left running for 13 minutes and hit the
kernel's recursion-depth limit without finishing; associativity (`256³ ≈ 16.7` million) was
never going to be feasible at all. This wasn't assumed, it was timed.

The fix was structural rather than computational: `rawMul` was proved additive in each
argument separately (`rawMul_add_left`, `rawMul_add_right`) by induction on the recursion,
using that `xtime` itself is additive (`xtime_xor`) — no enumeration anywhere in that argument.
Additivity makes `rawMul` bilinear over `GF(2)`, and a bilinear map on an 8-dimensional space
is determined by its values on a basis. `bitDecomp` expresses every byte as the xor of the
(up to 8) basis powers of two selected by its own bits; commutativity and associativity then
only need checking on the `8×8 = 64` and `8×8×8 = 512` basis pairs/triples respectively —
`decide` finishes both in a few seconds. Getting the *lifting* step (from basis facts to the
general statement) to actually close required a run of numeral/normal-form debugging — `0`
vs `0#8`, `.getLsbD i` vs `[i]` — documented in the skill; the mathematical content is exactly
"a bilinear form agreeing on basis pairs agrees everywhere."

Multiplicative inverses use Fermat (`a^254 = a⁻¹` for nonzero `a`, since the `255` nonzero
bytes form a group of that order). The exponentiation itself went through two failed designs
before the working one: a naive linearly-recursive power function blew the elaborator's
`maxRecDepth` when `decide`d across all 256 test values (depth-254 unfolding, times 256), and
a well-founded-recursive version (halving the exponent each step) didn't reduce via `decide`
at all — the same disease as `GaloisField`'s `Acc.rec`-based definition. The fix was to stop
trying to make a *general* power function reduce, and instead write `rawInv` as a fixed,
finite, fully unrolled chain of 7 squarings plus 6 multiplications (`254 = 128+64+32+16+8+4+2`
in binary) — no recursion at all, so nothing for either the elaborator or the kernel to get
stuck on.

The `GF256` type is a one-field wrapper `structure` around `BitVec 8`, not a bare
`def GF256 := BitVec 8` — `BitVec 8` already carries its own unrelated `Add`/`Mul` (ordinary
mod-`2⁸` arithmetic), and a reducible alias risks instance resolution silently picking those
instead of the ones built here.

## Part 2: `MDS.lean` — the branch-number theorem Mathlib doesn't have

A direct search confirmed Mathlib has no linear-code vocabulary at all: no MDS matrices, no
minimum distance, no Singleton bound. `Mathlib/InformationTheory/Coding/` covers only
Kraft–McMillan and prefix-free source codes — unrelated. This had to be proved from the
definition of a determinant up.

`IsMDS M` says every square submatrix of `M` (any order `k`, any `k` rows and columns, chosen
via injective functions `Fin k → Fin n` so repeats are excluded) is nonsingular. The main
theorem, `isMDS_branch_bound`, is the classical fact that this makes `{(x, Mx) : x}` an
optimal `[2n, n, n+1]` code: any nonzero `(x, Mx)` has at least `n+1` nonzero coordinates
between the two halves. The proof needed no coding-theory framework, just one self-contained
linear-algebra argument: assume the combined weight is `≤ n`; then the complement of `Mx`'s
support has room for a full copy of `x`'s support, giving (via `Finset.exists_subset_card_eq`
and `Finset.orderIsoOfFin`) a square submatrix of `M` that simultaneously (a) sends `x`'s
support to zero, because `Mx` vanishes there by construction, and (b) is injective, because
it's a nonsingular submatrix (`Matrix.mulVec_injective_of_det_ne_zero`) — forcing `x`'s
support to be zero, which contradicts it being, by definition, the support.

`isMDS_injective` (an MDS matrix acts injectively on the whole space) turned out to be a
one-line corollary of `isMDS_branch_bound` itself, not a separate construction: if `Mx = 0`
for `x ≠ 0`, the branch bound demands `n+1 ≤ weight x + weight (Mx) = weight x ≤ n` —
contradiction. No need to separately handle the "full matrix" case with permutation
machinery here; that need only showed up later, in verifying the *concrete* matrix.

## Part 3: `AESMix.lean` — the concrete matrix, and where the real difficulty was

This is where most of the build time went, and where `Matrix.det` itself turned out to be the
obstacle, not the mathematics.

**`Matrix.det` does not reduce under `decide` for order ≥ 3, at all.** Not a scale problem — a
*single*, fully concrete `3×3` determinant over `GF256` failed with
`did not reduce to isTrue or isFalse ... reduction got stuck`, tracing into
`Equiv.Perm`'s Fintype instance and `List.Nodup.getEquivOfForallMemList`'s proof-carrying
internals. This is the same species of wall as `GaloisField`'s noncomputability — a heavy
combinator the kernel's `whnf` cannot see through, confirmed by testing the smallest possible
isolated case rather than assumed from a bigger failure. `Finset.orderIsoOfFin` (the natural
way to turn "these 3 of 4 indices" into a submatrix selector) hit the identical class of wall
independently, even for one concrete `Finset` literal like `{0,1,2}` — two unrelated pieces of
Mathlib, same disease.

The fix used two different tools for two different sizes:

- **`Matrix.det_fin_three`** (an explicit six-term formula, not a literal-syntax-dependent
  simp-proc) rewrites `M.det` to plain arithmetic generically, even under a `∀`-binder. Used
  for the 16 order-3 minors.
- **`eval_det`** (`Mathlib.Tactic.NormDet`, Bird's algorithm) — the one tool that can evaluate
  a genuinely concrete `4×4` determinant (no `det_fin_four` exists in this Mathlib version).
  It only fires on a literal `!![...]` matrix notation, so the `aesMatrix` definition had to
  be unfolded (`simp only [aesMatrix]`) before calling it.

**Even with `Matrix.det` fixed, the order-3 enumeration itself still didn't finish.** Checking
`∀ r c : Fin 3 → Fin 4, Injective r → Injective c → ...` directly is `4096` pairs, and that
enumeration alone (confirmed by swapping in trivial arithmetic and re-timing) stalls `decide`
regardless of how cheap each individual check is — the same enumeration cliff as Part 1, one
order of magnitude smaller. Restating the check over `Finset`-selected submatrices didn't
help either: that traded the enumeration-size problem for the `orderIsoOfFin`-reduction
problem above, so it looked like progress but hit the *other* wall.

The actual fix needed a genuine structural reduction, `factor3`: every injective
`r : Fin 3 → Fin 4` factors as `Fin.succAbove m ∘ σ` for some omitted index `m : Fin 4` and
permutation `σ : Equiv.Perm (Fin 3)` — decided over the `24`-element space `Fin 4 × Perm (Fin
3)`, not the `4096`-element space of all injective-function pairs. Combined with
`Matrix.det_permute`/`det_permute'` (determinant changes by a nonzero sign under row/column
permutation — `sign_cast_ne_zero` confirms the sign, cast into `GF256`, is never zero), this
transports nonsingularity from the `16` canonical minors to every injective `r, c` pair
without ever enumerating more than `16 + 24 + 24 = 64` total cases. The order-4 case ("the
whole matrix") uses the same permutation-invariance idea directly (`Equiv.ofBijective` +
`det_permute`/`det_permute'`), reducing to the single fact `det4_ne_zero`.

One dead end worth recording: extending an injective `Fin 3 → Fin 4` to a full permutation of
`Fin 4` and citing "the whole matrix is nonsingular, so the minor is too" — this conflates two
unrelated facts (a full matrix being nonsingular says nothing about an arbitrary proper minor
of it) and was abandoned once the confusion was spotted, in favor of the omit-one-index route
above.

`aesMatrix_isMDS'` (the raw-injective-function statement, where all this machinery lives) is
then transported to the `Finset`-indexed `IsMDS` used by `MDS.lean`'s abstract theorem
(`aesMatrix_isMDS`) by a one-line wrapper: instantiate at the canonical order-embeddings,
which are themselves injective functions, so the general theorem applies directly.

## Part 4: wiring it up

`aesMixColumns` applies `aesMatrix` to each column of the `4×4` state independently.
`localWeight_sqCol_eq_weight` is the combinatorial bridge connecting `IsColBranchBound`'s
2-D, column-filtered weight count to `isMDS_branch_bound`'s 1-D vector weight (a bijection
`i ↦ i.1` between "active positions in column `ξ`" and "active positions of the restricted
column vector", via `Finset.card_image_of_injective`). With that in hand,
`aesMixColumns_isColBranchBound` and `aesMixColumns_nondegenerate` are direct instantiations
of `isMDS_branch_bound` and `isMDS_injective`, and `aes_four_round_concrete` /
`aes128_ten_round_concrete` are Layer 1's theorems applied to them — no new proof content,
just plugging in what Layer 2 built.

## Final state

```
#print axioms aes_four_round_concrete
#print axioms aes128_ten_round_concrete
-- both: [propext, Classical.choice, Quot.sound]
```

The standard Mathlib baseline, nothing else — no `sorryAx`, no `native_decide`, no `bv_decide`
fallback axiom, anywhere in the dependency graph. `lake build` is clean (one linter false
positive on `isMDS_injective`, verified to be a false positive by checking the proof breaks if
the flagged hypothesis is actually removed, left in place; see the linter-false-positive row
in the `lean4-decide-pitfalls` skill).
