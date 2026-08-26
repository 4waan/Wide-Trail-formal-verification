# Mechanics of Layer 2

This explains *how* `WideTrail/Layer2/` actually works — the mechanism, not a tour of the
file names. For the story of how it was built (what failed, what worked, in what order), see
[`WideTrail/Layer2/MDS_HYPOTHESIS_BUILD.md`](WideTrail/Layer2/MDS_HYPOTHESIS_BUILD.md).

## 1. What a byte *is* in `GF256.lean`, mechanically

A `GF256` value is a `BitVec 8` wrapped in a one-field structure. Nothing exotic: it's
literally the 8 bits of a byte. The two operations are where the actual field structure lives.

**Addition is xor, full stop.** `a + b := a ^^^ b`. There's no carry, no borrow — bit `i` of
`a + b` depends only on bit `i` of `a` and bit `i` of `b`. This is why `a + a = 0` for every
`a`: xor-ing a bit with itself always clears it. Every element is its own additive inverse.

**Multiplication is "multiply the two bytes as degree-≤7 polynomials over GF(2), then take the
remainder mod `X⁸+X⁴+X³+X+1`."** Mechanically, this is done one bit of `b` at a time:

```
mulAux : Nat → BitVec 8 → BitVec 8 → BitVec 8 → BitVec 8
mulAux (n+1) a b acc = mulAux n (xtime a) (b >>> 1) (if b.getLsbD 0 then acc ^^^ a else acc)
```

At each of the 8 steps: look at `b`'s current lowest bit. If it's set, xor the current `a`
into the accumulator (this is "adding in one term of the product"). Then unconditionally
double `a` via `xtime`, and shift `b` right one bit to expose the next one. After 8 steps,
every bit of the original `b` has been consulted exactly once, each time against the
correctly-doubled power of `a` — this is long multiplication, bit by bit, from the low end.

`xtime a` is "multiply by `X`" mechanically: shift `a` left one bit (`a <<< 1`), and if that
shift pushed a `1` out past bit 7 — i.e. the *original* top bit of `a` was set — xor in
`0x1B` (`00011011`, the low 5 bits of the reduction polynomial `X⁸+X⁴+X³+X+1`, since the `X⁸`
term itself is exactly what just got shifted out and needs cancelling). That's the entire
mechanism of staying inside 8 bits while still representing "multiply by `X` in the polynomial
ring, then reduce."

**Why this needed 64/512 basis checks instead of a proof that "just computes":** associativity
and commutativity are properties of the *whole function*, not something that falls out of
unfolding 8 loop iterations symbolically — the loop structure doubles `a` and reads `b`'s
bits, which is asymmetric between the two arguments, so there's no way to induct on the
recursion directly and get `rawMul a b = rawMul b a` to fall out. What *does* fall out of the
recursion directly is that doubling and adding are both `GF(2)`-linear operations, so `rawMul`
is additive in each argument. Once you know that, `rawMul a b` for arbitrary `a, b` is
completely determined by `rawMul` on pairs of basis elements `2ⁱ, 2ʲ` (write `a` and `b` each
as an xor of at most 8 powers of two, distribute), so checking commutativity/associativity on
the 64/512 basis (pairs/triples) checks it everywhere. That's the entire content of
`bitDecomp` + `rawMul_pow2_comm`/`rawMul_pow2_assoc` + the final `simp`-driven expansion in
`rawMul_comm`/`rawMul_assoc`.

## 2. Why "MDS" implies the branch-number bound, mechanically

Say `M` is the `4×4` mixing matrix, `x` is a nonzero input column, `y = Mx` is the output
column. `weight` counts nonzero bytes. The claim: `weight x + weight y ≥ 5` always.

Suppose it weren't — suppose the total nonzero count were `≤ 4`. Let `s = weight x`,
`t = weight y`, so `s + t ≤ 4`. Here is the mechanism that forces a contradiction:

- The `t` positions where `y` is nonzero leave `4 - t` positions where `y` is *zero*. Since
  `s ≤ 4 - t` (that's just `s + t ≤ 4` rearranged), those `4 - t` zero-positions of `y` have
  room to contain a full copy of `x`'s `s` nonzero positions — pick any `s` of them, call this
  row-set `R`.
- Look at the equations `y_i = 0` for `i ∈ R` (true, because `R` was chosen inside `y`'s
  zero-set). Each one unpacks to `∑_j M_{ij} x_j = 0`. Since `x_j = 0` outside `x`'s own
  support `S`, this sum only has `s` nonzero terms: `∑_{j ∈ S} M_{ij} x_j = 0` for every
  `i ∈ R`.
- That's exactly `s` linear equations in the `s` unknowns `{x_j : j ∈ S}`, with coefficient
  matrix the `s×s` submatrix `M[R, S]` (rows `R`, columns `S`). **This is where "MDS" gets
  used**: `M[R, S]` is a square submatrix of `M`, and MDS says every square submatrix is
  nonsingular. A nonsingular `s×s` system with right-hand side `0` has only the zero
  solution — so `x_j = 0` for every `j ∈ S`.
- But `S` is *defined* as the set where `x` is nonzero. `x_j = 0` for every `j ∈ S` is only
  possible if `S` is empty, i.e. `x = 0` — contradicting that `x` was assumed nonzero (or, in
  the fully general statement, contradicting `S` being nonempty when `s ≥ 1`).

That whole argument is `isMDS_branch_bound` in `MDS.lean`. The Lean proof does exactly this:
picks `R` via `Finset.exists_subset_card_eq`, builds the submatrix via
`Finset.orderIsoOfFin`, gets "nonsingular ⟹ injective" from
`Matrix.mulVec_injective_of_det_ne_zero`, and "injective + maps to 0 ⟹ is 0" is injectivity
applied directly.

## 3. Why the concrete matrix needed 64 cases, not 4096 or 16.7 million — mechanically

The 69 minors of a `4×4` matrix (order 1 through 4) are, individually, cheap: a `3×3`
determinant is 6 products of 3 field elements, added and subtracted. The expense was never the
arithmetic. It was in *selecting* "which 3 of 4 rows, in which order" in a form the kernel
could actually evaluate.

Mechanically, `Matrix.det`'s literal definition sums over all permutations of the index type,
using Mathlib's general `Equiv.Perm` machinery — which represents "the permutations of `Fin
3`" via a sorted-list construction carrying nontrivial equality proofs. The kernel's reduction
engine walks a term step by step, unfolding definitions; a proof-carrying `Eq.recOn` inside
that construction is a shape it cannot step through no matter how much budget it's given. This
is *not* "too slow" — it is "stuck," the same way a definition built on `Classical.choice`
would be stuck, because both boil down to a piece of the term the reduction rules simply don't
know how to progress past.

The escape is to never ask the kernel to unfold `Matrix.det`'s general definition at all.
`Matrix.det_fin_three` is a *different* proof — already established, once, by whatever means —
that `det A` equals a specific six-term formula written directly in terms of `A`'s entries.
Rewriting with it *before* asking `decide` to evaluate anything means the kernel only ever has
to chew on `+`, `-`, `*` applied to concrete field elements — arithmetic it's fine with.

Selecting "which 3 rows" has the same shape of problem one level up: the natural tool
(`Finset.orderIsoOfFin`, "the order-preserving bijection between `Fin 3` and this 3-element
subset") is built from `List.Nodup.getEquivOfForallMemList`, which carries the same kind of
`Eq.recOn`-laden proof term that blocked `Matrix.det` — so it is *also* stuck, independent of
what it's being used to select. `Fin.succAbove m : Fin 3 → Fin 4` ("skip index `m`, keep
everything else in order") is a plain case-split on a comparison, no proof-carrying detour —
mechanically transparent, and it computes.

The last piece is why checking only 4 "omitted-row" values × 4 "omitted-column" values (16
cases) is enough, rather than needing to separately check every possible *order* the 3 chosen
rows could be listed in (`4096` = `24 × 24` orderings). Swapping two rows of a matrix flips the
sign of its determinant and nothing else — `Matrix.det_permute` is exactly this fact, stated
generally. So if the "in order" minor (via `succAbove`) is nonzero, every reordering of the
same 3 rows has determinant `±(\text{that value})`, still nonzero (a field's `-1 ≠ 0`). The
`factor3` lemma is the bridge: *any* injective `Fin 3 → Fin 4` — any 3 rows, in any order — is
mechanically nothing more than "skip index `m`" followed by "then permute the remaining 3
positions," so checking the 16 canonical (in-order) minors really does cover every case, and
the permutation part is decided over a 24-element space (`Fin 4 × Perm(Fin 3)`) rather than
enumerated by brute force at all.

## 4. From a matrix fact to a cipher fact

`aesMixColumns` doesn't do anything to a `4×4` state except apply the same `4×4` matrix to
each of the 4 columns independently — column `c`'s new value at row `r` is
`∑_{r'} M_{r,r'} · (\text{old value at } (r', c))`. `IsColBranchBound` asks a question about
*one column at a time* (its active-byte count before and after, summed), which is exactly what
`isMDS_branch_bound` answers for a single vector `x`. `localWeight_sqCol_eq_weight` is the one
bookkeeping step needed to notice this: "count active positions of the 2-D state that fall in
column `ξ`" and "count active positions of the 1-D vector that *is* column `ξ`" are counting
the same set, just described two different ways (one as a filtered 2-D `Finset`, one as a
plain 1-D `Finset`) — a bijection `(r, ξ) ↦ r`, nothing deeper. Once that's established, the
cipher-level theorem is a direct instantiation of the matrix-level one; no new mathematics
happens at this last step, only translation.
