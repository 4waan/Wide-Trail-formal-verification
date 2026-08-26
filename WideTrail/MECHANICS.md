## The move that makes the whole thing work: throw the values away

A difference pattern is a function `Idx → K`. The theorem never reads a single value of it. `activePattern` collapses it immediately:
```lean
def activePattern (s : Idx → K) : Finset Idx := Finset.univ.filter (fun i => s i ≠ 0)`
```
From that line onward the state is a Finset Idx, a set of positions. weight is its card. Everything downstream is set arithmetic on 16 positions, not algebra over GF(2⁸).

That collapse is legitimate because of what an S-box layer does to a pattern. Take one S-box position i. Feed it difference 0: both members of the pair are the same input, so both produce the same output, so the output difference is 0. Feed it a nonzero difference: the two inputs differ, the S-box is a bijection, so the two outputs differ, so the output difference is nonzero. The S-box does not know or care which nonzero difference. Position i is active before if and only if it is active after.

That is the entire content of `PreserveSupport`

```lean
def PreserveSupport (γ : (Idx → K) → (Idx → K)) : Prop :=
  ∀ a, activePattern (γ a) = activePattern a`
```

Key addition satisfies the same predicate, and for a sharper reason: `(a ⊕ k) ⊕ (a* ⊕ k) = a ⊕ a*`, so it does not change the pattern at all, let alone its support. That is why no round key appears anywhere in the four-round theorems. Not "abstracted away". They are literally absorbed into γ by preserveSupport_comp, and the theorem statement never mentions them.

So the causal chain is: values do not matter to the S-box layer, therefore only supports matter, therefore the state is a finite set, therefore the theorem is a counting argument.

## What a branch number is, once you stop calling it a minimum

Textbook version: `B(λ) = min_{a ≠ 0} { w(a) + w(λ a) }`.

That is a bad thing to write in Lean. min over ℕ needs the set to be nonempty or it returns junk, and no theorem downstream ever needs the exact minimum. Every theorem needs one direction: "you cannot get below B". So isBranchBound is a predicate, not a function:

```lean
def isBranchBound (col : Idx → Col) (psi : (Idx → K) → (Idx → K)) (B : Nat) : Prop :=
  ∀ a ≠ 0, B ≤ colWeight col a + colWeight col (psi a)
```
Read it as a budget. Activity is conserved in a weak sense: you can have few active positions going in, or few going out, but the two counts cannot both be small. Squeeze one and the other expands.

## The counting identity that everything rests on

A column partition is just a map col : Idx → Col. A column is a fiber of that map. localWeight counts active positions inside one fiber, and weight_eq_sum_localWeight is the whole reason columns are useful:

```lean
theorem weight_eq_sum_localWeight [Fintype Col] (col : Idx → Col) (s : Idx → K) :
    weight s = ∑ ξ : Col, localWeight col ξ s :=
  Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (col i))
```

Fibers are disjoint and cover everything, so the counts simply add. No double counting, no correction term. One line, and it is the hinge.

## Lemma 1 is a multiplication

MixColumns is a bricklayer: four independent 4-byte maps, one per column, no wires between columns. So the branch-number budget applies per column, and `IsColBranchBound` says exactly that:

```lean
def IsColBranchBound (col : Idx → Col) (θ : (Idx → K) → (Idx → K)) (B : Nat) : Prop :=
  ∀ (a : Idx → K) (ξ : Col),
    0 < localWeight col ξ a + localWeight col ξ (θ a) →
    B ≤ localWeight col ξ a + localWeight col ξ (θ a)
```
Now count. Suppose N columns are active. Each one owes B active bundles across the input and output of θ. Those debts sit in disjoint columns, so by the identity above they add rather than overlap:

```lean
weight a + weight (θ a) = ∑ over ALL columns of (local in + local out)
                        ≥ ∑ over the N active columns
                        ≥ N · B
```

That is `card_mul_le_weight_add`, and the three steps of the proof are literally `Finset.sum_le_sum`, Finset.`sum_le_sum_of_subset`, `Finset.sum_add_distrib`. **N columns in, N·B bundles out**. Lemma 1 is a converter from column count to bundle count, with exchange rate B.

### The hypothesis is symmetric

Notice `IsColBranchBound` triggers on `0 < local_in + local_out`, activity on either side. That is deliberate, and it is the thing that made Theorem 2 work.

Theorem 2 applies Lemma 1 twice. On round 1 it knows how many columns are active at the output (lemma_one_out). On round 3 it knows how many are active at the input (lemma_one_in). An asymmetric hypothesis gives you one of these and not the other, and the proof stalls halfway.

This looked like an invented convenience, so it is discharged in `isColBranchBound_of_columnLocal`: if θ is genuinely column-local, fixes 0, and has the one-sided branch property that Definition 3 actually states, the symmetric version follows. Mechanism: if a column is dead at the input, column-locality says the output there equals the output of the all-zero state, which is zero, so the column is dead at the output too. The symmetric-looking extra case is unreachable.

## Lemma 2 is the same multiplication running the other way

Lemma 1 converts columns into bundles. To multiply you need the reverse converter, and that is what ShiftRows is for.

ShiftRows moves no activity at all. weight is invariant under it. It cannot create or destroy a single active byte. What it changes is which column each active byte lands in, and that is the only thing it needs to change.

`DiffusionOptimal`:
```lean
def DiffusionOptimal (col : Idx → Col) (p : Equiv.Perm Idx) : Prop :=
  ∀ i j, i ≠ j → col i = col j → col (p i) ≠ col (p j)
```
Two distinct positions in the same column land in different columns. Now watch the mechanism in `card_filter_le_colWeight_image`. Take the active bundles of one column and apply the map i ↦ col (p i). Diffusion optimality says exactly that this map is injective on that set. An injection into the set of active columns of the image means:

(active bundles in one column)  ≤  (active columns after the shift)
Bundles in, columns out. That is the reverse converter, exchange rate 1.

lemma_two chains the two together. Pick any column ξ active after the first shift. The branch budget says that column carries ≥ B bundles across θ. Split that budget: the part before θ gets pushed back through the inverse shift into ≥ that many distinct columns of the earlier state; the part after θ gets pushed forward into ≥ that many distinct columns of the later state. Sum:
```lean
columns(a) + columns(d) ≥ localWeight ξ (b) + localWeight ξ (c) ≥ B
```