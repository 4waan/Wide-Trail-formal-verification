# WideTrail

*a parametric Lean 4 formalization of the wide trail propagation theorems, producing kernel-checked active-S-box bounds for AES-like designs*

Based on Daemen and Rijmen's [The Wide Trail Design Strategy](https://www.researchgate.net/publication/225704500_The_Wide_Trail_Design_Strategy).

---

## Two layers

The project is split into two layers, in two directories, because they're two different
kinds of work.

**Layer 1** (`WideTrail/Layer1/`) is the abstract propagation theory: an S-box layer, a
shuffle, and a mixing layer, related only by the structural properties a wide-trail cipher
needs (support-preservation, diffusion optimality, a branch number). It's parametric — the
branch number, state size, and field are all just parameters — so it proves a bound for an
entire *family* of cipher shapes at once, AES included. Instantiated at the AES shape, it
gives `aes_four_round`/`aes128_ten_round` as an **implication**: *given* that MixColumns has
branch number `5`, four rounds force `25` active S-boxes and the ten rounds of AES-128 force
`55`. The `hmix`/`hnd` hypotheses in `Layer1/AES.lean` are exactly that "given."

The state is rectangular, `Fin rows × Fin cols`, not square, so the whole Rijndael family is
in range: `Layer1/Rijndael.lean` covers the 192- and 256-bit block sizes as well, and uses
them to test what the theory actually decides about a real design choice.

**Layer 2** (`WideTrail/Layer2/`) discharges that hypothesis. It builds `GF(2⁸)` from scratch
(Mathlib's `GaloisField` is `noncomputable`, unusable for the enumeration this needs), proves
the general "MDS matrix ⟹ optimal branch number" theorem — vocabulary Mathlib doesn't have at
all — and instantiates both against the real `4×4` AES `MixColumns` matrix. The output is
`Layer2/AESMix.lean`'s `aes_four_round_concrete`/`aes128_ten_round_concrete`: the same two
bounds, now with *no* remaining hypothesis except the free fact that the S-box layer is a
bijective bricklayer (true for any invertible S-box, AES's included).

Every theorem in both layers is checked by `#print axioms` to depend on nothing beyond the
standard `propext, Classical.choice, Quot.sound` baseline — no `sorry`, no `native_decide`, no
`bv_decide` fallback axiom, anywhere. See
[`WideTrail/Layer2/MDS_HYPOTHESIS_BUILD.md`](WideTrail/Layer2/MDS_HYPOTHESIS_BUILD.md) for the
build log of Layer 2 (what was tried, what failed, why) and
[`MECHANICS_L2.md`](MECHANICS_L2.md) for how Layer 2 actually works, mechanically.

---

## What's in each file

The files import each other in this order, each one building on the last.

### [`WideTrail.lean`](WideTrail.lean)
The entry point. It just imports every file below, so the whole library is one `import WideTrail` away.

### Layer 1: the abstract theory

#### [`WideTrail/Layer1/Activity.lean`](WideTrail/Layer1/Activity.lean)
The foundation. Defines what it means for a position in the cipher's state to be "active" (its difference is nonzero), counts how many positions are active (the *weight*), and proves the basic two-round bound: across any two rounds, the number of active positions is at least the branch number of the mixing layer.

#### [`WideTrail/Layer1/Columns.lean`](WideTrail/Layer1/Columns.lean)
Groups the state into columns, the way AES groups bytes into 4-byte columns, and proves that if the mixing layer guarantees a minimum spread within each column, that spread adds up: any set of active columns forces that many times more active bytes overall (**Lemma 1**).

#### [`WideTrail/Layer1/Dispersion.lean`](WideTrail/Layer1/Dispersion.lean)
Models the shuffle step (like ShiftRows) that scrambles which column each byte belongs to between rounds. Proves that if this shuffle is "diffusion optimal", meaning no two bytes from the same column ever end up sharing a column again, then a column-level guarantee can be upgraded into a stronger bundle-level one (**Lemma 2**).

#### [`WideTrail/Layer1/FourRound.lean`](WideTrail/Layer1/FourRound.lean)
Combines Lemma 1 and Lemma 2 into the paper's two headline theorems: any four consecutive rounds of a wide-trail cipher force at least `B²` active S-boxes, where `B` is the branch number of the mixing layer. It's proved for both of the paper's cipher shapes, to show they agree.

#### [`WideTrail/Layer1/Cipher.lean`](WideTrail/Layer1/Cipher.lean)
Packages a whole cipher design (its column layout, S-box, shuffle, mixing layer, and the proof obligations they must satisfy) into a single structure, `WideTrailSpec`. Also extends the four-round theorem to any number of rounds by chaining four-round blocks together.

#### [`WideTrail/Layer1/Grid.lean`](WideTrail/Layer1/Grid.lean)
Instantiates the abstract theory on a rectangular `rows × cols` state with ShiftRows at an arbitrary offset vector. The whole file turns on one equivalence: the paper's geometric "diffusion optimal" condition on a permutation of `rows · cols` positions is *exactly* injectivity of the offset vector. That collapses a design criterion into something the kernel can decide for any concrete candidate, count in closed form, and refute. It also proves, for every possible shuffle and not just rotations, that a state with more rows than columns admits no diffusion-optimal shuffle at all.

#### [`WideTrail/Layer1/AES.lean`](WideTrail/Layer1/AES.lean)
Plugs the real AES shape into `WideTrailSpec`: the square case of the grid, ShiftRows as the shuffle, and a MixColumns with branch number 5 (a property of AES that's taken as a hypothesis here — `hmix`/`hnd` — rather than re-derived from finite-field arithmetic; Layer 2 is what discharges it). Out comes the actual numbers: at least 25 active S-boxes over any four rounds, 55 over the ten rounds of AES-128, 75 over the twelve of AES-192, and 80 over the fourteen of AES-256.

#### [`WideTrail/Layer1/Rijndael.lean`](WideTrail/Layer1/Rijndael.lean)
Rijndael at all three block sizes, and the place where the formalization is asked to rule on a real design decision. Rijndael shifts its rows by `0,1,2,3` at 128- and 192-bit blocks but by `0,1,3,4` at 256 bits. The kernel's verdict on the natural explanation is *no*: `0,1,2,3` is diffusion-optimal on the wide state too, along with 1678 other offset vectors, so the wide-trail criterion is not what rejected it. The criterion is not vacuous either — the 256-bit offsets are illegal on the AES state, and a 4×3 state admits no diffusion-optimal shuffle whatsoever.

#### [`WideTrail/Layer1/sanity-check/Verification.lean`](WideTrail/Layer1/sanity-check/Verification.lean)
A sanity-check file, not a source of new results. It builds a toy cipher to show the theorems' assumptions can all hold at once (so nothing here is vacuously true), and builds a second toy cipher that is missing only the "diffusion optimal" shuffle property to show the bound genuinely breaks without it.

#### [`WideTrail/Layer1/sanity-check/Tightness.lean`](WideTrail/Layer1/sanity-check/Tightness.lean)
Measures how much slack is in the bounds on the one cipher small enough to search exhaustively (`toySpec`, a `2×2` state over `GF(2)`): the two-round bound turns out exactly tight, the four-round bound looser.

#### [`WideTrail/Layer1/sanity-check/Axioms.lean`](WideTrail/Layer1/sanity-check/Axioms.lean)
Audits the axiom footprint of the toy-cipher checks: confirms every finite check in the project runs through kernel `decide`, never `native_decide`, so nothing here quietly moved trust out of the kernel.

### Layer 2: discharging MixColumns

#### [`WideTrail/Layer2/GF256.lean`](WideTrail/Layer2/GF256.lean)
`GF(2⁸)` built from scratch as `BitVec 8` under xor and shift-and-reduce multiplication, proved a genuine `Field` — commutativity and associativity by bilinear extension from a 64/512-case basis check (not brute force, which hits a kernel recursion-depth wall well before it could finish), inverses by an unrolled Fermat exponentiation.

#### [`WideTrail/Layer2/MDS.lean`](WideTrail/Layer2/MDS.lean)
The general theorem: if every square submatrix of a matrix `M` is nonsingular (the MDS property), then `{(x, Mx)}` has the optimal branch number `n+1` — vocabulary Mathlib has none of (no MDS matrices, no minimum distance, no Singleton bound anywhere in the library).

#### [`WideTrail/Layer2/AESMix.lean`](WideTrail/Layer2/AESMix.lean)
The real `4×4` AES `MixColumns` matrix over `GF256`, proved MDS (all 69 minors nonsingular), and wired through Layer 1's `aes_four_round`/`aes128_ten_round` to produce the fully unconditional `aes_four_round_concrete`/`aes128_ten_round_concrete` (25 and 55), plus the same for AES-192 and AES-256 (75 and 80).

---

## How this works as a program, and why it's useful

At its core, this project turns a cipher's design into a small set of numbers, and a machine-checked proof that those numbers can't be beaten.

### The shape of a round

Every round of a wide-trail cipher is the same three steps, one after another:

```mermaid
flowchart LR
    A["state a"] --> S["γ: S-box layer\n(scrambles bytes, keeps zero/nonzero pattern)"]
    S --> P["π: shuffle layer\n(moves bytes between columns)"]
    P --> M["θ: mixing layer\n(spreads activity within a column)"]
    M --> B["state a′ (next round's input)"]
```

Only the mixing layer `θ` can actually reduce how "spread out" a difference is; the S-box layer never merges positions together, and the shuffle only relocates them. That's the entire reason the argument works: count what `θ` guarantees, and you've counted what the whole round guarantees.

### From one round to a certified bound

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
    GFMDS["Layer 2: GF256.lean + MDS.lean\nbuild GF(2^8), prove MDS -> branch B"]
    AESMIX["Layer 2: AESMix.lean\nthe real MixColumns matrix is MDS"]
    CONCRETE["AESMix.lean\nunconditional: 25 per 4 rounds, 55 over AES-128"]

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
```

[`WideTrail/Layer1/sanity-check/`](WideTrail/Layer1/sanity-check/) sits off to the side of this chain: it doesn't add a new theorem, it stress-tests the ones above by trying to break them with small hand-built examples, measures how tight the bounds are, and audits that everything really is kernel-checked.

### Why this is useful

Normally, showing a cipher resists differential and linear cryptanalysis means hand-checking (or exhaustively searching) huge numbers of specific attack patterns, one cipher at a time. This project instead proves a bound that holds for an entire *family* of cipher designs at once, AES included, as long as the design follows the wide-trail shape: an S-box layer, a well-mixing layer, and a shuffle that spreads columns well.

Two things make that bound trustworthy:

- **It's kernel-checked.** Lean's kernel is a small, independently trusted piece of software. If the project compiles, every theorem in it is guaranteed correct by that kernel, not by a human re-reading the proof or a test suite that might miss a case.
- **It's parametric.** The branch number, the state size, and the mixing layer are all just parameters. Swap in a different design with the same shape, and the same machinery hands you a new certified bound for free, instead of redoing the argument by hand.

The payoff of the bound itself: each active S-box cuts down an attacker's odds of guessing right, so a guaranteed minimum count of active S-boxes over every four rounds puts a hard ceiling on how good a differential or linear attack can ever get against the full cipher, no matter how many rounds are chained together.

---

## The basic principles, dumbed down

Take two plaintexts P and P' (differing in a chosen way) and cipher E_k
let `a'= P ⊕ P' && b' = E(P) ⊕ E(P')`
when E behaves like a random permutation on 128bit blocks for fixed a'
b' would be spread ≈uniformally over 2^128 possibilities and that means any b showing up has 2^-128 probaility
We define the difference propagation probability (for n-bit vectors a and (a'-a))as:
`P_h(a', b') = (2^-n)∑∆(b' + h(a + a') + h(a))`
∆(x)=0 forall x except ∆(0) = 1 so you can see direct implication of the spread of probability over bits.

so when i say dumbed down i ll also explain another thing here: 
### why differences specifically?

Round key enters by XOR, a and a* (a'-a) both get key 'k' XORed into them:
`(a⊕ k) ⊕ (a* ⊕ k) = a ⊕ a*` --> the key cancels
difference passes through key addition completely unchanged for every key. 
The same happens at any linear layer λ because linear means `λ(a) ⊕ λ(a*) = λ(a ⊕ a*)`.. the difference passes and key never enters
So in a key alternating cipher where there are 3 components in a round, 2 of them handle differences in a way that is exact and key independent

**The only place a difference behaves probabilistically at all is the S box layer** 

### the attack and the design

we can see the shape of the attack minimalised as: 

suppose you find a pair (a', b') where prob is 2^-30, which is 2^98 times more likely than it should be, the lever we have here is:
1. collect ~2^30 plaintext pairs with difference `a'`
2. Guess the final round key `k_r`
3. Decrypt the last round of both ciphertexts under that guess. 
4. Check whether the difference at round r-1 matches what the above high probability pattern says

so *attack* basically is among randomly showing up (scrambling guesses) predictions the right guess makes it show up at 2^30 and the correct k_r stands out from a counter array, and we peel off the last round key and repeat inwards.
Taking this further down the explain easy road because neither a beginner (or chatgpt) can wrap itself around the fundamentals:

two inputs:
`P  = 01010101...`
`P* = 01011101...`
almost same, and call the difference `a' = 00001000...`
encrypt both: E(P) and E(P*) and diff these outputs
Now think a perfectly random cipher:
knowing that inputs differ by a' will help with learning nothing about how outputs differ, it could be any of 2^128 possible 128 bit patterns `Pr[a' -> b'] ~2^-128`

But the weakness here:
Suppose by a chance you discover that when giving the cipher two inputs with diff `a'` the output differences are `b'` quiet often
like imagine `Pr[a'-> b'] ~2^-30`
That gives a statistical wrap of the cipher's internal structure!

*How will this help find the key?*

in an AES lik encryption, the P goes through suppose r rounds
P-> round1 ->.... round r-> ciphertext
here round r is the key we re trying to find
but you cant see the diff before the final round

1. decrypt final round using the guessed key with ciphertext pair
2. Xor together with guessed round r-1 values

does the difference look like as predicted?
so if the key guess is wrong its garbade random internal values...

Key guess          Number of matches

Guess A                  0
Guess B                  1
Guess C                  0
Guess D                  2
Guess E                  947  ← whoaa
Guess F                  1
Guess G                  0

*differential cryptanalysis is basically finding a weird cause-effect*
*relation in how differences are propagating in a cipher.* 

the key detector is nothing but a statistical bias.

### Inside S-box

think of a small lookup table like `S : {0, 1}^8 -> {0, 1}^8`. its invertible, non linear meaning it doesnt commute with XOR..

take two inputs (x and a') and pass through the S-box
x          ──> S(x)
x ⊕ a'     ──> S(x ⊕ a')
see the diff `S(x) ⊕ S(x ⊕ a')`

suppose
a' = 00000001
x  = 00000000

S(x)       = something
S(x ⊕ a') = something else

output difference = S(x) ⊕ S(x ⊕ a')

at the end we might get something like:
Input difference = a'

a DDT (difference ditribution table):

Output difference       Number of times

00000000                     0
00110110                     2
10011001                     4  <- happens 4 times
01010111                     2
...
..
