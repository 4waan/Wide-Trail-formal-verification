[WideTrail](../README.md) › [Documentation](README.md) › The basic idea, informally

# The basic idea, informally

*These notes are an informal introduction to differential cryptanalysis. They are not part
of the documentation of the proofs, and nothing in them is checked by Lean. Their numbers are
illustrations.*

Take two plaintexts P and P* that differ in a chosen way, and a cipher E.
Let `a' = P ⊕ P*` and `b' = E(P) ⊕ E(P*)`.
When E behaves like a random permutation on 128-bit blocks, then for a fixed a′ the output
difference b′ is spread roughly uniformly over 2^128 possibilities, so any particular b′ shows
up with probability about 2^-128.
The difference propagation probability of a map h (for n-bit vectors a and a′) is

`P_h(a′, b′) = 2^-n · ∑_a ∆(b′ ⊕ h(a ⊕ a′) ⊕ h(a))`

where ∆(x) = 0 for every x except ∆(0) = 1, and the sum runs over all 2^n inputs a. So the
formula shows directly how the probability is spread over the output differences.

## Why differences?

The round key enters by XOR: a and a* (where a* = a ⊕ a′) both get the key k XORed into them:
`(a ⊕ k) ⊕ (a* ⊕ k) = a ⊕ a*`, so the key cancels.
The difference passes through key addition unchanged, for every key.
The same happens at any linear layer λ, because linear means `λ(a) ⊕ λ(a*) = λ(a ⊕ a*)`: the
difference passes through and the key never enters.
So in a key-alternating cipher with three components per round, two of them handle
differences exactly and independently of the key.

**The only place where a difference behaves probabilistically at all is the S-box layer.**

## A differential attack, step by step

Two inputs:

```
P  = 01010101...
P* = 01011101...
```

They are almost the same; call the difference `a' = 00001000...`.
Encrypt both, E(P) and E(P*), and take the difference of the outputs.
Now think of a perfectly random cipher: knowing that the inputs differ by a′ tells you
nothing about how the outputs differ. The output difference could be any of the 2^128
possible 128-bit patterns, `Pr[a' -> b'] ≈ 2^-128`.

Now the weakness. Suppose you discover that when you give the cipher two inputs with
difference `a'`, the output difference is `b'` quite often, say `Pr[a' -> b'] ≈ 2^-30`.
That is 2^98 times more likely than it should be, and it gives a statistical handle on the
cipher's internal structure.

*How does this help find the key?*

In an AES-like cipher, P goes through, say, r rounds:

```
P -> round 1 -> ... -> round r -> ciphertext
```

The key of round r is the one we are trying to find, but you cannot see the difference
before the final round. Suppose the pair (a′, b′) above describes the first r − 1 rounds.
Then:

1. Collect about 2^40 plaintext pairs with difference `a'`.
2. Guess the final round key `k_r`.
3. Decrypt the last round of both ciphertexts under that guess, and XOR the two guessed
   round r − 1 values together.
4. Check whether the difference after round r − 1 matches the high-probability pattern.

If the key guess is wrong, the internal values are random garbage, and they match only at
random. The right guess makes the prediction come true about once every 2^30 pairs, so over
2^40 pairs it sees about 2^40 × 2^-30 ≈ 1000 matches:

```
Illustrative counts, 2^40 pairs

Key guess          Number of matches

Guess A                  0
Guess B                  1
Guess C                  0
Guess D                  2
Guess E                  947  <- the right guess
Guess F                  1
Guess G                  0
```

The correct k_r stands out in a counter array; then that round key is peeled off and the
process repeats inwards.

*Differential cryptanalysis is basically finding a weird cause-and-effect relation in how
differences propagate through a cipher.* The key detector is nothing but a statistical
bias.

## Inside an S-box

Think of a small lookup table like `S : {0, 1}^8 -> {0, 1}^8`. It is invertible and
nonlinear: in general `S(x ⊕ y) ≠ S(x) ⊕ S(y)`.

Take two inputs, x and x ⊕ a′, and pass both through the S-box:

```
x        ──> S(x)
x ⊕ a'   ──> S(x ⊕ a')
```

and look at the difference `S(x) ⊕ S(x ⊕ a')`. Suppose

```
a' = 00000001
x  = 00000000

S(x)      = something
S(x ⊕ a') = something else

output difference = S(x) ⊕ S(x ⊕ a')
```

Doing this for every x, for the input difference a′, gives a row of a DDT (difference
distribution table), something like:

```
Output difference       Number of times

00000000                     0
00110110                     2
10011001                     4  <- happens 4 times
01010111                     2
...
```

## From one S-box to the whole cipher

The largest entry in any row with a nonzero input difference is the S-box's differential
uniformity. For AES it is 4, so each active S-box multiplies a trail's probability by at most
4/256 = 2^-6. A trail through 25 active S-boxes therefore has probability at most 2^-150 (one
trail, independent uniform round keys). Counting active S-boxes is what the library proves:
every trail through four consecutive AES rounds has at least 25.

Next: [GLOSSARY.md](GLOSSARY.md), then [HOW_IT_WORKS.md](HOW_IT_WORKS.md).
