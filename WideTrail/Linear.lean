/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Character
import WideTrail.Linear.Binary
import WideTrail.Linear.Masks
import WideTrail.Linear.Trail
import WideTrail.Linear.Hull
import WideTrail.Linear.Checks.Character
import WideTrail.Linear.Checks.Conventions
import WideTrail.Linear.Checks.Axioms
import WideTrail.Linear.Checks.ToyOne
import WideTrail.Linear.Checks.Toy
import WideTrail.Linear.Checks.ToyNat
import WideTrail.Linear.Checks.ToySpec
import WideTrail.Linear.Checks.TrailAxioms

/-!
# Linear cryptanalysis: correlations, masks, trails and hulls

The correlation side of the wide-trail strategy, built from exact character sums:

* `Character`: pairings of masks with states, additive characters, the Walsh value
  `walsh ψ P Q F u v = ∑ₓ ψ (⟨v, F x⟩ - ⟨u, x⟩)`, adjoints, and the identities (W1)-(W10): keys
  and constants contribute phases, linear layers move masks through adjoints, bricklayer maps
  factor over bundles, orthogonality, multiplication of correlation matrices, the Walsh values of
  a map with an adjoint, zero masks, Parseval, and the scaling symmetry of inversion. The
  identities that need a separating pairing and a domain are marked as such;
* `Binary`: the sign character of `ZMod 2`, the bit pairing of `Idx → ZMod 2`, integer Parseval,
  linearity bounds and the bound on a bricklayer's Walsh values by its active bundles;
* `Masks`: the adjoint calculus, adjoints of bundle transpositions and of matrices under a
  trace-form pairing, branch numbers of a bijection and its inverse, the linear branch number of
  a map as the differential branch number of its adjoint (for a separating pairing), and the
  forward/backward readings of a mask trail. Masks are propagated forward through the inverse of
  an adjoint;
* `Trail`: the correlation `trailCorr` and the key phase `trailPhase` of a linear trail through
  the keyed rounds of `Scheduled.run`; the fixed-key expansion of the cipher's Walsh value as a
  signed sum over trails, for every key vector; the bridge from a nonzero trail correlation to
  `WideTrailSpec.IsTrail`; and, in the binary case, the bounds `|trailCorr| · 2 ^ (d · A) ≤
  |X| ^ r` and `|trailCorr| · |K| ^ A ≤ c ^ A · |X| ^ r` for the activity lower bound `A` of a
  wide-trail specification;
* `Hull`: the key-averaged squared correlation `elpCount` in the independent-key model; key
  averaging, Markov composition (including a second block of zero rounds), Nyberg's identity,
  row and column sums, and the two-round bound `(c / |K|) ^ (2 (B - 1))` for a backward map of
  branch number at least `B`, with its extension to a whole schedule;
* `Checks.Character`: (W1), (W6) and (W9) recomputed by the kernel on a 3-bit map, with negative
  controls for injectivity (Parseval rows) and separation ((W6) under the zero pairing);
* `Checks.Conventions`: on `GF(2⁸)`, every bit-pairing adjoint of `x ↦ 0x02 · x` maps `0x01` to
  `0x80`. Under every trace-form pairing, multiplication by `0x02` is an adjoint of itself and
  the field transpose of the `MixColumns` matrix is an adjoint of it; under the separating trace
  form with mask `0xA0`, every adjoint of `x ↦ 0x02 · x` maps `0x01` to `0x02`;
* `Checks.Axioms`: pinned axiom footprints;
* `Checks.ToyOne`: on a one-bundle 3-bit toy, the fixed-key expansion and Nyberg's identity
  instantiated and compared with the kernel's direct evaluation (the count `512` over `64` key
  pairs), and Nyberg's identity failing under a non-separating pairing;
* `Checks.Toy`: on a two-bundle toy with sixty-four states, the two-round hull bound and the trail
  bound instantiated and attained; the bound failing without bijective S-boxes or with a larger
  branch number; a fixed key whose squared correlation is four times the key-averaged bound;
* `Checks.ToyNat`: the toy's hull bound at all `63 · 64` mask pairs, recomputed on natural
  numbers as a numerical cross-check;
* `Checks.ToySpec`: the two-bundle toy as a wide-trail specification (columns of one bundle,
  branch number `1`), with the bridge, the specification-level trail bounds and the schedule hull
  bound instantiated; the bridge failing without bijective S-boxes, as a typed statement about
  `IsTrail`; the two-round bound failing at the zero masks and with a smaller linearity bound;
  and the fixed-key expansion failing under a non-separating pairing;
* `Checks.TrailAxioms`: pinned axiom footprints for the trail and hull results.

Every module here stays under about 3.1 GB of memory.

## What is not claimed

This file only imports the modules above and proves nothing itself. Apart from the 3-bit maps of
the checks (`chi3` and `andNext`, each with linearity bound `4`), no S-box is shown to have a
linearity bound, and no bound for a concrete cipher is proved in these modules: the trail and hull
bounds take the S-box bound and the branch number as hypotheses and are instantiated only on toy
ciphers. The wide-trail specification of the toy (`Checks.ToySpec`) has columns of one bundle and
branch number `1`, so its instances of the specification-level trail bounds show only that their
hypotheses can be met together; the first instance with a meaningful activity bound is planned
for AES. A trail bound bounds one summand of the fixed-key correlation; it is not a bound on the
cipher's correlation for a fixed key. The hull bounds are averages over an additional independent
uniform key per round. The claims, and the statements of what is not claimed, are those of the
individual modules.
-/

set_option autoImplicit false

namespace Linear

end Linear
