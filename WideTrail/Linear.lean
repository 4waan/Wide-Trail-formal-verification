/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Linear.Character
import WideTrail.Linear.Binary
import WideTrail.Linear.Masks
import WideTrail.Linear.Checks.Character
import WideTrail.Linear.Checks.Conventions
import WideTrail.Linear.Checks.Axioms

/-!
# Linear cryptanalysis: correlations, masks and adjoints

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
* `Checks.Character`: (W1), (W6) and (W9) recomputed by the kernel on a 3-bit map, with negative
  controls for injectivity (Parseval rows) and separation ((W6) under the zero pairing);
* `Checks.Conventions`: on `GF(2⁸)`, every bit-pairing adjoint of `x ↦ 0x02 · x` maps `0x01` to
  `0x80`. Under every trace-form pairing, multiplication by `0x02` is an adjoint of itself and
  the field transpose of the `MixColumns` matrix is an adjoint of it; under the separating trace
  form with mask `0xA0`, every adjoint of `x ↦ 0x02 · x` maps `0x01` to `0x02`;
* `Checks.Axioms`: pinned axiom footprints.

Every module here is cheap to elaborate (at most about 2.4 GB of memory).

## What is not claimed

This file only imports the modules above and proves nothing itself. No correlation bound for an
S-box, a trail, a hull or a cipher is proved in these modules. The claims, and the statements of
what is not claimed, are those of the individual modules.
-/

set_option autoImplicit false

namespace Linear

end Linear
