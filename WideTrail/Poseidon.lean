/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import WideTrail.Poseidon.StarkPrimality
import WideTrail.Poseidon.StarknetConstants
import WideTrail.Poseidon.Starknet
import WideTrail.Poseidon.ConstantFolding
import WideTrail.Poseidon.StarknetCompressed
import WideTrail.Poseidon.StarknetExecution
import WideTrail.Poseidon.Checks.Starknet
import WideTrail.Poseidon.Checks.Axioms

/-!
# Pinned certificates for the original Poseidon (HADES) permutation

The Poseidon v1 family, as opposed to `WideTrail.Poseidon2`. It contains one instance,
Starknet's Poseidon permutation over the STARK field, width `3`, S-box `x^3`, `4 + 83 + 4`
rounds:

* `StarkPrimality`: the STARK prime and its Lucas certificate;
* `StarknetConstants`: the `91 × 3` round constants and the `107` compressed constants;
* `Starknet`: the S-box, the linear layer, the permutation, and its activity, trail and
  differential bounds;
* `ConstantFolding`: a generic lemma that pushes round constants off the S-box coordinates
  through the linear layers;
* `StarknetCompressed`: the compressed schedule computes the same permutation;
* `StarknetExecution`: a materialised runner, proved equal to the specification;
* `Checks.Starknet`: known-answer vectors, negative controls and exactness checks;
* `Checks.Axioms`: pinned axiom footprints.

Every module here is cheap to elaborate (at most about 3.3 GB of memory).
-/

set_option autoImplicit false

namespace Poseidon

end Poseidon
