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
import WideTrail.Poseidon.Certificates.StarknetAutomaton
import WideTrail.Poseidon.StarknetMiddle
import WideTrail.Poseidon.Checks.Starknet
import WideTrail.Poseidon.Checks.StarknetMiddle
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
* `StarknetCompressed`: the compressed schedule computes the same permutation, also with the
  same additional key added to both schedules;
* `StarknetExecution`: a materialised runner, proved equal to the specification;
* `Certificates.StarknetAutomaton`: a forward-space automaton certificate for the `83` partial
  rounds and a witness trail through the `91` rounds, checked by `decide +kernel` on light
  imports;
* `StarknetMiddle`: every trail through the `83` partial rounds charges at least `41` S-boxes,
  so two distinct inputs incur at least `57` charged S-box applications, and the independent-key
  trail bounds with the exponent `14250`;
* `Checks.Starknet`: known-answer vectors, negative controls and exactness checks;
* `Checks.StarknetMiddle`: exactness checks for `41` and `57` in the `IsTrail` model and for the
  exponent `14250`, negative controls of the certificate, and the axiom footprints of the new
  theorems;
* `Checks.Axioms`: pinned axiom footprints.

Every module here is cheap to elaborate (at most about 3.4 GB of memory).

## What is not claimed

This file only imports the modules above and proves nothing itself. The claims, and the
statements of what is not claimed, are those of the individual modules.
-/

set_option autoImplicit false

namespace Poseidon

end Poseidon
