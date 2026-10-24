# Unexpanded-node observer source review

Reviewed at 2026-10-24 02:17 CEST. Status: SOURCE CLEAR. No concrete type, proof, projection, or scope error was found. The reviewer ran no compiler and made no repository change.

The complete 78-line candidate `/tmp/mcfta-observer-frame-20261024-node.lean.txt` was read. SHA256: `e1b3bad8507467a7928940ac59412275599c3ae3321313f5839c5278c95fb47e`. Its imported installed `EnumerationObservations.lean` is byte-identical to the previously reviewed primitive candidate, SHA256 `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab`.

The modeled projection matches the branch structure of Haskell `getUnexpandedNode` at `cfta/src/Data/CFTA/Enumeration.hs:1412–1417`: read the current representative's value, return the optional node from `UVarUnenumerated`, and return `Nothing` for both other tags. A pending value with no node also returns none. A pending stored empty node remains a present node; the observer does not test its language or contents. The candidate does not enumerate, prune, call an oracle, or change any payload.

The Haskell value and representative readers at lines 415–428 were read. `getUVarRepresentative` runs the actual union-find lookup and stores its returned forest. `getUVarValue` then reads that representative's slot. The candidate uses the existing modeled `getValue` operation rather than a raw-slot read or a pure lookup at the original variable. The Haskell `UVarValue` constructors and fields at lines 184–199 were also read.

`getUnexpandedNode_success` is an exact successful-branch inversion. It exposes a successful value read with the same final state and the literal node projection. The pure continuation cannot change the state. Both directions use the actual `success_bind` and `success_pure` equality directions correctly.

`getUnexpandedNode_agrees` permits independent fuels and related input states. It requires only the input frame, left totality, and the two actual observations. The underlying paired value read derives equal complete values and the full final frame. Rewriting the two literal projections gives equality of the optional nodes. No desired node or payload-coherence assumption is present.

`getUnexpandedNode_transport` is not conditional on an assumed right observation. It takes one successful left observation, transports its actual value read to an independently constructed finite right read, and applies the same projection. The full final frame comes from value transport. Readability is supplied by the actual left observation; totality alone is not used as a substitute for an existing slot.

`getUnexpandedNode_moreFuel` is `Retains` for successful branches. It keeps the exact result and exact final state at larger fuel. It uses the existing `getValue_moreFuel` and reconstructs the same pure projection. It does not assert equal-fuel behavior in different forests or equality of error branches.

The frame remains the complete installed compression frame: counter, values, obligations, both ancestry fields, and every root/size-path equivalence. It does not assert equality of raw forests. These results concern the modeled primitive observer. They do not prove congruence of arbitrary callbacks, an ordered/shared-driver theorem, or a complete Haskell-to-Lean representation correspondence. In particular, Haskell uses native `Node symbol` payloads and a partial `IntMap.!` slot access; the model uses node IDs and an explicit missing-slot failure. This review confirms the projection and successful-read route, not an equivalence of all native errors or representations.

Exact live API uses were checked: `success_bind`, `success_pure`, `getValue_agrees`, `getValue_transport`, `EnumerationExecution.Retains`, and `getValue_moreFuel`. Relevant source identities:

- `cfta/src/Data/CFTA/Enumeration.hs`: `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`.
- `EnumerationCorrectness.lean`: `087b96d593bb42cea0b61b2742b43d4a41ce5a2d990e300c8d15700e2eb0672d`.
- `EnumerationExecution.lean`: `b81e03600e03085ec32fc8c85026ca4af562593764b28d6f8dd776eb3ac98346`.
- `EnumerationState.lean`: `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4`.

Arity authored the node candidate; Root read the whole source and installed the exact checked bytes. The reviewer authored only the prior primitive route proposal and review reports. No native correspondence or arbitrary-callback claim is made by this clearance.
