# Independent final recursive-domain compiler review

Date: 2026-10-17 00:58 CEST. Final source: `SourceCurrentAllocatedRecursiveDomainCode.lean`, 458 lines, SHA256 `a87444fcab499c4c549a6c280d992797f82880ff100204e37b444f7862cea6c6`.

No material defect was found. This review and its imported probes use the final source and canonical olean. The earlier 454911a8 header is preserved at `recursive-prefix-code-pre-linter.source.lean`. That historical snapshot is not endorsed as the live final API. The final `body_certified` needs edge-key equality but has no unused Symbol equality parameter.

## Source scope and inventory

`Closed:24` requires the reserved empty key and closure under literal domain extension for all source-available operand pairs with actual identity equations. This is a sufficient overapproximation. It is not limited to selected Mu branches or actual reachable requests. `source_closed:37` derives that condition for the explicit initial SourceInventory; no future domain list is supplied.

`Certified:47` consistently keeps `NodeScope source` and `EdgeScope source` in one fixed source HEAP. The current `Machine` has its own heap and domain cache. The certificate does not incorrectly require that the current domain cache be the initial source cache. A node/edge instruction retains the request's inventory key and its original operands. Result availability belongs to the current returned heap, not the source heap.

## Literal compiler branches

`mu_certified:265` computes the actual enter operation in the current domain cache. It derives physical validity and extension using `Kernel.entered`. It obtains the exact returned key from `Schedule.entered_key`. That key transfers the original body scope through `NodeScope.mu`. Inventory membership comes from `Closed.extend` applied to the original source-available operands. The optional-binder continuation only consumes a physical available returned value. It assumes no smaller-body termination or semantic result equation.

`reference_certified:289` follows the literal domain-name test and actual later `SourcePreparedSharedRows.read state.heap name`. `OriginalBindings.read` uses current heap Facts, source growth, and issued history to recover the same original source Mu. Both left/right reference directions keep the correct operand order. Missing-name branches remain certified failures; they are not presented as successful completion.

`node_certified:310` covers all actual selector cases: empty, reset, self, swap, repeated pair, the three Mu cases, both unions, both references, ordinary rows, and unsupported input. Reset uses `Closed.empty`. Repeated produces its actual intersection-reference result without feeding that result into a new original-source request. Union and ordinary-row helpers use the original ordered member and pair lists. Physical construction receives resident outputs from their continuations.

`body_certified:421` inspects the actual current `SourceEqualityNativeDemand.body` yield. It proves `after.native=before.native` from the literal current operation and then certifies the exact emitted code at that returned machine. It handles arity rejection, conjoin failure paths with no yield, contradiction sentinel, and accepted zipped child code. It does not substitute the old eager `compileEdge`. The certificate is indexed by Machine, not full equality-operation state. It makes no claim that operation effects disappear; those effects remain in the supplied checked yield and need separate physical prefix invariants.

## CPS and exact scope boundary

`certified_bind:87` composes actual returned machine extensions, including work and optional-binder done equations. Enter uses its literal allocated state; read uses its actual current read result. The shared `walk_certified:139` processes the source list in order and transports earlier result residency through later machine extensions. It requires only membership properties, not a result identity or path uniqueness premise.

The universal continuation conditions for Valid, Extension, SemanticReady, and returned residency are physical conditions on a possible return. They do not assert that a recursive return exists. The public compiler results derive the local certificate from initial scope, representation readiness, and actual checked yield where relevant. They require no `Completes`, `requiredFuel`, `Words`, `WordRanges`, supplied native result, or recursive body-law callback.

This is intentionally a local certificate. Failures certify True, and finish instructions certify their continuation at the same Machine. The certificate alone does not prove a driver frame is protected, that a warm owner matches its candidate, that every recursive body completes, or that every raw checked prefix retains the certificate. Whole-prefix admission still needs the actual driver-state induction, exact owner readback, physical readiness and operation-state preservation, and domain-allocation trace transport. The module does not claim current general recursive WordRanges or general outer convergence.

## Imported validation

The final canonical Audit passed 2700 jobs and checked 61554 theorem dependencies in `lean-audit-final.log`. This owner ran no canonical build.

Pinned Lean 4.34.1 direct imported checks passed on their first attempts, with all linters and complete explicit proof/universe/deep-term/name printing: eight public axiom/full-signature pairs (`source_closed`, `Certified`, `certified_bind`, `walk_certified`, `mu_certified`, `reference_certified`, `node_certified`, `body_certified`) and two meaningful integration pairs.

`original_mu_compiler` starts from two actual original available Mu records. It constructs the local compiler certificate under the computed initial inventory and extracts the exact new extended-key membership from that same enter certificate. It supplies no completed execution, word bound, semantic output law, or future key list.

`actual_checked_body` starts from one literal current checked body yield. It retains the exact full native-state identity across that operation and certifies its actual emitted code. Its standalone full signature has no Symbol equality, word, or completion premise.

Both final logs are terminal exit 0. They contain no warnings, errors, `sorryAx`, omission, or truncation markers. No production, Git, Haskell, older evidence, or Audit source was changed by this review. Host forcing and runtime correspondence remain separate.
