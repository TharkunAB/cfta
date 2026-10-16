# Required profile validation

Date: 2026-10-16 19:39 CEST.

The frozen source is `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.lean`.
It has 237 lines. Its SHA256 is `ff1a55ead7e444aefa5009164784d1aeaf3a715bc196216f81e974510e6e4694`.
The evidence source copy is byte-identical.

## Checks

- Direct source check 1: terminal exit 0, no diagnostics. Session 93884 was polled to its terminal result.
- Parent canonical batch: terminal exit 0, 1122 jobs. Parent confirmed the terminal result. The module has no diagnostics. The batch log retains warnings from other targets.
- Imported public probes: terminal exit 0. All 6 public declarations have an axiom probe and a full signature probe.
- Imported integration probes 3: terminal exit 0. All 4 kernels have an axiom probe and a full signature probe.
- Final public and kernel logs have no warnings, errors, or `sorryAx`. Reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

Kernel draft logs 1 and 2 retain failed elaborations and unused-binder warnings. Only log 3 validates the final kernel source. No production source change followed direct check 1.

## Public result

`head` and `node` preserve `NodeShape R A` at the same returned heap. They also derive Keeps, SemanticReady, and output availability.

`children` preserves `ChildrenShape R A` for the complete ordered result list. Its result length equals the original length. `rows` preserves `RowsShape R A`; its result length is at most the original length. Both return the same physical heap, semantic readiness, and resident results.

`requireAll_done` verifies the literal worker return. `finite` constructs a stable literal return from initial SemanticReady, availability, and the original profile. It derives input closedness from the current coherent resident records. Neither entry requires supplied child-result laws, completed callbacks, output profiles, or a final heap invariant.

## Proof scope review

The mutual induction follows the actual Required graph. Each smaller actual prefix derives its current semantic heap and resident records through the existing physical Required theorem. The profile induction supplies only the profile for that smaller graph.

Ordinary nodes use the actual returned rows and makeNode result. All₂ positional traversal retains child arity. Rejected rows do not traverse children. Retained rows run their selected children, rebuild with the same raw constraint, and then traverse the suffix at that returned heap. The actual constructor profile laws include coherent cache hits.

Profiles contain the finite ordinary domain, so recursive head branches are excluded by input inversion. Full guards and equality classes have no added restriction. The exact limits R and A remain unchanged; no squaring or arity widening is used.

The module is generic in Symbol and Guard. It models the existing ordered Required graph and literal instrumented worker. It does not claim a GHC demand schedule, full checked caller-state wrapper, native-query termination, or a new Work reservation. Root owns the independent Required reservation component.

## Kernels

1. Two constructed finite requireAll calls use the first returned heap, SemanticReady, availability, and exact profile to derive the second call. Their histories compose.
2. The empty path list returns the same forest and heap at zero proof bounds.
3. A missing index rejects a literal nullary row before child or constructor execution.
4. A selected unary child uses the identity node graph and the exact raw edge constructor result at its actual heap.

No older proof, Haskell, Audit, root document, or earlier evidence file was edited. This owner ran no Git or Lake command. All owned new text files have one final newline and no blank line at EOF.
