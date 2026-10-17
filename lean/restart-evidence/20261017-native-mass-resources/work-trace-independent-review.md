# Literal Work and checked-prefix mass review

Reviewed on 2026-10-17 at 06:58 CEST. No material defect was found.

Frozen review inputs:

- `SourceRecursiveIntersectionWorkMass.lean`: `2683ffd0d82b254bd5a91bc6fe6d0fd929af4856afa1ec51aea749eb88f41b3e`.
- `SourceCurrentAllocatedRecursiveMassTrace.lean`: `e9578e2d8fa8aea3eea4eab1dbf03eb8ba5476448976ff4fef1964518fda11b8`.

WorkMass derives literal edge, node, and union work bounds from an initial causal payload store. Each element bound and the original list length determine `inflate`. The constructor proofs retain earlier winning records. The union proof covers flattening, duplicate removal, ordinary-node flattening, and literal union allocation. It derives at most one node request and no edge request. Counter bounds use actual observed reservations and requests. They are not final-counter subtraction definitions.

`Inputs` indexes only pure, makeEdge, makeNode, and makeUnion Work. It retains actual available children or resident rows and a literal width bound. The generic run theorem does not assume an arbitrary Work continuation has a bounded result or identity function. Pure Work can return arbitrary data; its conclusion bounds stores and counters, not the mass of that arbitrary value. The specialized node, edge, and union theorems also derive their returned payload mass.

MassTrace's `step_bound` covers every checked instruction and every stopping outcome. Work uses the indexed input certificate and an initial store. OptionalBinder uses the actual current available body, initial physical facts, and the all-outcome source construction mass proof. Its complete nested construction is charged in that single checked instruction. Node and edge memo transitions change no constructor heap. Enter changes the domain cache. Reads and finish frames preserve the constructor heap. Checked edgeBody can change equality operations, but its actual heap remains unchanged. Thus the proof does not ignore an actual constructor write.

The ceiling joins the literal-constructor bound with the full optional-binder bound. The charge pays both constructor counters conservatively. The numeric iteration and addition theorems use only an initial bound and an instruction count. They do not inspect future payloads or later counters.

`domain_step_bound` uses the actual DomainAllocation trace with the singleton key emitted by a literal enter. All other controls use an empty inventory. Every actual instruction allocates at most one source domain, without a width premise. The prefix domain theorem adds this bound over the exact trace length.

`InputsThrough` remains an explicit certificate about the widths at reached Work instructions. `prefix_bound` combines it with the supplied physical Trace and initial Good, Fields, and Stored. The physical effects derive the next Good and Fields at every actual returned checked state. `initial_prefix` computes its initial Stored bound from that initial heap's physical facts. It retains Good, Fields, numeric store bounds, both constructor counters, and the domain counter.

These theorems verify supplied actual prefixes. Their fuel is an actual prefix length. They do not derive an initial upper bound on the length of a complete generated query. They also do not produce `InputsThrough` for every compiled query. The new CompileMass and CheckedMass modules supply local emitter bounds, but a whole-query invariant must still connect them through all frames and recursive returns. Equality-operation resource bounds and general constrained reduction termination remain separate.

The imported public probe checks 30 explicit axiom/signature pairs: ten WorkMass declarations, four literal Inputs constructors, and sixteen MassTrace declarations. The exact same imported kernel also passes. It constructs a used optional binder's own completion from initial Good and an available body. That actual return supplies the child to the next literal makeEdge instruction. The singleton width follows from the positive computed initial bound and its next ceiling. The kernel derives its own two-step physical Trace and width certificate. `initial_prefix` then gives the store and counter bounds at the same final state. One initial numeric credit condition yields final constructor word room. No later-entry room, future completion, returned mass, or callback law is supplied. Native memo tables, domain cache, and operation state remain literally unchanged in this example.

Both final source strict logs are empty. Public log 1 and kernel log 1 have no diagnostics. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Canonical WorkMass log 2 completed 1181 jobs. Canonical MassTrace log 2 completed 1205 jobs. They replay only the older `InternedFreshOrdinaryClosedCompletion.lean:24` unused-input warning. No production or older evidence file was changed by this review.
