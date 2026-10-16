# Current checked native structural result audit

Reviewed at 2026-10-16T16:09:21+02:00. Read-only declaration and source inspection. No proof source, Haskell, Git, or Audit change. No build or new theorem is claimed.

For the current target entry, no counterexample to finite-ordinary result closure or height bounded by EACH operand was found. The accepted constructor path supports this bound without a guard-truth premise. There are two necessary restrictions: a suitable initial warm structural certificate and an empty seen-pair domain. Physical/semantic validity alone does not supply the structural certificate.

## Minimal stored certificate

Use the new generic `SourceCurrentAllocatedFiniteOrdinaryDomain.Node`, `.Rows`, `.Children`, and `.Edge`. Its raw metadata and guards remain unrestricted. In particular, pure Node does not imply cached `.free=[]`; physical residency and semantic cache facts must justify cached metadata when a completion adapter needs closedness.

The proposed structural law can be heap-independent:

```
NodeResult request result :=
  Node request.left → Node request.right → request.domain.key.seen = [] →
  Node result ∧ height result ≤ height request.left ∧ height result ≤ height request.right

EdgeResult request result :=
  Edge request.left → Edge request.right → request.domain.key.seen = [] →
  Edge result ∧ edgeHeight result ≤ edgeHeight request.left ∧ edgeHeight result ≤ edgeHeight request.right

Stored native :=
  ContextCache.Returned NodeResult native.nodes ∧
  ContextCache.Returned EdgeResult native.edges
```

A full `request.domain.key = emptyKey` premise is a simpler valid initial scope. The empty-seen premise is sufficient for the branch obstruction below. The law stays conditional on input domain membership, so unrelated warm Mu/reference/union cells need no invented structural certificate. EdgeResult needs no matching-symbol premise for this structural conclusion. Actual joining supplies symbol agreement separately for semantic proofs.

`ContextCache.Returned` is the actual all-returned-cell predicate. `ScopeCache` already shows the exact empty/advance/lookup/demand/finish lifecycle pattern. The new Stored should derive at empty tables, retain exact old cells at lookup and demand, and finish only from its literal evaluating owner plus a LOCALLY DERIVED NodeResult/EdgeResult. Heap advancement changes neither request nor result, so these laws need no heap-growth premise. Do not substitute old eager `Produced` as the actual checked body provenance.

## Request keys and owner readback

`SourceRecursiveIntersectionThunks.NodeRequest` stores the actual interned domain and ORDERED complete operands. EdgeRequest stores the actual domain and ordered complete edge records. Physical native state has separate node and edge tables; it also retains the current constructor heap and domain cache. Checked `SourceEqualityNativeDemand.State` adds current equality operations.

Node keys are `(domain identity, tagged left, tagged right)` through `SourceRecursiveIntersectionMemo.requestKey`; unresolved placeholders bypass the table. Empty is cacheable with code -1; ordinary node uses `4*identity`. Edge keys use the domain and raw ordered edge identities through `SourceRecursiveIntersectionEdgeMemo.requestKey`. Do not canonicalize the key by swapping: source comparison is inside the body AFTER publication. Word checks are required for injectivity.

`PhysicalCache.node_request_exact` and `.edge_request_exact` prove full captured request equality from physical Valid, NodeReady/EdgeReady, safe current words, literal publication, and literal stored cell. The key-injective lemmas identify domains AND complete physical operands, using current coherence and availability/residency. There is no need for a separate desired owner-value equality assumption.

For an actual selection/demand pair, `.node_ready` and `.edge_ready` give the exact requested returned cell in the chosen table, unchanged demand state, and actual output residency. `.node_started` and `.edge_started` identify the evaluated captured owner with the requested record. Their initial arguments are physical only. Combine that readback with the new Stored. Do not use Provenance.Valid or NodeProduced/EdgeProduced as lifecycle premises.

## Exact result constructors

| Reached branch | Structural argument |
| --- | --- |
| Empty operand | Literal Empty result; height 0 is bounded by either input. |
| Closed self | `Control.self_record` plus current coherent resident operands identifies both full records. Return the left domain and equal heights. |
| Swap | Actual recursive request reverses operands. Exchange the two derived inequalities. |
| Reset | Actual recursive request uses emptyDomain with unchanged operands. Transfer its two inequalities. |
| Repeated pair | Must be excluded by empty seen. It returns a recursive reference and is not in this domain. |
| Ordinary node | `compileRows` walks literal `Kernel.pairs leftRows rightRows`, then raw makeNode. Each result edge is bounded by both captured input edges. |
| Edge mismatch/rejection | Actual `Demand.body` emits `CheckedCode.sentinel`: raw makeEdge of top with `[Empty]`, after empty-field allocation. Its edgeHeight is 0, even for nullary originals. No equal-arity output assertion is valid here. |
| Accepted edge | Actual checked field load/conjoin/check returns combined. Only then does `CheckedCode.children` walk `left.children.zip right.children` and raw makeEdge with `readback combined`. All₂ local node certificates give both child-height bounds and domain children. |

Mu/reference/explicit-union payload branches cannot occur on domain operands. No optional-binder construction or free-binding lookup is needed in this fragment. Full guards and nonempty normalized equality fields are allowed. A rejected constructor skips children. Structural bounds need no assumption that either guard accepts a term.

`Kernel.pairs_member` gives both input memberships and matching symbols for every actual joined pair. For each returned edge, use those memberships and the dual edge bounds. Apply `MergedOrdinaryHeight.makeNode_bound` separately to the left and right parent heights. Do not replace pair order/multiplicity by an arbitrary Cartesian supplier. The join emits finite ordered pairs; order does not affect these maximum bounds, but remains part of the actual graph.

The new Domain exports actual makeEdge/makeNode/ordinaryUnion closure and bounds. They retain current coherent/cached/linked and complete available/resident readback premises. `SemanticReady` supplies those facts at each returned constructor heap. These constructor lemmas do not prove a whole checked-native request bound by themselves.

## Actual graph and completion route

The principal preservation theorem must be scoped to a completed `requestNode`/`requestEdge` execution, or to statically certified source code. An ARBITRARY physical Trace does not preserve Stored: literal `.finishNode handle arbitraryAvailableValue ...` can install a result with no structural law. A local FinishThrough premise containing the root's desired law would hide the main proof obligation.

`PhysicalTraceCompletion.Trace` records every exact yielded checked step plus its physical Inputs. `SemanticTraceReadback.bind_inverse`, `.walk_readback`, `.cons_readback`, and `.work_readback` isolate actual child requests and actual constructor returns. `.effects` derives prefix Good/Extension/Keeps/operation growth from initial Good. `DemandNodeReadback.of_trace/of_done` distinguishes actual direct, ready, and evaluate branches. Physical keys rule out the direct placeholder path for finite-ordinary operands. The edge readback must follow the CURRENT checked body, not old compileEdge's eager child path.

A suitable proof is mutual strong induction on the supplied completed trace length for node calls, edge calls, and their ordered child/row continuations. Each recursive request is an exact shorter subtrace. Thread the new Stored through those actual prefixes. Derive parent NodeResult/EdgeResult from local child certificates and literal constructor readback BEFORE installing it at its own finish. `DemandRunning.node_body_cell/edge_body_cell` protects the exact selected evaluating handle; no future owner-survival assumption is needed. Existing ScopedCode callbacks provide only Scope, so they cannot supply the new height law without an additional structural code predicate/interpreter.

For completion, reuse `PhysicalTraceCompletion.initial_complete`: initial Good, Idle, actual Original operands, availability, cached closedness, and reached WordRanges construct a physical receipt and final Idle. Do not infer Trace from arbitrary raw done. `AllocatedTargetWorkerNative.of_done` already derives the SAME TargetQuery.Step from legitimate initial Good/Idle/available/closed/WordRanges and raw done, using constructed completion plus `ColdClosedExact.completed_unique`. `TargetQuery.Step.run` contains the actual Trace; `.done/.unique` preserve full returns. TargetQuery.finite/Step.verified additionally retain the computed inventory and global bundle. The new structural verification can then inspect THAT same Step; no old scoped native engine is needed.

## Concrete schema obstruction and source limits

`Control.decision` checks repeated pairs before ordinary payload. Two distinct ordinary records with ordered identities i<j and an arbitrary canonical domain with `free=[]`, `seen=[(i,j)]` select `.repeated (i,j)` and return `.reference (.intersection i j)`. This refutes unconditional domain closure for arbitrary request domains even though the operands have no Mu/ref/union. It is not a current source bug: public `intersect` starts emptyDomain, and this finite-ordinary fragment never enters a Mu domain. The structural law must state that scope explicitly.

Live Haskell Interned/Operations.hs:480-522 matches node keying and guard order. Lines 564-579 publish raw ordered edge keys, test arity before zipped child work, then call mkEdge with conjunction. The Lean checked body models the early source constructor check and its exact returned operation state. No historical Mu height fixture is used as a counterexample in this domain. No source repair or broad validation rerun is warranted from this review. GHC forcing/publication, host tables/IDs, and the later full local/class/outer structural composition remain explicit boundaries.
