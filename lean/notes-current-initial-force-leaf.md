# Current library proof status and complete initial Force and Leaf

This checkpoint starts at published 7b774272. Proof commit is 4f815db0.
Source main remains c0cc8a05, merged at 896b0a1c. The complete public
Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of contracts. Specify the intended behavior first. Then
prove that the current Haskell implementation has that behavior. Initial
support and resources must not assume a later successful call or result.
Documented errors and validation order are observable results.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts. Passing builds do not give a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and rank/unrank inverses. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, including nested Mu and unions, with physical stores and causal payload bounds. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive reads | Initial resources construct closed recursive collection and row exposure with exact heaps, literal row widths, and stable replay. | Remaining callers and public correspondence. |
| Comparison and selection | Initial counters and causal mass construct repaired worker success with exact histories, heaps, and stable replay. | Remaining callers and independent language-law hypotheses. |
| General memo-aware Merge | Initial resources compute sufficient work and selection fuel. Full allocated replay retains equality state, heap, memo, and winner. | Remaining callers and Haskell runtime correspondence. |
| Recursive intersection | Supported closed operands construct stable semantic execution at initial computable fuel. | General constrained callers and public correspondence. |
| Native query programs | Initial forecasts construct supported finite indexed query sequences with language, stores, origins, globals, and resources. | Adaptive caller control flow and concrete capacity. |
| Selected Operand | Initial forest, signed path, counters, and causal mass construct projection then Merge, with exact full worker return, receipts, Profile, and Frame. | Remaining caller composition and concrete capacity. |
| Interleaved Target | Initial profiles and reservations construct the actual head Operand, recursive tail, and query sequence with complete receipts, states, and common-fuel worker result. | All-root cap and selected-domain assumptions remain explicit. Runtime correspondence remains open. |
| Shared Force and Leaf | Initial class facts, valid slot laws, and numeric reservations construct miss or hit Force, then Leaf's checked query at its actual return. Both preserve full shared state, receipts, Frames, profiles, caps, inventories, and global memos. | General mixed Edit/ClassPass execution and resource forecasts. |
| Mixed editor and class pass | Actual reads and source class order preserve stores and finite syntax depth. | Initial complete Edit and ClassPass execution and forecasts. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver proofs remain preserved. The Lean
definitions are handwritten. These component proofs do not yet establish
complete correspondence with compiled Haskell.

## Complete initial shared execution

`SourceCurrentConstrainedCapSharedForecast` defines the initial schedule.
Force uses the initial target slot's `Option.isSome` value. A hit keeps
the initial Profile, needs no Target reservation, and uses zero Force
fuel. A miss uses the complete Target forecast for the literal
`operandPaths record.paths path` list. Leaf adds one native forecast
after that exact Force profile. Its initial reservation includes Room
at that query entry. Its fuel is the maximum of Force and query fuel.

`SourceCurrentConstrainedCapForceNumeric.complete` handles both slot
branches. A hit reconstructs the existing full receipt from the stored
historical receipt. It returns the same target, shared state, inventory,
and global memos. Its cap follows from the initial universal slot law.

A miss constructs its actual Target with TargetNumeric.complete. Initial
selected class domains derive the literal operand domains. The existing
selected-inclusion theorem supplies the class language law. Ready.store
installs that exact target and full historical receipt. The existing
MixedShared.force_receipt derives the universal new-slot certificate from
the actual Target reads. Earlier slots retain their values. The same
return has a full Frame, computed Profile, semantic Merge laws, cap,
inventory, global memos, and exact common-five-fuel Force worker result.

`SourceCurrentConstrainedCapLeafNumeric.complete` calls this Force endpoint.
Its actual returned target and shared state feed the native checked query.
The original input stays available through Force's heap preservation.
Initial input closedness and cap remain explicit. The target cap comes
from Force. The query uses their maximum depth and derives its resource
bound from Force's returned Fits and the initial Leaf reservation.

The checked query returns the complete Frame and next Profile. Its state
advance preserves the target table and every earlier slot certificate.
The old complete Leaf receipt retains actual graphs, reads, readiness,
extensions, Merge tables, global memos, availability, closedness, narrowing,
and preservation. Existing stability lifts Force and query to leafFuel.
The full Leaf worker returns the same result and complete shared state.

Neither endpoint takes ForceRanges, Leaf.Ranges, a future completed graph,
a successful future fuel, a returned heap bound, or a callback resource
law. The complete actual execution and reached laws are outputs. Their
numeric ceilings cover each worker fuel argument. They do not count the
sum of host instructions.

## Constructed integration evidence

The integration constructs ordinary roots from literal rows and a class
record from `recordOf [[0],[1]]`. It derives coherence, nontriviality,
selected domains, initial Shared.Ready, and MixedShared.Stored. An open
unselected sibling remains in the captured forest. A prepared equality
descent operation has an actual stored record and a validity proof.

One kernel constructs a missing-slot Force. Its produced slot gives a
literal zero-fuel warm Force at the exact returned shared state. Another
kernel constructs a missing-slot Leaf and a second Leaf with the first
result as input. It passes the first complete returned state, Frame,
Profile, inventory, slot histories, and global memos into the second call.
The second Force uses the produced slot. Both worker returns and the
retained descent record remain in the public theorem.

These kernels take only formulas and solver. They derive a sufficient
finite width from one composed initial numeric forecast. They take no
future state, result, successful execution, or later reservation. Warm
reuse concerns the class target slot. The proof does not assert a native
query hit or an unchanged second checked state.

## Exact support and contract boundaries

Selected ForestClosed domains permit unrelated open ordinary roots and
siblings. A separate cap premise bounds every original captured root.
It can exclude an unrelated nonhereditary Mu body. General source support
must discharge or replace that stronger premise separately.

The Target receipt retains one-way inclusion for nonempty proper selected
paths. Merge can overapproximate its input. The whole Target language is
not proved equal to the intersection. Each checked native query retains
its exact intersection law. Leaf retains narrowing and preservation under
the existing explicit class-satisfaction contract. This checkpoint adds
no editor-wide path-mask theorem.

Initial MixedShared.Stored includes valid laws for every warm target slot.
Historical receipts refer to the immutable captured base and forest.
They are separate from the current checked inventory. The new execution
preserves both. It does not assume a newly successful Force as a premise.

Numeric bounds control constructor counters, domain counters, and causal
constructor payload mass. Full allocated equality and target-slot states
remain exact. Equality-table size and instruction counts, concrete bytes,
solver work, wall time, concurrency, Haskell lazy demand, and memo
publication remain separate obligations.

## Next caller: mixed Edit and ClassPass

The general mixed editor has an actual graph and worker completion from
that graph. Its current finite producers still need NodeRanges,
ChildrenRanges, ListRanges, or equivalent per-callback range laws.
ClassPass also takes a range law at the actual preceding class return.
These premises do not construct the whole initial execution.

Derive a pure initial editor forecast for source head, child, and row order.
Use actual row widths and reconstruction growth. Feed each returned shared
Frame, Profile, current Merge table, slot laws, inventory, and global memos
into the next stage. Derive Force and Leaf reservations from that one
schedule. Do not assume an actual future graph, reached bound, or successful
worker. Then compose the class fold in its literal source order.

## Remaining library work

1. Construct complete mixed Edit and ClassPass from initial resources.
2. Complete active and stored outer descent, arbitrary constrained Mu
   bodies, and the full source gate. Separate selected domains from
   stronger all-root cap assumptions.
3. Prove repeated reduction convergence and remaining recursive callers.
   One complete modeled pass does not prove convergence.
4. Complete current typing, refinement, drawn-field, symbolic-measure,
   observable-error, validation-order, and generator-rank adapters.
5. Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
6. Compose the complete public construction, transformation, graph
   conversion, exact query, generation, and sampling pipelines.

The complete library goal stays active.

## Haskell repair handoff

No Haskell patch or new behavior defect is added. Root FINDINGS keeps the
external repair registry first. Repair b9219b9e is merged in source
c0cc8a05. Derivation validation rejects a field pool for the datatype itself.
The retained Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone `holds` still treats pool
descendants as opaque. Reuse the unchanged strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence. Record each
later repair in FINDINGS with its failure, executable reproducer, affected
paths, commit, checks, and upstream status.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2939 jobs and 65012 dependency checks.
All three final production strict logs are empty. All 33 complete signature
and axiom pairs pass in six groups: 27 public declarations and six
constructed checks. Only propext, Classical.choice, and Quot.sound occur.
Four component manifests verify 101 entries. Read checkpoint-validation.json
in lean/restart-evidence/20261017-initial-force-leaf/ for exact hashes.

Preservation retains 14399 starting files, 2933 older non-Audit proof
sources, all 239 Haskell files, all 206 active-package files, two stashes,
and three other worktrees. All 88 frozen module manifests retain 694
entries. Older proofs, counterexamples, repairs, and marked drafts retain
their bytes. Failed strict sources and raw logs remain in the evidence.
