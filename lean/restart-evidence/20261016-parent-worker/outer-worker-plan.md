# Next: literal eight-family outer worker

Reviewed 2026-10-16 14:11 CEST. Source main is c0cc8a05. This is a source and interface audit. It does not add a worker or prove general outer termination.

## Minimal state and API

Reuse `SourceCurrentAllocatedPartialState.State width` (`:52–57`). It contains the complete Checked state, warm merge memo, fourth memo, and separate node/edge FlatMemoThunk states. Do not add a new owner map: each FlatMemoThunk cell already stores its original request, status, and handle. Keep the request keys exactly `NodeRequest.key` and `EdgeRequest.key` (`:44–49`): inherited allocated identity plus tagged NodeRef or full edge identity. The two outer families differ from the native intersection tables already inside Checked.

Use one generic `Outcome width A := done A Caller | failed Fault Caller`. Failures must retain full lower observations, including class target slots nested inside a Local/Parent fault. Suggested faults are parent observation, inherited error, missing inherited value, Mu pending key, unexpected reference, node/edge busy handle, node/edge absent handle, and outer exhaustion. A body failure leaves its actual evaluating cell in the returned state. It must not call finish or erase the cell.

Expose eight functions matching `SourceCurrentAllocatedPartialGraph` (`:46–118`): nodeCall, nodeBody, edgeCall, edgeBody, rows, descendants, children, and walk. Arguments contain the nine lower bounds g/s/r/e/p/h/m/c/n, a separate outer recursion bound, and fixed algorithmic conjunction budget. Keep returned Caller state literal. The global query Memos remain a separately constructed strict Reads index, not an executable argument.

## Source schedule

`Equality/Operations.hs:80–91` memoizes before the node body. Empty returns Empty. InternedUnion returns unchanged. The Mu pattern reconstructs through createMu (`Interned/Type.hs:671–676`); execute literal `SourceEqualityMuReconstruction.rebuild`, including its pending state. Do not replace arbitrary Mu reconstruction with identity. At a resident clean Mu, `SourceCurrentAllocatedMuRebuild.resident_rebuild` (`:143`) and `actual_rebuild` (`:162`) derive cleanup and the unchanged heap from Ready plus the separate ProbeHeap. Ready alone does not supply clean probes.

Ordinary node rows are read in their existing order. For each original edge, run the reduced-edge memo call, then descendants of its RETURNED edge, then the remaining original rows (`Operations.hs:87–96`; Graph.Rows.cons `:89`). A parent may return a sentinel with Top and one Empty child. Descendants must read that returned raw field and children. They cannot use the old edge shape or old children.

Descendants run the inherited prefix once. Inherited contradiction returns before the own accessor. Otherwise the prefix reads the returned raw field, then combines inherited first and own second (`SourceCurrentAllocatedInheritedPrefix.run:30–43`). Error and missing return the prefix's actual operation state. On success, contradiction erases the current child list without recursive calls. A live payload runs the indexed walk in ascending original positions. For each head, execute literal `PartialGraph.descend` (`:31–35`) at the CURRENT operations, call the resulting node request, and carry its return into the tail.

After descendants, call `RawRebuild.edge originalReturnedEdge results currentChecked` (`:30`), not MkEdge. The child walk preserves length, so this is source setChildren's raw same-arity branch. It retains symbol and full returned raw guard. After rows, call `RawRebuild.modify originalNode oldRows newRows currentChecked` (`:47`). Its ordered edge-identity equality fast path must remain literal (`Interned/Type.hs:622–632`). Do not sort rows or compare only accepted languages.

## begin/demand and ownership

`PartialState.beginNode:68` and `beginEdge:75` run lookupOrInsert followed by demand. They publish before dispatch. Their incomplete cases come from `FlatMemoThunk.Observation` (`:164`):

- ready: return that result and the exact post-begin state; execute no body.
- evaluate original: run the STORED original request. A later candidate with the same key does not replace it.
- busy: retain the exact post-begin state as incomplete. No successful graph constructor covers it.
- absent: retain the exact post-begin state as a distinct incomplete observation. Protocol excludes a linked absent cell, but the raw worker must still define the case.

A ready hit should not require positive body fuel. Inspect begin before charging evaluation fuel. If evaluation fuel is exhausted after begin, retain the published evaluating cell and the selected handle in the fault. Other structural traversal ticks may use a simple decreasing bound. Document the chosen fuel schedule; it is a bounded observer, not Haskell runtime fuel.

On body success finish only the handle returned by that begin. `PartialFrames.beginNode_owner:104` and `beginEdge_owner:126` identify its exact evaluating request. `PartialFrames.node_body/edge_body` (`:273/:283`) protect pending owners through an actual successful body. `PartialCallSteps.node_finish/edge_finish` (`:104/:138`) derive the completed law from the body post and law. They do not prove the body completes. If the worker permits corrupt raw states, a silent finish can be a no-op; physical owner/returned-cell guarantees need the existing Protocol/Context proof, not merely a raw done constructor.

## Honest proof order

1. Define the literal eight workers and every failure. Do not take a recursive callback as an execution premise.
2. Prove supplied successful worker output yields its same raw graph. Success reconstruction can be unconditional where the body result already carries all literal equations.
3. Prove successful monotonicity in the outer and nine lower bounds. Keep the source conjunction budget fixed. Then derive full-return uniqueness across successful bounds. Failure outcomes need not be stable.
4. From a finite raw graph plus its same actual source-field equations, derive stable sufficient bounds. Graph-to-execution does not derive general finite graphs.
5. Under initial Context and reached machine-range plans, construct the strict source Reads for the worker's own return. Use strict primary reads through the current Parent/Local Actual adapters, never infer strict reads from historical erased reads.
6. Apply the eight existing `PartialActual` endpoints (`:228–280`) to those same actual traces and Reads. Their Context/Post carries computed inventory, operations, semantic/cost/probe facts, warm caller laws, merge and fourth memo extensions, fourth correctness, and global validity.

Do not quantify Checks over an assumed future completed graph in a theorem advertised as general finite completion. The current `PartialChecks.Checks` (`:142`) is indexed by a completed Trace. It is valid for same-trace soundness, but it cannot supply the missing recursion measure. Similarly, body-finite, no-busy, or future Context callbacks would restate the central completion obligation.

## Remaining completion and runtime limits

No existing local completion theorem supplies a decreasing measure for arbitrary recursive outer requests. Unequal-length classes can move constrained structure deeper (`Operations.hs:129–141`). A serial logical worker can stop at busy cells; it must not claim that a busy source thunk is an empty language. Unfinished-cell exclusion requires an independent progress/rank argument for the intended domain. The memoized pair key's finite allocation is not enough if local transformations create new identities or inherited payloads.

The public reduction performs one pass. Repeated-pass convergence remains separate. The source's lazy lists, IntMap order/forcing, Typeable caches, publication-before-demand, global events, exceptions, concurrent GHC black holes, machine identity widths, and noConstraint CAF need their own transfers. Existing graph and Reads theorems describe completed serial source schedules. Unchanged Haskell source uses the already validated 798 examples plus golden; this audit runs no Haskell or canonical Lean build.
