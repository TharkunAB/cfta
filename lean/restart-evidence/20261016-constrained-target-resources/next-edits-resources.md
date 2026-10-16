# Cumulative resources after whole Target

Reviewed 2026-10-16 20:51 CEST. This is a read-only proof plan. No production file, build, Git state, or Haskell file changed for this review.

## Established starting point

`SourceCurrentAllocatedFiniteOrdinaryTargetResources.target_complete` (`lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryTargetResources.lean:196`) now constructs the whole actual Target from initial forest profiles and initial constructor headroom. It returns the same Target graph, Reads, full receipt, stable literal execution, computed inventory, native structural and output certificates, Merge profile certificates, output profile, height bound, and an actual ConstructorWork trace with request bounds. Its `fold_complete` at line 97 follows head operand, recursive tail, then native intersection. The native query and projection-plus-Merge resource producers are dependencies, not remaining gaps.

The next cumulative stage is shared Force/Leaf, followed by compiled edits, one class, and the complete right-fold pass. A bound for one Target does not yet bound the number of targets or queries made by these callers.

## Exact schedule and counts

| Stage | Current source anchor | Actual order and resource event |
| --- | --- | --- |
| Class entry | `SourceCurrentAllocatedClassEdits.lean:31` | Capture the literal entry forest. `SharedTargetState.initial` clears only class-local target slots. Keep checked execution and the warm Merge memo. |
| Force | `SourceCurrentAllocatedSharedTargetForce.lean:40` | A present slot returns the same value and full state. An absent slot runs one Target on the fixed captured forest and then stores the literal returned value, checked state, and Merge memo. |
| Leaf | `SourceCurrentAllocatedSharedTargetLeaf.lean:34` | Force first. Then run one native intersection of the target with the current input. Advance checked execution and retain slots and Merge entries. |
| Selected child | `SourceCurrentAllocatedSharedEditGraph.lean:50` | Edit the selected head, then scan the remaining children at its exact returned state. Unselected children do not invoke a callback. |
| Ordinary rows | `SourceCurrentAllocatedSharedEditGraph.lean:64` | Edit a row's children, intern that edge with its original symbol and full guard, then process the remaining rows. Intern the node after all rows. |
| Class pass | `SourceCurrentAllocatedClassPass.lean:32` | Complete the tail classes first. The head captures the tail's returned forest and warm state. Propagate Empty after the whole fold. |

For one coherent active record, let `m = record.paths.length`. `operandPaths` removes the selected path and retains source order (`SourceEqualityClassTarget.lean:21`). Coherence supplies distinct paths (`SourceEqualityClassEdits.coherent_supported`, line 58). A small pure length lemma can therefore derive exactly `m - 1` target operands for a selected member. Active records have at least two paths.

A first force then makes `m - 1` projection-plus-Merge operands and `m - 2` internal native intersections. Each path can miss at most once within the class because Force stores it and later operations retain present slots. Thus at most `m` targets are constructed. This is an upper bound; some paths need no force.

Every executed leaf occurrence still makes one native query, including a leaf that hits its target slot. The number of native leaf queries can exceed `m` because an edit path passes through many alternative rows. Count source positions, including repeated values and rows. Do not count only unique identities or compiled callback tokens.

There is an important Empty case. `FiniteOrdinaryOccurrences.node` returns `(0, 0)` for Empty (`SourceCurrentAllocatedFiniteOrdinaryOccurrences.lean:17`). An `EditNode.leaf` on Empty still runs its callback. The existing ordinary node count alone cannot bound the number of leaf queries.

## Warm invariant required at the shared boundary

`SharedTargetState.Ready` retains historical SlotReceipts (`SourceCurrentAllocatedSharedTargetState.lean:45` and line 56). Those receipts retain exact historical Targets, heaps, Merge histories, and semantic receipts. They do not give a numeric output profile. Their historical inventory need not equal the current inventory.

`FiniteOrdinaryShared.Stored` contains native structural certificates, Merge domain certificates, and a domain fact for each present slot (`SourceCurrentAllocatedFiniteOrdinaryShared.lean:31`). Domain and height bounds do not imply row or arity bounds.

The next small producer should carry these proof facts beside the existing runtime state:

- Native structural Stored and native OutputStored at the current checked state.
- Universal MergeProfileCache.Stored for the current Merge memo.
- For each present target slot, a row/arity profile and height bound computed from this class's fixed captured forest and target path count.
- Existing full Shared Ready, current inventory admission, captured-heap retention, physical Merge Stored, semantic CacheCovers, and valid global memos.

Fresh class slots discharge the slot obligation without a result oracle. A miss derives its certificate from the actual `TargetResources.target_complete` result before storing it. A hit reads the existing certificate and makes zero Work requests. Checked or constructor advancement retains it. An API for arbitrary initial warm slots must take an initial causal profile invariant or prove it from the historical slot graph. It cannot infer it from domain-only Stored.

Force and Leaf resource theorems must preserve the same checked state, operations, native tables, domains, Merge table, slots, global receipts, and computed inventory. The fourth memo stays external to these components and is retained by the existing effects. No table may be reset to simplify a bound.

## Input-only envelopes to prove

The following formulas are proposed conservative bounds, not existing theorems. Let one class capture a forest with uniform profile `(R, A)`, length at most `C`, height at most `H`, maximum record path length `D`, and `m >= 2` paths. Use the already proved Target definitions:

```text
T  = TargetResources.outputRows R C D H (m - 1)
A1 = max A 1
Q  = NativeBudgetNumbers.nodeBudget (max T R) A1 H
R1 = (max T R) * (max T R)
V  = C * (1 + A * OccurrenceBounds.edgeCount R A H)
```

`T` bounds every stored target because every target reads this same captured forest. `Q` bounds one leaf query. The native budget bounds total node-plus-edge requests, so charging it separately to each constructor supply is conservative. The sentinel requires `A1`, even when `A = 0`.

Prove a value-position count that includes Empty. `V` is a safe candidate: charge every root position and every literal child position of every source row. The existing bounds at `SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.lean:62` and line 111 bound ordinary node and row occurrences from profiles, height, and forest length. Add the child-position argument; do not silently reuse ordinary nodeCount for Empty leaves.

Within one compiled class, traversal continues through the original immutable input rows and remaining siblings. A callback's new output is returned at that position; the same edit does not traverse it again. Prove this fact in the actual edit graph induction. It permits these proposed per-class request bounds:

```text
nodes <= m * TargetResources.nodeBudget R A C D H (m - 1)
         + V * Q + C * OccurrenceBounds.nodeCount R A H
edges <= m * TargetResources.edgeBudget R A C D H (m - 1)
         + V * Q + C * OccurrenceBounds.edgeCount R A H
```

The final terms charge raw rebuilding even on constructor-cache hits. The first terms charge all possible first forces. The middle terms charge every possible leaf occurrence. A tighter bound can follow later; no sharing or source branch needs to be removed for these bounds.

Derive a uniform output forest profile `(R1, A1)`, the original forest length, and height at most `H`. Below-edits keep original row multiplicity and child arity. Leaf outputs use the native output profile. Existing positional `NodeNarrow` supplies domain and height, but a new profile proof must supply row and arity bounds. For a generic edit API, captured originals and edited inputs can differ; use separate profiles there. The class-specialized graph identifies them at `SourceCurrentAllocatedClassEdits.lean:36`.

## Minimal proof order and API contracts

1. Add a shared resource invariant and Force/Leaf producers. Inputs are legitimate initial Shared Ready, captured Values/profile, causal table/slot certificates, semantic coverage/global validity, selected path facts, and initial cumulative headroom. Return an actual graph, Reads, the existing receipt, the updated resource invariant, output profile, and an actual bounded Work trace. A hit consumes no Target budget. Every leaf query consumes its derived native budget after Force.
2. Add positional occurrence/profile algebra and edit resource producers for node, children, rows, and list. Induct in the actual state order. Derive current prefix headroom by subtracting earlier request budgets from the initial total. Do not ask for a future prefix capacity, output profile, or completed current callback.
3. Add a compiled Class resource producer. Start with fresh slots and derive compiler validity, populatedness, allowed paths, disjointness, proper paths, and safety from `SourceCurrentAllocatedClassEditPlan.lean:18`, lines 22-39, and line 61. Prove the at-most-`m` miss count from literal slot retention. Return the same existing Class receipt and conditional class-language law, not a stronger Merge language equivalence.
4. Add a Pass resource producer. Recurse on the tail first. Compute the row/arity envelope for the head from the tail result, then add the head's budget. Carry `C` and `H`; update rows and `A -> max A 1`. Each record retains its literal paths and path-depth bound. Existing receipt domain transport (`SourceCurrentAllocatedClassPass.lean:92`) retains their support. Sum budgets in this same right-fold order. A sum that uses the original row bound for every class is unjustified because preceding class results can increase rows. Final Empty propagation performs no Work and preserves the bound.
5. Compose Require, Scan, local reduction, Parent, and the whole outer caller. Existing component semantic and finite execution theorems remain available. Their complete input-only cumulative constructor headroom still needs this composition.

Each constructed endpoint should return its exact actual graph and strict Reads together with the existing physical/semantic receipt and the new Work trace. A separate supplied-execution endpoint may align a successful literal worker with that constructed result by the existing unconditional whole-state uniqueness. Neither endpoint needs an assumed future result law.

## Existing numeric plans are not the cumulative proof

`SharedCapacity.ForceCapacity` and `LeafCapacity` (`SourceCurrentAllocatedFiniteOrdinarySharedCapacity.lean:35` and line 41) require TargetCapacity or Capacity at reached states. `EditCapacity.NodeCapacity`, ChildrenCapacity, RowsCapacity, and ListCapacity (`SourceCurrentAllocatedFiniteOrdinaryEditCapacity.lean:37`, lines 48, 62, and 74) propagate those requirements through actual earlier prefixes. `ClassCapacity` starts them at fresh slots (`SourceCurrentAllocatedFiniteOrdinaryClassCapacity.lean:34`). `PassCapacity` requires the head plan at each actual completed tail (`SourceCurrentAllocatedFiniteOrdinaryPassCapacity.lean:36`).

These plans avoid a current completed-result oracle, but they still contain reached-state headroom assumptions. The new resource producers must derive those assumptions from initial limits, or construct the finite components directly with the derived limits. Merely accepting the old plans does not close cumulative accounting.

## Source and whole-library boundary

`cfta/src/Data/CFTA/Equality/Operations.hs:211` runs RequireAll, the right-fold class pass, and final Empty propagation. Lines 236-245 define each class callback from the other paths of the class's captured forest. Lines 313-334 compile signed edits, ignore a list-root leaf, expose Mu/Union, and reject an unexpected Rec. The finite-ordinary profile excludes the recursive edit branch; this review does not transfer its accounting to general Mu execution.

Keep the existing source-call graph and explicit failure outcomes. These bounds count constructor Work requests, including cache hits and repeated occurrences. They do not prove a bound for equality-allocation counters, solver execution, host allocation, or GHC demand/publication order. Full root numeric-plan discharge, generated outer memo output profiles, general recursive termination, runtime correspondence, and the remaining API/Sized contracts remain separate whole-library obligations. Preserve approximate emptiness and conditional class-language directions exactly. Record any future Haskell repair in root FINDINGS before implementation; no Haskell issue or repair was found in this review.
