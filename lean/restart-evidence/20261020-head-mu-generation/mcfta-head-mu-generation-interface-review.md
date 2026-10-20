# Actual Head Mu-generation interface review

Date: 2026-10-20, Europe/Stockholm. This is an independent source audit and an unchecked interface proposal. No Lean job or repository mutation was performed.

## Conclusion

The requested classifier follows the actual successful worklist recursion. It does not need a new execution machine. The missing information is the operation label on the publication selected from that recursion. The current issued Path forgets that label. A source build writer alone roots its publication in the generated encode syntax, not in the original program.

Use one public Head or Read producer. Private collect and nodeEdges classifiers can follow SourceCurrentHeadIssuedHistory. The exact initial complete-cell alternative must remain explicit. Do not recover an operation by selecting an arbitrary publication from a Path.

## Proposed contract

Let target be the complete value `.mu entry body depth ordinary`. Keep its lookup key separate from `entry.key` unless an existing coherence fact proves their equality.

Inputs:

- One actual successful `SourceEqualityRequiredHead.Head value before result after`, or `SourceEqualityProjectionRead.Read value before edges after`.
- `SemanticReady before`, `InternedFreshOrdinaryCostHeap.Heap before`, and `Available before value`.
- `after.nodeRecords key = some target`.

Conclusion:

1. `before.nodeRecords key = some target`; or
2. one tuple with a full parent Mu, operation-entry heap, operation result and operation-return heap. The SAME tuple retains:
   - `Available operationBefore parentMu`;
   - `unfold parentMu operationBefore = .done operationValue operationAfter`;
   - `operationBefore.nodeRecords key = none`;
   - `operationAfter.nodeRecords key = some target`;
   - `Nonempty (NativeMuIssuedHistory.Path before operationBefore)`;
   - `Grows operationAfter after`;
   - `Extends operationAfter.nodes.issued after.nodes.issued`;
   - the rich source `Context` at operationBefore for the exact mapped leaf inputs;
   - the exact completed build equation for `encode (leaves parentBody) [] parentBody` under those inputs;
   - `CompletedBuildRootedWriters.Written` for THAT generated root and THAT input list, from operationBefore to operationAfter, for the exact key and target.

The environment is the actual stored-unfold environment: the parent own interned reference maps to the COMPLETE parent Mu; every other reference maps to none. The input list is `(leaves parentBody).map (input environment)`. It is generally nonempty. Neither its slots nor the target writer become original-program slots by this construction.

`Written` already keeps one publication event, its same candidate equality, its first-write absence, its Reached route, its issued callback paths, and its later growth. Keep this witness intact. Do not independently choose another writer for the rooted route or a different operation for the prefix/suffix.

No initial empty-to-before History or Path is required. No closedness, supplied operation label, supplied Rooted Written, or desired row-origin assumption is required. CostHeap fits the existing effect APIs. A separate refactoring may remove it from this narrow classifier, but that is not necessary for this endpoint.

## Actual proof schedule

### collect

`MergedFreshOrdinaryExposure.collect`, lines 18-34, gives the complete schedule. Induct on the literal fuel and pending list, generalizing the selected key/full payload and initial state.

- Empty worklist, exhausted worklist, unresolved reference, empty value and node prepend cannot install a target Mu themselves. Node prepend retains the state. For a successful-only classifier, exhausted/unresolved/pending outcomes are impossible under the actual success equation.
- A visited union or visited Mu skips the value. Reuse the recursive classifier at the same heap.
- A new union expands `members ++ rest` at the same heap. Its children are available by the actual parent's Available proof.
- A new Mu executes its actual unfold, then continues at the exact returned heap with `result :: rest` and the updated seen set. The parent is Available at this entry; retain that fact before advancing the heap.

First classify the recursive tail's final target. If the tail supplies a new operation, prepend the actual first-unfold Path to its prefix. Its suffix already ends at this same collect return.

If the tail says the target was already present at the first-unfold return, classify that actual unfold interval. If the entry already contains the same target, return the initial alternative. Otherwise derive literal entry absence and use the operation as the new witness. Its suffix is the actual tail's growth and issued extension.

Literal absence is stronger than a negated exact-cell lookup, but it follows here. Inspect the entry record. If it is `some previous`, `Grows.nodeRecords` preserves it into the operation return. That return also contains the selected target at the same key. Option injectivity forces `previous = target`, contradicting failure of the prior alternative. No injectivity of cache identities is needed for this argument.

### nodeEdges

`MergedFreshOrdinaryExposure.nodeEdges`, lines 37-47, has a separate initial unfold for a Mu root.

- Empty, reference and node roots leave the heap unchanged.
- Union roots use the actual collect schedule, followed by state-preserving canonicalization.
- Mu roots first unfold once. If this returns a node, that operation is the entire exposure interval.
- If this returns another kind of value, fallback collect starts at the returned heap with `[ORIGINAL parent Mu]`, not with `[unfold result]`.

Therefore a fallback can execute a second, warm unfold of the same full parent. Classify the fallback first. If its prior-cell alternative reaches the first-unfold return, classify the first operation. Otherwise prepend that first operation's Path to the fallback witness. Do not collapse the two operation heaps or relabel the first installation as the repeated warm call.

Canonicalization and prepend retain the physical state. Their existing helpers are `SourceEqualityAnnotationExposure.canonical_state` and `prepend_state`.

### Read and Head

A Read is the actual successful nodeEdges equation at its recorded fuel. Unwrap it once.

A Head is the actual Read followed by `makeNode`. `InternedShallowHeap.makeNode_noNewMu` moves the selected final complete Mu cell back to the read return. It is not enough to use Grows in this reverse direction. Append actual makeNode growth and issued extension to the chosen operation's suffix. The existing HeadIssuedHistory.head proof already derives exactly these constructor facts from the actual rebuilt equation and read effects.

## Deriving the rooted writer for the same operation

`InternedFreshOrdinaryStoredSubstitution.unfold` is definitionally the stored `execute` on the parent body with the self environment. `execute` is definitionally the exact encoded Fresh build. Retain both displayed equations if that helps consumers, but they are the SAME operation.

Derive body Available from the full parent Available proof. Derive Replacements for the self environment from that same parent proof. Then construct the rich Context exactly as SourceCurrentHeadIssuedHistory.unfold, lines 35-46, does: normality, input availability, profiles, free names and decoded depth all come from the actual ready operation-entry heap.

Apply `SourceCurrentCompletedBuildRootedWriters.build_writer_or_prior` to this exact completed encoded call and the target cell at operation return. The old-cell alternative contradicts operation-entry absence. The other arm is the requested same-event rooted Written. Nested publications in Depth, ordinary and reserved-body callbacks remain covered by the existing build producer. No assumed selected event or desired source ancestry is introduced.

The writer is rooted at the generated encode call. Its event can be a nested callback publication. It is not necessarily the parent Mu itself or a publication whose syntax equals the current native requester.

## Reuse and premise boundaries

- `SourceCurrentHeadIssuedHistory.unfold/read/head` supply actual issued paths. Their private collect/nodeEdges proofs are the closest reusable recursion template.
- `SourceEqualityOpenOrdinaryHead.unfold_complete` supplies actual completion, Keeps, semantic readiness and result availability without a closedness premise.
- `SourceEqualityExposureCosts.collect_verified/nodeEdges_verified` supply the actual tail effects, including arbitrary bounded stopping states.
- `SourceEqualityProjectionCosts.read_effects/head_effects` preserve the exact supported read/Head interval.
- `SourceCurrentStoredReconstructionPath.actual` gives an actual stored-call Path, but alone does not record that the call was visited by this Head.
- `NativeMuIssuedWriters.writers` supplies prior-or-written from a Path. It does not supply the generating operation label or original root.
- `CompletedBuildRootedWriters.build_writer_or_prior` supplies the generated root route from the actual encoded build. It should be used only after the actual operation has been recovered.
- `RecursiveHeadChainRows.Chain` is not the correct replacement for this induction. It requires a closed root and its `advance` constructor accepts Keeps. Such an advance does not identify the specific collector operation that installed an arbitrary selected record.

The prefix is an actual issued Path, not an inference from physical Grows, heap Keeps, numeric unfold history, or physical publication History. The suffix requires both Grows and issued extension; neither is an assumed original-program binding route. No native checked-memo history is reconstructed.

## Exact meaning of first introduction

Entry absence plus return presence identifies the actual unfold interval that first completes this immutable target cell in the Head schedule. All earlier intervals in its derived prefix lack that complete target, because prior record entries persist forward. The selected nested publication inside this interval is retained by one Rooted Written witness.

This does not prove operation-witness uniqueness, original-binding ancestry, a strict source/value decrease, or a renewal bound. It does not say that this operation alone returns the target as its value. The target may be a complete nested record installed during the operation's actual callbacks.

Only the stored-unfold Head/read/collect family is covered. Native `Body.maybeMu` construction is a distinct generation family and is not silently included.

## Verification scope

This report is a source-level interface audit. It contains no new checked theorem, public proof pair, example, or Lean run. Its proposed classifier remains unchecked until the implementer supplies a proof and final receipts. The earlier generation-gap report is unchanged.
