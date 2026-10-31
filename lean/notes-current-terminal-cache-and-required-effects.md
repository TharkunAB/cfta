# Actual terminal cache bounds and required-reader effects

Current checkpoint: 2026-10-31. Branch: `formalize`. The full goal remains active.

## Full objective

Prove the complete public system from its original admissible inputs.
Prove sound accepted outputs and the exact intended finite ordered prefix.
Include configured stops, sufficient original depth, and sufficient original resources.
Cover both Native and Prepared recursive workers.
Keep generic Mu, Union, and opaque branches in scope.
Include originalMap, source-domain, allocation order, and SCC correspondence.
Include signed and Set adapters, default and weighted getters, row history, and constructor-sensitive NodeEq.
Include node-count and size order, rank and unrank, Prefix, table and count APIs, and checkpoints.
Connect the public Haskell and host interfaces to the modeled operations.
Local current-state admissions do not replace this objective.

## Strongest current statement

In the Lean executable interned-core model, actual cached terminal operations preserve whole
`KnownOrdinary` from explicit current caller, cache, and input admissions.
Every successful raw terminal Core row satisfies the original common ordinary bound at the actual returned Caller heap.
Every returned `Some` cache satisfies the same property at that heap.
The theorem includes the raw fallback when no fold cache is recovered.
It derives the successful prefix and fold conditions internally.
It does not accept a future prefix observation, endpoint, Post, or result-bound supplier.

The actual built-in ordinary selected-edge producer supplies availability, closedness, ordinary domain,
strict parent-height descent, and the common cap for each child in the exact staged list consumed by traversal.
This producer still requires the literal selected stored-row admission and its current cache conditions.
It does not cover an arbitrary user-supplied `edgesOf` function.

The existing local semantic, source-refinement, resource, and operational output-prefix theorems remain checked.
These statements do not yet establish the complete public-system objective.

## Five checked modules

`SourceCurrentAllocatedNativeTerminalKnown.run_known` is the complete terminal preservation statement.
Its 206-line module uses the literal `CachedTerminalAdapter.run` result.
It derives the recorded source list, joined values equality, pending winner and sources,
and the fold reservation from the original local input conditions.
The reservation counts the original sources, including duplicates, plus one incoming step.
The actual singleton fold endpoint supplies its current Context, Post, Fits, remaining Room,
Stored, Known, and incoming availability internally.
The proof includes empty incoming values, prefix failures, fold failures, unsupported raw shapes,
incoming failure, absence, and successful raw rows.
Failures with no rows or cache do not imply preservation of an unexposed final Caller.
`KnownOrdinary` alone does not prove index validity or waiting-cache correctness.

`SourceCurrentAllocatedNativeIncomingCacheKnown.run_known` proves the corresponding actual incoming-adapter law.
Its 155-line module includes raw successful rows when the optional cache is `None`.
It handles the literal empty-raw adaptation that writes Empty handle 0.
Its public `read_values` theorem identifies the actual read Core values with the original values.
The adapter theorem requires current Context, realized pending values, incoming availability and closedness,
ordinary incoming domain and height, Known, Fits, Room, and Stored.
These remain current admissions.

`SourceSizedPrefixOrdinaryIncomingInputs.complete` proves the actual ordinary child producer.
Its 101-line module certifies `CachedOwn.prepare` and the exact
`staged.map (fun input => (input.1, input.2.1))` consumed by child traversal.
It derives each selected original child and its current bucket admission internally.
It also preserves Safe, Roots, realized pending values, waiting counts, flags, and Known after preparation.
Its source is a literal selected edge of the decoded stored parent.
The current Ready, parent lookup, row membership, arity, projection, and cache premises remain explicit.
A recursive hook runs after captured-edge processing.
That hook does not supply the incoming child in this theorem.

`SourceEqualityProjectionWorkerPhysical.require_effects` proves actual required-reader effects.
Its 210-line module handles every supplied fuel and Needed value.
It derives SemanticHeap, Covered, heap growth, and issued-node history at the actual reached state.
A done value is Available and closed.
Pending, unresolved, and exhausted results retain their own reached-state effects.
The proof starts from cold SemanticHeap, Covered, Available, and closed input gates.
It uses the checked actual forest effects internally.

`SourceEqualityProjectionWorkerPhysical.requireAll_effects` composes those effects for the actual list operation.
Its 122-line module performs the list induction internally.
It takes current available and closed input values.
It does not accept a future list-result certificate.
The required-reader laws remain useful secondary helper laws.
They do not close the current failed-check call route described below.

## Corrected current failed-check route

The current route starts at `SourcePruningEnumerationEnabledEmpty.check`.
It enters `SourceCurrentAllocatedConjunctionWorker.call` and `SourceCurrentConjunctionWorker.call`.
The actual exploration uses `SourceCurrentConjunctionRowsWorker.rows`.
Its tuple path uses `SourceCurrentConjunctionEquality.fold`, requirements, classes, and projections.
Its projections call `SourceEqualityProjectionWorker.forest`.

This route does not call `SourceEqualitySharedTargetWorker.step` or `SourceEqualityClassFoldWorker.pass`.
Those older helpers form a separate route.
Their raw `SourceRecursiveIntersectionNative.execute` call is also distinct from
`SourceEqualityNativeDemand.execute`, which intercepts some edge requests into an equality body.
The old native result can retain an outer `before` while its inner result carries another state.
No actual current-call preservation claim follows by substituting one of these programs for the other.

The wrong-route review is retained with zero new theorems.
Its original source cuts, cumulative scope concerns, and corrected complete metadata closure remain available.
A separate source-only task now follows the actual current rows and forest route.
No unchecked result from that task is part of this checkpoint.

## Largest remaining proof obligations

Derive the physical effects of the actual current rows, exploration, decision, and call on all outcomes.
Use the actual reached heap on failures.
Then derive the worker invariant for literal `resume D k` in both recursive workers.
Keep the original primitive work fuel `D` fixed as recursive fuel `k` decreases.
Generalize the reached metadata, Caller, queries, cache, and next decision inside that induction.
Derive current Post, admissions, memo identity, Fits, annotations, and reservation lineage internally.
Do not expose a future transition function or endpoint certificate as an original public input.

After a recursive hook, the next sibling uses the SAME captured cache and hook metadata.
It uses the hook's ACTUAL returned Caller and query state.
The existing `Packet.captured_post` can restore that captured packet if the actual Post is supplied.
The missing recursive producer must derive that Post and the next current admissions.
Known for a returned cache does not prove validity of the captured cache at the new Caller.
Each recorded output must be certified at its own recorded Caller.

Prepared preparation failures can retain an inner raw heap while the outer endpoint is `None`.
That option does not expose a hidden final Caller.
Keep terminal, alias, renewal, writer, Mu, Union, and opaque branches in the proof.
Local sufficient prefix and callback bounds do not establish that the fixed original `D` is sufficient everywhere.
The checked fixed-work output-prefix laws do not establish termination or coverage.
An exhausted or stuck branch mapped to `complete []` does not prove completeness.

Finally derive one sufficient original depth and resource allocation from the original admissible input.
An ordinary height cap is not a primitive work budget.
A finite guard carrier or SCS representation does not alone bound work, slots, or renewals.
A finite-model witness, supplied completed-query history, or fresh identifier counter does not close this gap.
The initial boundary completion theorem, default source/getter correspondence,
complete public ordered result contract, and Haskell correspondence remain open.

## Validation and provenance

All five modules pass focused default and strict checks with unchanged public admission intent.
The complete Audit passes at 4,801 jobs and 83,659 audited theorem dependencies.
Public readback passes at 1,321 checks and 159 printed public definitions.
All six new axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The complete prior 5,085,806-byte public readback remains an exact prefix.
The new suffix is 17,116 bytes and 246 lines. Root read that suffix in full.
Root read all 794 final new source lines and all proof repairs.

The 22 actual compiler commands include 14 passes and eight retained failures.
There are 108 exact input snapshots.
Each command verifies 4 GiB memory.max, 4 GiB memory.high, zero swap, and a five-minute cap before and after execution.
Seven smaller failed diagnostics were read in full.
The 114,992-byte first terminal diagnostic was read through all error headers and bounded goal prefixes.
Its complete raw log and exact read vectors are retained. No complete raw-read claim is made for that log.

All 597 previously protected sources remain exact.
All 835 native/Haskell inputs remain exact.
Of 4,796 old Lean sources, only Audit changes by five prepended imports.
The two Root OLD whole paths were named before acquisition: RequiredWorker100 and IncomingNode296.
The additional actual terminal-adapter definition is a named 52-line cut of its 635-line source.
Root has three OLD original paths and 448 unique OLD lines in this checkpoint.
The complete source-only owners retain their own ORIGINAL-path vectors and disclosed scope concerns.
Thirty-four complete owner closures pass independent Root metadata replay before the final public review.
The rejected incomplete legacy seal and its exact superseded metadata remain retained.

No native or Haskell product program ran in this checkpoint.
No executable Haskell defect, edit, or fix was established.
`FINDINGS.md` retains this statement and the complete earlier findings.
Formatting tools were skipped because the changes are proof and proof documentation only.
The full goal remains active.
