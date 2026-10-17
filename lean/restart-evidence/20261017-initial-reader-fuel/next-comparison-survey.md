# Initial computable comparison fuel

Survey time: 2026-10-17T08:58:17+02:00. Read-only source audit. The paired header file records exact lines and SHA-256 hashes for 19 production sources. No production code or theorem changed.

## Current closed results

`SourceCurrentAllocatedReaderNumeric.collect_complete` derives sufficient `collectFuel(N,E,B,pending.length)` from initial semantic/coverage/depth facts, available closed pending values, and causal `Stored B`. It constructs its own actual run and exact stable full heap. `SourceCurrentAllocatedRowReadNumeric.complete` now constructs a stable actual `nodeEdges(readFuel N E B)` return with semantic effects, resident closed rows, stored mass, and both absolute supplies. These results include full repaired Mu unfolding, old winners, union closure, and current heaps. Initial reader fuel is closed.

`SourceMergedComparisonCompletion.check_complete` constructs a stable comparison result, but its fuel is existential. `SourceMergedComparisonMass.check_bound` transfers resources through a supplied successful `check clear fuel ...`; its result is `Resources(comparisonBound fuel B)`. It does not compute sufficient fuel. `SourceMergedSelectionMass.select_complete` constructs success but still reports `selectionBound fuel inputs.length B` at the existential successful fuel. Combining these alone does not give an initial numeric forecast.

## Exact demanded order

1. `MergedFreshOrdinaryComparison.check` first handles empty narrow, empty wide, identical references, failed identity lookup, and an ancestor-pair hit. A fresh nontrivial pair consumes one comparison fuel unit. It reads the narrow operand at the current comparison fuel, then enters `allRows` with the recursive callback at fuel minus one and the new pair prepended to `above`.
2. `allRows` processes narrow rows in order. Each row performs a new wide read at the same local reader fuel. It then invokes `MergedSourceComparison.anyCover`. A false cover ends the comparison at its actual returned heap. A true cover continues with the original narrow suffix at that heap.
3. `anyCover` scans wide candidates in order. Its header test requires equal symbols, equal child lengths, and `clear wide.constraint = true`. A rejected header has no effect. An accepted header invokes `children`. A false child conjunction retains its heap and tries the next wide row; true returns immediately.
4. `children` follows ordered zip conjunction and stops on either empty list or the first false callback. Every demanded recursive comparison receives the previous callback's complete heap. The Boolean `clear` test does not need an oracle to bound control flow.

These structural sibling loops do not decrement comparison fuel. A sufficient `check` fuel must bound recursive depth and every reader fuel; it is not the sum of all callback instructions.

## Existing termination measure and remaining numeric gap

`check_eventually` uses the lexicographic measure

`(unfinished Mu counts by body degree, remainingPairs current.nodes.next above).`

The first vector is `InternedFreshMuUnfoldBudget.count`, which counts actual unsettled canonical records in the issued range. `unfold_progress` proves strict vector decrease or complete heap equality. Settlement replays through growth. A changing reader prefix therefore consumes unfinished degree progress. If the entire preceding prefix is unchanged, `remaining_cons_lt` consumes the fresh ancestor pair in the identical heap. `SourceMergedComparisonBudget` already transports that progress through successful children, covers, rows, and comparisons.

This is a termination proof, not an initial numeric bound on all reached counters. Fresh unfolding can add lower-degree Mu and ordinary identities. The initial fixed Cartesian pair universe therefore does not contain every later identity merely from the current source proof. The source-built `reader-control-kernels.actual_mu_control` independently demonstrates real growth of both supplies. This is evidence against assuming heap equality; it is not a counterexample to every possible formula based on initial counters.

`SourceMergedComparisonStages` combines stable local bounds at actual returned heaps. Its `CompleteCallback` is discharged internally by smaller lexicographic calls. It is not an initial computable callback budget.

## Proposed smallest proof sequence

1. Add an exact comparison/stage graph, or a heap-history projection from each supplied successful comparison. Flatten each demanded repaired reader into its actual successful unfold events. Preserve the literal narrow-read, wide-read, failed-cover, child, and suffix order. `ReaderConsumed.extract` supplies exact collector graphs; the top-level direct Mu probe in `nodeEdges` must also be recorded. Keep heap-equal unfold events as stutters and remove them only from the strict progress path.
2. Prove an initial absolute heap envelope for this projected history. Carry semantic/depth facts, the fixed initial Mu-degree bound, causal stored mass, and both supplies. `InternedValueMassBinderDepth.stored_bounded` fixes the degree dimension from initial `B`. Every changing unfold strictly decreases the unfinished vector, whose coordinates are at most the current node supply. `ProjectionResources.unfold_bound` controls its next store and supplies, and `ReaderControl.g` is a monotone strict numeric envelope. `HeightOrderControlled.Path.final_le` can then bound all event heaps independently of supplied comparison fuel. The measure may use proof-only `Settled`; the numeric majorant itself remains computable.
3. With a proved absolute ceiling `Q`, derive every actual identity below `Q` using `identity_closed`. Along any recursive path, each fresh pair is new in the persistent ancestor list. Thus at most `Q²` fresh calls occur on that path, even though identities were allocated later. Prove uniform intermediate reader sufficiency from `RowReadNumeric.readFuel Q Q Q`; monotonicity in the two counters follows from the fixed-mass `HeightOrderControlled.majorant_mono`. Keep causal `Stored Q` at each exact intermediate heap.
4. Replay the complete ordered comparison graph at a pure sufficient fuel. A conservative candidate is `1 + Q² + readFuel Q Q Q`. This formula is proposed, not proved. Each child loses one fuel unit, all sibling scans retain the local fuel, and stable row-read replay identifies the same full intermediate heaps. Existing `check_stable` and `successful_results_eq` identify exact returns after replay. Then call `check_bound` at this initial sufficient fuel, and lift the resulting bound through the actual selection loops.

A suitable final API is `check_initial clear above wide narrow before B semantic stored wideAvailable narrowAvailable wideClosed narrowClosed`: it constructs `answer, after`, a successful equation at a pure `comparisonFuel before.nodes.next before.edges.next B`, stable larger-fuel replay, and the existing resource envelope. It must not take a successful comparison, future counter bound, callback resource law, or final pair universe as an input. A transfer theorem over a supplied successful graph is a useful first component, but is not this initial endpoint.

## Selected open-root scope and next integration

The comparison endpoints operate on closed available operands. This does not require the whole captured forest closed. `SourceEqualityProjectionPathDomain.ForestClosed` follows only the selected ordinary route; `forest_effects` derives a closed available selected result. An unrelated ordinary sibling can stay open. A recursive Mu/union head on a nonempty selected route retains its existing whole-value closure boundary. Do not strengthen this source domain to `ClosedValues originals`.

The next constructive check should build an ordinary root with an unrelated open sibling and a selected closed productive Mu/union endpoint. Construct both selected operands, then comparison and selection at the proposed initial fuel. Derive the causal mass after projection, prove the actual fresh unfold changes supplies, and replay at larger fuel with the exact same complete heap. Full Operand mass transfer still also needs the actual projection and Merge ordering. No new Haskell behavior defect or end-to-end Target/Force completion is established by this survey.
