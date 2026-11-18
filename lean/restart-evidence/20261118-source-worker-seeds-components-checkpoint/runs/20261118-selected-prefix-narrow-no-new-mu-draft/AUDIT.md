# Selected-prefix native narrowing cut

The current normal source is the pushed Source57 tree. The selected module
pins are exact current bytes. The packet does not change that tree.

The actual runtime chain is SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
lines 68–76: after the literal old-handle lookup it calls Action.prepareWithNarrow,
then advances the caller to prepared.state. The configured runPrefix supplies
OuterNarrow.narrow. The original six prefix fuels remain unchanged upstream.
Only nativeFuel and representativeFuel are inputs to this local action cut.

Action.prepareWithNarrow at SourcePruningEnumerationAction.lean:17 propagates a
native failure unchanged. On success it computes reject, no action, pure unit,
or representative/setValue. Every branch retains the SAME nextHeap. The current
candidate covers that native endpoint before any computed enum action runs.

OuterNarrow.narrow at SourcePruningOuterNarrow.lean:11 retains Mu inputs and
metadata.types members without a native effect. Its other cases call narrowAt
at the original holeKey and native fuel. SourcePruningNativeView.narrowAt at
line 33 calls the repaired edge reader, filters the actual row list, and makes
one ordinary node. Every failed reader outcome retains its exact returned heap.

The required exposure producer already exists:
MergedFreshOrdinaryExposure.nodeEdges_verified at line 141 returns a Verified
receipt under Facts, Prepared and Available. Its unchanged field covers done,
unresolved, pending and exhausted outcomes. It does not require closedness or a
completion bound. InternedShallowHeap.makeNode_noNewMu at line 42 is unconditional.
These two checked laws supply the local NoNewMu algebra; no new induction engine
is needed. Ownership.current_build_prepared at line 420 derives Prepared from
the original accepted build. Prepared.preserve at MergedPhysicalWarmup.lean:24
transports it using the source NoNewMu field of past Seeds.

The literal selected-prefix advance uses advancePhysical with the original
operations and source caller advance with its original fourth and merge memos.
SourceCurrentAllocatedQueryMemo.advance_tables at line 111 already exposes the
native nodes, edges and domain-cache equalities. They also hold definitionally
at this exact advance. All Returned clauses of Seeds mention those unchanged
tables. Its source NoNewMu clause composes with the actual narrowing receipt.

## The separate emptyAt operation

SourcePruningNativeView.emptyAt at line 46 exempts Mu and otherwise narrows once,
then reads the narrowed result. A whole-tree word search found no runtime call
of this definition outside that module. Its occurrences there are the definition,
its completion theorem, proof reduction and Mu theorem. SourceDenotationPlain
also uses the spelling for a local proof variable; that is unrelated.
Do not treat emptyAt as the actual SharedEnabledEmpty worker call. Source57's
separate Gate/Skip theorem concerns that actual shared worker.

A generic emptyAt NoNewMu law is also supported by existing local algebra, but
is not implemented in this candidate. At a completed narrowAt read, the
Verified.edges receipt makes the filtered rows resident at the SAME middle
heap. InternedNestedFacts.node_verified then derives actual constructor Facts
and output availability. The first NoNewMu receipt transports Prepared. A
second nodeEdges_verified covers the literal second read at the SAME fuel and
heap, including its failures. This route needs no future native inhabitance or
empty-answer correctness assumption. It must retain all actual endpoints; a
syntactic empty result is not a finite-language inhabitance certificate.

## Exact remaining integration

The public FIRST is
SourcePruningEnumerationAction.original_source_prepare_endpoint_preserves_seeds.
Its only semantic preservation input is past Seeds at the actual input. It
accepts original source/build, actual current Facts and a literal old-handle
lookup. It derives the current Prepared and Available facts internally. The
four outputs refer to one explicit native endpoint: local NoNewMu, native node
and edge tables, domain cache, and Seeds. No existential witness is spliced.

The full worker still needs a joint phase induction that produces those past
facts at this same cut. It must refine every ordered dispatch/fold query input,
retain the last query before a stop, and preserve Seeds through the other
interposed effects. The checked resource admitted_request_plans law can derive
both Through plans from genuine Ready/Fits/Admits and closed Available operands.
It is not a future plan supplier. This local candidate does not discharge those
worker-wide resource admissions or historical finite-model obligations.

The full target stays ONE finite accepted completion of the SAME original
emitted partial root under ONE compatible assignment for all historical
obligations on the same causal branch. All original work, recursive and primitive
fuels, source, root, noStop and outputs before later stops remain in scope.
Native inhabitance, guard truth, Type/Marker class compatibility and Haskell
correspondence remain open. No reachable Haskell defect is claimed.
