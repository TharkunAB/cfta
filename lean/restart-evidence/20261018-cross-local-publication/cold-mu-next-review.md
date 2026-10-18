# Intrinsic semantics and the next proof target

Reviewed 2026-10-18 22:33 CEST. Source pins are in cold-mu-source-pins.json.

MergedFreshOrdinaryGraph.successors runs unfold at one supplied reader and discards the returned heap. It then uses that same reader for the next successor. The checked cold witness shows why initial availability cannot provide epsilon-closed WarmSupport for this graph. It does not show that every cold graph gives incorrect language.

The intended traversal target is SourceCurrentAllocatedPartialMemoSound.NodeLaw. It uses InternedGuardedLanguage.meaning. That interpretation reads actual stored bodies, complete guards and ordered children. Its positive Mu binders use a least language. It has no reader parameter, interning effect or probe-defined meaning. A global fixed-reader Directed instance is therefore a sufficient proof route, not a necessary part of the target statement.

The existing SourceFreshOrdinaryColdGuardedExact.graph_exact requires replayed rows, resident rows, covered rows and supported values at its graph reader. trace_graph_exact derives the final graph correspondence from an actual growing shared trace. These hypotheses must remain explicit. The cold witness cannot refute the final supported-graph theorem and does not justify applying it to the original cold reader.

A direct alternative is a chronological intrinsic-language substitution contract for each actual published payload, parametric in free-reference languages and supplied local replacements. The publication step must compare the actual stored body with its ordinary probe after root filtering. It must account for a retained earlier writer and smart unused cleanup. Such a contract would target guarded semantics directly. The present root profile/Empty contracts do not establish it. Exact first-writer provenance remains necessary even if physical equality is attempted first.

A distinct initial assumption can already be removed. SourceCurrentConstrainedCapGuardExecution.closed_heap produces exactly SourceCurrentConstrainedCapGuardHeap.Heap Plain for every actual closed source stopping heap. SourceCurrentConstrainedCapGeneratedQueryResources.Frame.initial consumes that same predicate. This discharges that initial guard heap for source-built empty-native-cache entries. It does not discharge arbitrary warm outer memo Sound, numeric Room, an observed successful traversal, or general recursive completion. It is separate from the remaining parametric stored-substitution question.

The next bounded mathematical target can be exact equality fusion under equal resolved lexical values, or a chronological intrinsic-language substitution law. Both must prove the binder publication step. An unrestricted up-to-transitive closure rule, a backward reader transport, and a claim that every epsilon successor remains originally available are invalid replacements for that step.
