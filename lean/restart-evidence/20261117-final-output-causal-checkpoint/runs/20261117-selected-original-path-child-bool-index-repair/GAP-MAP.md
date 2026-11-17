# Original path descent at one actual selected child

Status: **UNCOMPILED**. The public theorem is a proof candidate. The separate control-cut header is **OPEN**. The reported published base is `51da59b3`. `SOURCE-PINS.json` records the exact source files read for this packet.

The theorem `selected_original_path_child_invocation` takes an original obligation at its actual list occurrence and a path `position :: suffix` in that obligation. It takes the same literal successful own preparation and actual selected complete trace. It derives the staged child at `position`. It does not ask the caller to supply that child lookup.

The theorem retains the descendant obligation at an exact index. That index is the number of retained descents in the original obligation prefix. This preserves duplicate obligations and their original raw variables. It retains the valid suffix trie, the actual child invocation with its original continuation, both output indices, the completed fragment prefix, the actual remaining tuple trace, and the same selected return. It derives alias transport from that child's return through the remaining tuple and the selected finish.

## Existing source facts used

- [EqualityTrie.lean:133](../../MicroCFTA/EqualityTrie.lean#L133), `descend_exact`, identifies the exact suffix. `descend_valid` at line 432 preserves validity. `descendScs` at line 623 maps and filters obligations. Existing `descendScs_exact` is a membership law. It does not select the original duplicate occurrence. The new private list lemma supplies that index.
- [EnumerationState.lean:394](../../MicroCFTA/EnumerationState.lean#L394), `arityAllows_correct`, derives `position < edge.children.length` from the literal successful preparation and original path. No future roots or child availability premise is used.
- [SourcePruningEnumerationCachedOwn.lean:27](../../MicroCFTA/SourcePruningEnumerationCachedOwn.lean#L27), `prepare`, creates the staged list from the actual `edge.children.zipIdx`. The child bucket is `descendScs position parentBucket ++ descendScs position own`. The original descendant belongs to the first segment.
- [SourcePruningEnumerationSelectedStagedChildInvocation.lean:66](../../MicroCFTA/SourcePruningEnumerationSelectedStagedChildInvocation.lean#L66), `selected_staged_child_invocation`, extracts the child and remaining tuple from the same trace. The candidate does not construct a separate output witness.
- [SourcePruningEnumerationInvocationRawAliasGrowth.lean:323](../../MicroCFTA/SourcePruningEnumerationInvocationRawAliasGrowth.lean#L323), `children_done_sameClass_forward`, transports aliases through that exact remaining tuple. `OwnAliasForest.finish_forest` covers the same selected finish.

## Exact remaining control boundary

A completed child does not always execute a deeper selected row. [SharedInvocationTrace:95](../../MicroCFTA/SourcePruningEnumerationSharedInvocationTrace.lean#L95) records a literal shallow dispatch. `guarded_else` at line 124 and `eager_fallback` at line 133 can reach that case. Only `eager_ordinary` at line 142 records the complete scan prefix and the same producing selected row.

`NEXT-CONTROL-CUT-OPEN.lean.txt` records the exact next structural extraction. The same completed child is either a literal successful dispatch, or the actual producing selected row with its scan prefix and output offset. It is not a theorem in the candidate module. It adds no output, history, or model supplier.

For the selected-row alternative, another application of the candidate can follow the next suffix index in the same actual invocation derivation. For the shallow alternative, the unprocessed suffix remains an obligation at the authentic child input. The trace does not prove that the suffix was visited.

[ShallowChild.prepareChild:28](../../MicroCFTA/SourcePruningEnumerationShallowChild.lean#L28) stores the full bucket for an ordinary node. Its Mu and Union branches at line 33 allocate a hole without that bucket update. The actual `prepareChild_complete` statement at lines 55–61 reports the same distinction. Thus an unrestricted trace alone cannot imply that every nonterminal input bucket is retained in the actual pending store. This is an API boundary. This packet does not construct an accepted-source counterexample or claim an implementation defect.

## Whole-goal boundary

This theorem is parametric in every original path and suffix, policy, output type, stop reason, and five primitive fuels. It does not prove that every path is executed. It proves alias transport to the same selected-return cache. Transport to the final emitted worker cache must use the authentic captured finalization and recursive restart continuation. A shallow or unfinished descent must retain its historical obligation in the joint completion proof, or use a source-derived exclusion or discharge. No future assignment, roots, model, closure, semantic law, or alias supplier is an input here.

The full original same-root, same-branch finite accepted completion and one compatible assignment remain open. This packet does not reduce that objective to immediate one-position paths.
