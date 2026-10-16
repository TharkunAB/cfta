# Next cumulative Target profile and reservation contracts

Reviewed 2026-10-16 19:20 CEST. This is a bounded read-only plan. The proposed contracts below are not new theorems.

## Current local foundation

`SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.lean:87` and `:102` now derive the actual `makeEdge` and `makeNode` profiles. They include coherent cache hits. `normalized_rows` at line 61 retains complete edge profiles and bounds the canonical surviving length by the literal input length. `children_of_all₂` and `rows_of_all₂` at lines 69 and 78 collect positional result profiles and exact lengths. These are local constructor laws. They do not derive the profiles of recursive calls.

`NativeProfile` computes an input envelope and retains original row multiplicity. `NativeBudget` bounds all actual finite native prefixes from original inputs. The new `ProfileBudget.node_budget_le` derives a uniform reservation from operand row/arity/height bounds. This is the necessary connection between a returned profile and the next native-query budget. It does not derive a cumulative Target bound.

The current native output producer is being developed separately. Its rejected edge needs arity `max A 1`, because the literal sentinel has one Empty child. A returned node or edge cannot receive a profile solely from language exactness or the older domain/height certificate. Warm tables need a causal output-profile certificate for the exact stored owner.

## Projection: first bounded producer target

Current `Projection.project`, `rows`, and `forest` are at lines 149, 157, and 165 of `SourceCurrentAllocatedFiniteOrdinaryProjection.lean`. They retain domain and actual physical effects. They do not bound the returned profile, constructor requests, or returned height.

The literal source graphs matter. `SourceEqualityProjectionGraph.Project.ordinary` recursively projects one selected child per source row, then calls `Union` on the returned list. A missing child makes no recursive call. `SourceEqualityProjectionUnion.Union.node` reads every operand row list in order, concatenates them, and calls `makeNode` once. `Forest []` has this union branch. `Forest (index :: path)` first selects one forest entry and then projects only `path`. Signed missing positions return Empty.

The smallest useful additive theorem should strengthen the same actual `Forest` return with:

- a computed uniform output row limit from the original forest profile, its length, and path length;
- the original arity limit;
- a height bound by the maximum original forest height;
- node/edge constructor-request bounds and the corresponding actual counter bounds.

An ordinary union of `k` profiled nodes has at most `k * R` literal rows before normalization. Its descendants retain the common child profile. It cannot use the old row limit `R` without a separate bound on `k`. For projection, a conservative path recurrence can use `max 1 R` and multiply once per ordinary projection level. The forest-root union must include forest length separately. Prove this recurrence against the literal graph before naming it a result bound.

For a simple first reservation bound, count ordinary-node occurrences in the complete original record tree, including repetitions in different rows. Each selected recursive projection visits a corresponding original occurrence. Each nonempty ordinary projection performs at most one final `makeNode` request. Ordinary reads have unchanged heaps by `Projection.read_domain` and `readAll_domain` at lines 24 and 40. `Forest []` adds at most one node request. No raw `makeEdge` appears in this finite ordinary projection graph. A conservative candidate bound is one plus the sum of original node occurrences. This requires a graph induction and primitive request accounting; it is not yet proved. No future returned forest or completed child callback is needed as a public input.

## Required paths: profile retention is stronger than current NodeNarrow

`SourceCurrentAllocatedFiniteOrdinaryRequired.lean:28–33` defines `NodeNarrow` and `EdgeNarrow` with domain and height only. `node`, `children`, `rows`, and `requireAll_done` at lines 264, 271, 278, and 286 do not imply row or arity bounds.

A new actual-graph profile induction should preserve the original uniform `R,A` exactly. `RequireChildren.length` preserves positions. A rejected row is omitted before child recursion. A kept row calls the literal child graph and reconstructs the same symbol/full guard with `makeEdge`. `RequireRows` returns an ordered selected source sublist with corresponding rebuilt rows. `makeNode` then filters and canonicalizes those rows. These are the inputs needed by the new constructor laws.

The proposed public endpoint is initial SemanticReady, resident/available original profile, and an actual supplied required graph, returning the same actual output profile and physical effects. Derive profile results for its smaller calls internally. Then compose with existing constructive completion for a finite endpoint. Do not add supplied child completion or a final profile premise.

A static reservation bound can count all ordinary node and edge occurrences in the original record tree. The graph visits each selected occurrence at most once per call. Identity and Empty branches add no Work. A retained row adds at most one edge request, and a visited ordinary node adds at most one node request. The bound can count unselected and rejected occurrences conservatively. This must be proved from the actual graph rather than defined as a final counter difference. Generalize to actual prefixes if the later capacity argument needs in-call supply bounds.

## Merge: retained columns can enlarge descendant row profiles

Current `Merge.allocated`, `finite`, and checked `merge` are at lines 103, 116, and 128. `MergeWorker.verified` and `finite` expose the same physical graph and stable literal worker return. They establish domain, physical effects, and memo retention. They do not establish an output row profile or input-only constructor total. `MergeCache.Stored` is only conditional domain preservation.

The literal `SourceCurrentAllocatedMergeGraph` is the correct producer graph. `small` maps recursive requests over the actual children and rebuilds their row. Groups of size at most four retain one result row per input row. A larger group builds each child column, then one Top row. The Top-field allocation changes equality state separately from the two constructor heaps. The final node consumes the flattened group results. The finite ordinary branch excludes the explicit recursive-boundary `makeUnion` path through actual domain inversion.

Top-level grouping cannot add rows. It is still incorrect to conclude that every descendant keeps the original row limit `R`: a retained column can union children from a group of up to `R` rows. Concatenating their child row sets can produce a recursive input with row limit `R * R`. Its height is bounded by the original child height. This needs the actual `ordinaryUnion` readback and height law, not a language argument.

A conservative proposed merge envelope can therefore recurse on original height:

```text
M(R,0) = R
M(R,H+1) = max R (M(R*R,H))
```

This is a proposal, not a checked theorem. It covers both small recursive children and the enlarged column input only after proving monotonicity in `R`, exact column/member counts, and strict child-height descent. Arity can remain `A` for this merge graph: each large-group output uses the first row's literal column count, and ordinary union does not add child positions. Do not transfer the native sentinel's one-child arity issue into a merge claim without an actual sentinel constructor.

The warm merge invariant must quantify the producer bound over the actual captured original. On a hit, use `hit_original` to recover that original. On a miss, derive the candidate profile from the actual memo-aware body. If recursive work has already completed the same key, `remember` keeps that winner. Read its stored certificate rather than assigning the losing candidate's bound to it. Existing keep-first/domain helpers provide this lifecycle pattern, but not the profile conclusion.

The reservation proof needs the same height/column recurrence plus actual comparison/selection effects. Prove that source structural selection over this domain issues no constructor Work if that fact is used. Do not infer zero allocation from selection only returning original inputs. Group iteration and sequential allocation order remain the explicit graph-to-host boundary. Count equality-field allocations separately if a later resource theorem needs them.

## Cumulative Target boundary and next API

`SourceCurrentAllocatedTargetGraph.Fold.cons` runs the head operand, then its recursive tail, then the checked native request. The nil branch computes the separately captured seed operand. Thus a nonempty path list evaluates the remaining head operands before its first seed operand, as specified by this rotated right fold. Preserve this order and every returned full state, native table, merge memo, fourth memo, and target slot table.

The next cumulative theorem should use a finite path list, an initial uniform forest profile/height bound, initial physical and causal output-cache invariants, and computed initial supply headroom. It should construct its own graph and receipts, derive every intermediate operand profile, and spend the same budget at each actual prefix. The native sub-budget then follows from `ProfileBudget.node_budget_le`. Retained result profiles supply the next generated query's inputs. No reached TargetCapacity or future result profile should remain in the final public premise.

The smallest first implementation is the Projection producer above, followed by Required profile/count preservation and the warm memo-aware Merge producer. Then derive one complete Operand profile/reservation and lift it through the literal Target fold. Starting with a whole Target formula would currently conceal the missing projection and merge producer facts.

This is not yet initial-only capacity for full reduction. Shared edits, class right folds, local/parent passes, and the outer recursion also need visit counts and causal returned profiles. Domain and height alone do not bound branching, row counts, or the number of constructor reservations. Mu, reference, explicit union, arbitrary fixed points, equality-interner and host allocation, concurrent losing candidates, GHC demand/publication, and frontend correspondence remain separate obligations.
