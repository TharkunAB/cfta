# Current class prefixes and finite conjunction reads

Source main is `a4f38cbb`, merged at `a140c37b`.
Its only change from the previous source checkpoint is CI scheduling.
The optimized interned core and all earlier proofs remain unchanged.

## Historical emptiness-body boundary

`Enumeration.provablyEmpty` now explores conjunction rows. It constructs no
native intersections inside that body. Its completed constructor reads,
equality accessors, row requirements, and Boolean fixed point need their
own operational graph.

`SourceCurrentEmptinessDecision.Decision.closed` still embeds the earlier
`SourceEmptinessDecision.Decision`. Its task rows construct native class
intersections. `SourceCurrentEmptinessMemo.Call.miss` requires that earlier
body. `SourceCurrentEqualityClassScan.Scan` then consumes those calls.
The existing proofs remain valid for these historical definitions.
They do not establish execution of the current conjunction body.

Conservative soundness cannot identify the two body algorithms. They can
return different Booleans and constructor heaps. A new source Decision and
completed memo Call must consume the conjunction graph before a general
current-source Scan completion claim is possible. Earlier sections that use
these Scan and Decision names retain this historical body boundary.

## Finite gates and seeded query

`SourceCurrentClassGateCompletion` constructs the ranked gate input directly
from SemanticReady, CostHeap, and input availability. The constructor uses
fields already retained by readiness. No new construction equation,
completed trace, or callback completion is supplied.

Both primary_class_complete and secondary_class_complete derive an actual
current class trace, its returned semantic/cost heap, retained original
values, and exact execution at every larger bound. The secondary theorem
includes the changed constrained-Mu endpoint. Predicates remain pure Boolean
functions in this component. Actual global predicate memo receipts remain
separate.

`SourceCurrentSeededQueryCompletion` derives the initial refused-class query
from an actual false secondary gate. That query still uses native intersection
in the current source. Its first seed is demanded last in the right fold.
Selected path support comes from the false gate at its actual returned heap.
Every projection and native request completes before the next operation.
The final query is closed and available. Physical readiness, stored costs,
normalized fields, and original values survive.

Native ranges remain explicit at actual reached projection and tail-fold
prefixes. They supply no completed recursive callback or future invariant.
Unrelated original siblings can remain open.

`SourceCurrentClassPrefixCompletion.finite` composes both gates and the
reached seeded query from the initial physical invariants. Its Prefix
constructors distinguish selected, skipped, and queried classes.
A selected class does not execute the secondary gate. A true secondary gate
does not construct a query. The result stops before provablyEmpty.
Its Ranges premise supplies only the reached seeded native checks.
This theorem covers one supplied class. It does not prove a whole lazy
partition, all global memo receipts, checked constraint allocation, or GHC
forcing order. It assumes no old Decision or Scan trace.

## Literal conjunction map

`SourceCurrentConjunctionMap` executes the existing finite signed-map alter
worker over source entries. Later occurrences replace earlier occurrences
at one identity key. last_winner derives exact overwrite behavior.
Ascending elems has strictly ordered keys and no repeated values.
Every returned record comes from an actual input occurrence.

FaithfulOn restricts key injectivity to the original finite input.
Under that condition, elems_exact derives literal ordered equality with the
older eraseDups/mergeSort sequence. The existing closed/nonempty KeyFaithful
law supplies the conjunction specialization. conjunction_accepts then derives
common-term acceptance. No iterator or desired sequence is supplied.

A kernel example shows why unrestricted sequence equality is false:
two different records at one key leave only the last record in the source
map. Node-equality deduplication can retain both. Key faithfulness is a
sufficient semantic condition, not a claim of the weakest possible condition.
Native Patricia storage, machine Int conversion, allocation capacity, and
physical resident/global-identity faithfulness remain bridges.

## Finite actual constructor reads

`SourceCurrentConjunctionCompletionReads` derives actual nodeEdges sequences
from closed available operands. It retains one edge list per occurrence and
the exact returned constructor heap. Every exposed row is resident and closed.

Its jobs list visits original child forests first, then paths within each
forest. Projections thread actual getPath calls through their returned heaps.
Finite completion derives closed available outputs, semantic readiness,
stored costs, annotation fields, and original heap retention.
The tuple endpoint starts at the exact heap returned by actual exposures.
No future heap or supplied native completion is needed.

read_accepted derives accepted accessor-edge exposure from actual guarded
acceptance. projection_included derives the selected-subtree language law
from an actual proper path read. These results can replace the older generic
exposure and projection premises at their actual operation sites.

The chosen finite read sequence is an eager mathematical graph. It is not
identified with the lazy Haskell tuple spine. Empty tuple lists can avoid
later source demands. No heap-equality result under reordered reads follows.
Equality accessor and combination interner effects remain separate.

## Next dynamic source graph

Thread these actual stages through one completed worklist:

1. Empty, open, budget, and stored-key guards in their source order.
2. Literal edge tuples, with tail operands before the original head.
3. Equality accessors and their right-fold combination, with allocation effects.
4. Child columns and class-path projection jobs in their original order.
5. Identity-map canonicalization and exact stored rows.
6. Pending requirements, admission decrement, and finite grow/canAccept.

The earlier pure finite worklist and fixed-point proofs remain reusable.
Their arbitrary edge/project supplier must be connected to actual returned
reads. Do not assume one effect-free supplier across heap growth.
Then define the current Decision, completed emptiness memo Call, and Scan.
Connect the resulting successful scan to the executable physical class pass.

General constrained completion, runtime publication, native allocation,
concrete containers, and all other full-library targets remain open.
Keep every separate Sized contract and the older constructor/equality work.

## Validation

The full pinned audit passes 2,225 jobs and checks 54,843 theorem dependencies.
Only permitted foundations and the old unused-input warning occur.
Forty public axiom probes and 23 kernel examples pass.
All previous non-Audit Lean files retain identical bytes. Audit gains three
imports. Five new modules and this increment's two notes are added.

The CI-only source refresh changes no Haskell code. The previous strict Nix
build, 755 examples plus golden, Fourmolu, and Cabal-gild checks remain valid.
They were not repeated for this proof-only increment.
Evidence uses `/tmp/mcfta-general-scan-*`, `/tmp/mcfta-current-class-*`,
`/tmp/mcfta-seeded-query-*`, `/tmp/mcfta-conjunction-map-*`, and
`/tmp/mcfta-conjunction-completion-reads-*`.
