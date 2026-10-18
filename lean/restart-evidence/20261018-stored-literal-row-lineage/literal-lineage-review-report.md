# Independent review of stored literal-row lineage

The review concerns original stored-row occurrence through actual repaired substitution. No material proof issue was found. It does not run Lean or add a public declaration. The final manifest records the reviewed production hashes and reused receipts.

## Induction and source occurrence

The induction measure is `sizeOf` the original input Value. The union case recurses on an original indexed member. The Mu case recurses on the original stored body. The generated raw value, normalized output, or selected cache winner is not the induction measure.

An ordinary source occurrence retains its exact original node and row index. Union and Mu constructors retain the path to that source node. Equal rows or duplicate union members need not have unique source indices. Matching a physical row identity alone is not an occurrence path.

The ordinary case uses `StoredSubstitutionOrigins.NodeRows`. It gives an indexed original row, the exact full symbol and guard, unchanged arity, actual ordered child Calls, and prefix and suffix heaps. Those child calls use the lexical environment at that source node. After a Mu descent this can be a shadowed environment, rather than the unchanged initial map.

The union case uses literal root-row normalization and indexed actual member Calls. The strict-size witness is about the original member. Dead filtering, duplicate removal, and canonical reordering permit a forward source witness; they do not justify a converse saying every original row survives.

`StoredLiteralCalls.execute` derives semantic output, physical growth, issued-name extension, result availability, and replacement preservation from an actual completed stored call and its initial support. `indexed` derives the actual selected member's semantic entry from its completed prefix. `union_row` combines these producers with literal union normalization. It retains the original member and output indices, literal Row of that actual member output, prefix and suffix Calls, and growth from the selected call's return into the actual union return. No future semantic read graph or supplied per-member invariant is an input.

The closed shortcut returns the exact original value and heap. Its literal root rows yield original occurrences through root unions without Mu unfolding. The appropriate result is an identity branch. No actual child execution took place in this shortcut.

## Lexical replacement branch

An arbitrary replacement environment can introduce an entire ordinary node at a reference source. The general theorem must retain a separate replacement-origin branch. It cannot identify that row with an ordinary row of the original reference input.

The native local map is a sparse shadow: it overrides the original stored self name with the actual callback reference, then retains the outer map elsewhere. A returned replacement-origin witness from the strict-body induction is transported through this shadow. If its name is the local self name, the replacement is a bare reference and has no literal Row. Otherwise its lookup is exactly an outer-environment lookup. This removes the local override case without assuming all names are distinct.

A RefOnly environment maps every supplied replacement to a bare reference. Sparse shadow preserves RefOnly when the local value is the actual bare ordinary reference. Missing bindings also fall back to bare references. Alias patterns do not obstruct the forward occurrence theorem: they can merge or discard rows, but cannot introduce a literal row from a bare reference. No global name injectivity or extra fresh-name premise is needed for this property.

## Pure lineage and anchor contracts

`StoredLiteralRowLineage.RowAt` retains indexed original ordinary rows and indexed original union-member descent. Its Mu step follows the original stored body. `ReferenceAt` retains the same original structural path, with an explicit inequality that prevents a bound self name from being reported as an external replacement.

`Origin` distinguishes closed identity, ordinary child Calls, union-member descent, sparse-shadow Mu-body descent, and an actual external replacement lookup with a literal replacement Row. `anchor` preserves exact symbol, full guard, and arity in its source-row branch. The other branch retains the exact external source-reference path and initial-environment replacement lookup. Its Mu elimination correctly rejects the local-reference row case and preserves the original external map for all other names.

`source_row` removes the replacement branch with an explicit pure condition that supplied replacements have no selected literal row. Bare references and Empty satisfy this condition. A no-row condition on arbitrary replacement values must not be omitted when the theorem is used outside those cases.

The pure `Origin.mu` constructor retains a lexical shadow choice through its `currentDepth` parameter. It does not store a complete chronological parent callback equation or its heaps. The actual execution producer must derive that choice from its real callback, but the resulting Origin is a row-lineage receipt rather than a complete binder execution graph. Its ordinary Calls are actual equations at the captured child interval.

`RowAt.child_smaller` proves that every child of the anchored original row has smaller structural size than the original input Value. Its ordinary case uses the exact source row index and child membership. Union and Mu cases add their original structural ancestors. This is a property of the original row's children. It does not bound rebuilt output children or actual later requests.

## Actual Mu body and chronological reader

The nested Mu step retains the original input body and exact original self name. The actual selected cache winner can have a different body. Current full probes and the actual winning record are read back through coherent residency. Correctness must be derived for that exact winner.

The actual completed callback provides post-Depth semantic context, source-body availability, replacement availability, and physical growth with issued-name extension. A later publication history is used only after transporting the complete winner forward to that reader. It does not provide an earlier publication history by reverse inference.

A literal output Row excludes the retained physical Mu and Empty cleanup cases. Literal filtering and bare-self erasure preserve the exact ordinary rows of the raw callback result without unfolding opaque Mu atoms. This is stronger than an epsilon Origin and permits strict original-body recursion.

The new Mu literal-row helper accepts a literal Row rather than only `nodeEdges` membership. A union member call can return a mixed union containing an ordinary row. That result has a literal Row although its immediate `nodeEdges` list is empty.

`StoredMuLiteralRows.mu` implements that literal-row case. It derives an exact Depth callback and repaired execute of the original stored body under the sparse local override. It supplies SemanticHeap, original-body availability, and Replacements at the actual post-Depth entry. Raw-call and filter-tail growth are explicit. Correctness of the actual selected current-probe winner excludes the retained-Mu and Empty cleanup branches. The actual winning record grows forward to the reader before `history_unused` is used. The final literal raw Row follows from `PublicationFilterSource.filtered_row` and does not unfold a retained Mu atom.

## Actual execution and constructed completion

`StoredLiteralRowLineage.execute_row` derives Origin from an actual completed stored execution, initial SemanticHeap, original availability, replacements, a later reader publication history, forward growth, and a literal output Row. It does not receive Origin, a source-row comparison, or a smaller-source result as a premise.

The closed case derives exact source identity from the actual closed shortcut. The reference case keeps an actual replacement lookup; a missing lookup is a bare reference and cannot have a literal Row. The ordinary case first proves the actual makeNode result is ordinary, then converts its literal Row to an immediate physical index and uses the existing indexed source-row call producer.

The union case derives the selected member's semantic entry from its actual completed prefix. Its strict-source induction uses the original member, its actual call, and selected-return-to-parent-return-to-reader growth. The Mu case uses the original stored body, its actual post-Depth semantic entry, sparse lexical replacements, and raw-return-to-parent-return-to-reader growth. Neither case recurses on a generated result. No historical publication history is inferred backwards.

`complete` constructs the actual successful execution from initial SemanticHeap, Covered, Available, and Replacements. The independent source history producer supplies its local History segment. An explicit initial global History composes forward to the final reader, where execute_row derives Origin for every literal output row. This is an initial-data producer, rather than a wrapper that assumes the desired output lineage or future completion.

## Existing boundaries and next handoff

No near-identical generic original-row producer was found. `StoredNodeExpansion` covers ordinary roots. `RecursiveHeadChainRows` retains actual chronological terminal rows and warm calls, but those terminal rows can be generated values. `RecursiveHeadRowOrigins.BodyRows` leaves its nested stored-Mu case open. The new theorem supplies original-row provenance for completed stored reconstruction's literal rows. It does not replace the chronological collector receipt or classify rows exposed by unfolding a retained Mu atom.

The reference-only specialization yields an original ordinary stored-row occurrence with the same full symbol, guard, and arity, plus actual ordered child Calls or literal identity. It is not exact equality of changed child values. It is not an initial public-source occurrence when the stored input was itself generated by native intersection.

A complete outer source-anchor theorem must also compose native products and class/Parent edits with that original stored-row relation. Repeated original values with changed inherited constraints are already possible. This row-lineage result alone does not establish a decreasing outer measure, all-active-owner key exclusion, recursive termination, or public Haskell API correspondence.
