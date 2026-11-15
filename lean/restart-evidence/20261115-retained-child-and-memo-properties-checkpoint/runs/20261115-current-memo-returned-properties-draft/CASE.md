# Returned-property laws for actual memo operations

Frozen 2026-11-15. Uncompiled. Root owns compilation and publication.

The requested generic framework already exists. FlatMemoThunk.Valid is
parametric in cell goodness. lookup_valid and setStatus_valid preserve that
chosen goodness. demand_ready retains the same actual returned cell and state.
finish_ready prevents a second completion from replacing a returned payload.

SourceCurrentAllocatedNativeContextCache.Returned law records exactly a
request/result property at returned cells. Four existing private theorems already
establish empty initialization, lookup preservation, demand preservation, and
finish preservation for ANY such property. SourceCurrentAllocatedNativeScopeCache
contains a second private copy used for its free-reference law.

The ContextCache candidate changes only the visibility of returned_empty,
returned_lookup, returned_demand and returned_finish. Their headers, proof bodies,
and all existing public theorems remain otherwise unchanged. returned_evaluating
stays private. No new invariant structure or evaluator is introduced. Existing
ScopeCache is unchanged. Root must check/publish this visibility candidate before
compiling the small application module through its normal import.

The application module contains four direct laws for the actual node/edge memo
operations. node_ready_property and edge_ready_property use the physical
ready_receipt APIs to identify the exact original request from the checked key,
actual published handle and literal returned cell. They retain literal lookup
and demand equations with the SAME native state. They recover the chosen law
at that exact request and payload, together with availability or row residency.
They neither force a new result nor replay another evaluator.

finishNode_property and finishEdge_property use the exposed generic returned_finish
and the existing physical finish validity laws. The actual evaluating cell and
the SAME literal producer result/row supply the local property. The conclusions
retain weak PhysicalCache.Valid, all previous returned properties, the exact new
returned cell, the unchanged machine, and the unchanged other memo family.
They do not require strong SourceRecursiveIntersectionThunks.Valid.

The public generic lookup and demand laws cover all phases, including misses,
suspended-to-evaluating demand, busy, absent and ready observations. Lookup
creates only a suspended cell. An existing completed result cannot be overwritten
by FlatMemoThunk.finish_ready. This packet duplicates none of those proofs.

# Application scope and exact remaining obligation

Choose law as a conditional structural result-footprint property at the original
request, not merely as an unconditional property of arbitrary physical values.
The law can retain the full original source/build/stored U and the exact genuine
closed and mixed body/ref request families. No request domain is changed by the
application theorems. They do not restrict requests to empty domains or closed
operands, so they do not discard the mixed recursive calls.

The intermediate Returned input is a cache invariant to be DERIVED from the
actual empty-cache initialization and earlier actual body completions. It is not
a new assumed premise on the original caller or worker target. The localLaw
input at a finish must come from the same actual producer body and its result.
This packet does not prove that any actual producer body satisfies only-U.
It does not derive whole-history propagation, pending-domain membership,
compatible assignments, or the original full semantic target.

SourceEqualityNativeDemand uses these same native node operations through lift
and the same lookupEdge/demandEdge/finishEdge operations around its allocated
edgeBody. These laws concern the actual memo operations only. They do not equate
that allocated body with compileEdge or the literal kernel evaluator. The next
body proof must retain the actual allocated edge body and supplied fuel.

No live source, compiler, Git, board, Haskell or /tmp artifact changed. No new
Haskell defect is claimed. The source-no-Mu and no-handle branches retain their
previous separate scope. The original full targets are unchanged.
