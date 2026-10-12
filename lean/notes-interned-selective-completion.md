# One request erases its parent and retains older active ancestors

`InternedSelectiveConstruction.Selective` permits each source binder to
retain every enclosing input or to erase its immediate parent while
directly retaining every older input. The erasure proof uses the structural
relation from `InternedErasureCorrespondence`. Its declared empty-child
erasure can occur below further source constructors. Binder bodies in this
completion grammar have ordinary node roots with the required unary edges.

`InternedSelectivePreparedSites.Ready` stores actual earlier depth calls
only for ordinary descendants that cross no new binder. Their older
captures are exactly the current older captures. The source depth marker
occupies the one changed nearest-parent slot.

`InternedSelectiveCompletion.build_completes` handles both branches in the
same actual pending context. If the nearest input is an active parent and
the request erases it, the proof applies source-call correspondence to the
earlier depth call. If the nearest input is retained or is not an active
frame, the direct older-reference edges exclude all pending keys. Depth and
ordinary callback markers differ from every active interned reservation.
Fresh callbacks obtain their own preparation from their actual earlier
depth body. No callback stability premise supplies this preparation.

`closed_completes` starts with empty frames and caches. It derives every
active interned name and every prepared trace during execution. Its only
program premise is the stated source grammar. It does not assume a
successful first run, stable probe keys, or complete pending callbacks.

`InternedSelectiveExamples` proves a closed family at every finite depth.
An arbitrary chain of retained binders ends with one selective request.
That request reads and erases its nearest parent and keeps every older
ancestor. All edges use symbol zero. `program_complete` derives complete
record coverage, availability, and exact subsequent replay.
`program_not_pending` excludes an unfinished canonical readback.

A temporary Haskell probe exercised the matching live
`Data.CFTA.Interned` constructors under Nix. For both raw and smart
construction, an open selective request had exactly the two older free
references and omitted the nearest parent. All 12 closed chains with two
through seven retained ancestors completed with exact cached depth and
canonical equality on repeat construction. The files are
`/tmp/mcfta-selective-erasure.hs` and `/tmp/mcfta-selective-erasure.log`.
This source evidence is separate from the unbounded Lean theorem.

General closed-input first completion remains open for arbitrary retained
and erased ancestor subsets, computed-empty child erasure, and erasure
that needs union identity collapse or smart-cleanup correspondence. This
checkpoint closes the immediate-parent-erased, older-ancestors-retained
case within one request.
