# Actual indexed first ordinary cut and source composition

Reviewed 2026-10-20 16:43 CEST. This is an author reread of the constructed witness.

The sole public theorem is `IndexedFirstOrdinaryCutKernels.actual_prefixes`. Its public statement repeats the private checked_witness statement exactly. The public proof is an alias to that checked witness. No caller supplies any hypothesis.

The source uses Nat symbols and Bool guards. It builds a closed raw Mu with body row 19, then an open raw Mu with body row 7 and ordered children `[leaf17, var0, var1, leaf17]`. The external source input is the actual available Depth reference. Both raw binders use smart=false. The root source is their union. Joint Context is derived from empty Context and Depth availability. The actual prelude, closed leaf, open Mu, and root calls are retained with their exact start and return heaps.

The open Mu's body contains its own reference and the external Depth reference. The root remains open. Actual leaf lookups at root positions 1 and 4 return the same complete closed leaf. The selected position is 4. The leaf row has symbol 17. The ordinary parent row has symbol 7. A direct structural row at the raw root can only come through the row-19 prelude or the row-7 body. It cannot descend into the ordinary children, so `RowAt raw leafRow17` is impossible.

The open case calls official `SourceCurrentIndexedLeafSourceRows.source_cases` exactly once with the actual initial Context, completed root build, exact position-4 lookup, and RowAt of the closed leaf. Its direct arm is excluded by the actual row shapes. The remaining existential retains the SAME Cut and SourceRow for the SAME completed root source call, plus all Cut.facts lookups. Its parent row differs from the selected leaf row. No desired SourceRow or Cut is an input premise.

An independent literal certificate also checks union member 1, the open Mu body, ordinary row 0, ordered child 3, and inner leaf position 0. It retains the exact root index 4 and both prefix offsets. This computed Cut is not equated with the existential Cut returned by source_cases. The public theorem does not assert uniqueness of a cut or equality of their witness data.

The separate closed-root case applies pure Cut.split to the actual closed leaf at index zero. A Cut at a closed value is impossible from every Cut constructor's open premise. The resulting direct RowAt is retained. Closed-root stopping, repeated occurrences, and the distinction between parent row and leaf row are therefore exercised explicitly.

The result contains no encoder slot/findIdx equation, strict physical-value decrease, Ready requirement, reader transport, general source ancestry conclusion, or runtime correspondence claim. It does not change the checked negative same-leaf source-union boundary. SourceRow can retain a stored winner at a binder boundary; this fixture does not assert a new global binding origin from that receipt.

All jobs began only after both official canonical GO signals. The checked dependency sources are Cut 98e3f005 and SourceRows 8a1d9dcb. The first two strict attempts failed on concrete reduction obligations and impossible list lookups. The actual source calls and leaf shapes did not change. Strict attempt 3 has a literal zero-byte log. Full public attempt 1 prints the expanded statement, proof alias, and axioms without omissions. Its axioms are exactly propext, Classical.choice, and Quot.sound.

All four capped Lean jobs are retained with fresh usage and effective memory.max=memory.high=4294967296, memory.swap.max=0, and timeout 5m. There is one constructed pair, zero production pairs, and zero owned canonical jobs. The pre-source_cases unchecked draft is retained separately. No repository or old frozen artifact was edited. Mutable peaks are excluded from the manifest; a final four-row snapshot is pinned.
