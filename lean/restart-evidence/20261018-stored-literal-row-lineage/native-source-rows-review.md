# Native construction to original stored rows

Reviewed at 2026-10-18 09:29 CEST.

Production: `lean/MicroCFTA/SourceCurrentNativeConstructSourceRows.lean`.
SHA-256: `4f57c91ae3dbecdd7baf393eb8fec461d66d9a52049e10981466c576a043a45b`.

The sole public theorem is `construct`. It takes an actual native construct equation, initial SemanticHeap and body availability, final-reader publication History from empty, forward growth from the actual construct return into that reader, and a literal indexed physical row in the returned value. It derives an original body RowAt occurrence with the exact symbol, full guard, and arity. The row either equals that original row or retains actual ordered stored calls from the original children to the returned children under the lexical environment at that source occurrence.

ConstructReaderReadback supplies the current raw ordinary substitution and its actual callback/filter schedule. The proof constructs the initial joint Context from SemanticHeap and available body leaves. The actual depth callback equation is rewritten to the repaired encoded callback. Context.callback and callback_verified then derive postDepth SemanticHeap, forward physical growth, and issued-reference extension. Those actual effects transport the ORIGINAL stored body into the raw substitution entry. No earlier publication History or postDepth semantic property is assumed.

The single external replacement maps only old to the actual ordinary reference. Its replacement availability follows from ordinary_available. The returned physical row is a literal root Row. Actual filtered_row and the current erasure equality transport it to the current raw ordinary result. StoredLiteralRowLineage.execute_row supplies source provenance by induction on the original stored value. Its final-reader growth is the composition of actual raw-to-return growth and the supplied reader growth. source_row removes the external replacement alternative because a reference has no literal ordinary row.

The original occurrence follows original union members and original Mu bodies. It does not descend through a generated result. The row keeps its complete guard and ordered children. RowAt.child_smaller can derive a strict original-child bound without a new public wrapper.

No BinderFree, NoDeep, finite Cap, closed-body, desired row relation, or history-before-construct premise is added. The theorem requires an observed successful construct and final reader History. It does not prove native or outer completion. It concerns direct physical returned rows. It does not infer rows from a retained-used Mu through arbitrary epsilon exposure. The Calls alternative is an actual lexical schedule; it does not equate changed children with their original records.

Selected receipts:

- `native-source-rows-direct-1`: exit 0; actual raw log 0 bytes; immutable executed source matches production.
- `native-source-rows-canonical-1`: exit 0; warning-free canonical build, 635 jobs.
- `native-source-rows-public-1`: exit 0; one complete #check @ / #print / #print axioms pair. All eight required options are explicit. Hardened validation reports no omitted terms, printer failures, warnings, errors, or sorryAx. Only propext, Classical.choice, and Quot.sound occur.

Each check uses pinned Lean 4.34.1 and a five-minute heavy-management wrapper. Inner effective memory.max and memory.high equal 4294967296, and memory.swap.max equals 0. Direct and public checks execute immutable numbered sources with -Dlinter.all=true and the compiled LEAN_PATH.

There are no failed attempts in this component. Counts are one public pair and zero owned constructed pairs. The separate native-source-kernels integration is owned by arity_meaning. This component pins only its own evidence and frozen source dependencies, without root or sibling working fixtures.
