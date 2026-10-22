# Ready pair completion plan
Status: SOURCE-ONLY proposal. No proof body or accepted H10 theorem exists.
Import checked SourceCurrentSameSymbolEdgeStable. Use one public theorem, ready_complete.
Use heap Coherent instead of full native Good. Only resident identity uniqueness needs it. [R30–36;E157–166]
Retain the same fixed semanticView, model, ranked, holds and complete before.checked state. [S14–37;L69–81]
Require both actual requested operands resident and at least one ordered table key present.
Case split on the original table key. A present key selects its actual cell through Stable.valid.linked. [M35–50]
Stable.returned makes that cell returned. Stable.valid.checked supplies captured residency, result residency and law. [S14–37;T80–85]
The stored key equality gives both captured operand identities. Apply edge_identity_unique twice at the SAME heap. [E157–166]
Substitute the full captured edges. This obtains the exact canonical emptyDomain EdgeLaw without symmetry.
For an original hit, lookup_hit and demand_ready give call→demand→ret[]→done in three steps. execute 7 stops at that done. [C63–106;M62–65;M185–196]
For an original miss, the presence premise supplies the reversed key. Stable.canonical forces right.id < left.id. [S33–37]
If left.id < right.id, reverse canonical presence contradicts the original miss. Equal IDs collapse both keys.
Publish the original suspended pair, demand it, then swap to the existing reversed pair. [C67–83;M53–74]
Valid.bounded makes its old handle differ from before.memo.next. Preserve its cell and table entry through both new status writes. [M35–40;M121–132]
The reversed hit selects its actual returned cell. The two full captured equalities identify the requested canonical pair.
Run seven literal wrapper steps: call, demand, order, reversed call, reversed demand, finish ret, final ret. [C63–106]
The checked state stays unchanged. Only the new original pair cell is added and returned in the reverse-only case.
Use Extension.refl after rewriting checked equality. Apply checked completed_preserves once for final Stable, Extends and Returned. [K19–26;S258–338]
Use two small private facts at most: actual ready-cell readback and the reverse-only seven-step execution.
Do not import private H9 helper names, repeat its writer induction, or fabricate a native Receipt.
Keep the empty Stable producer out of this module. An empty table cannot satisfy the ready premise; add that producer with the later cold both-miss composition if needed.
Target 230–260 total source lines. Hard stop: 350 total rendered source lines before more implementation or any compiler.
Both misses retain H8 semantic completion, current admission and WordRanges obligations. This theorem does not discharge them. [B99–146]
No execution, capacity, practical host-width, repeated-pass, solver API or Haskell refinement claim follows beyond the stated ready path.
