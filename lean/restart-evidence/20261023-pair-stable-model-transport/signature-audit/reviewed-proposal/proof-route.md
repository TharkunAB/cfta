# Source reasoning only

Keep `state` literal in every premise and in the conclusion. The native checked state and the separate pair memo do not change.
Retain the old Stable returned and canonical fields directly. Their types do not depend on the interpretation.
Reconstruct Valid with its old bounded and linked fields. They also do not depend on the interpretation.
For each actual handle, cell and stored lookup, read the exact old invariant through `stable.valid.checked`.
Retain the two captured resident records in the same heap. Only the returned-cell law needs transport.
Split the stored phase. A nonreturned CellSpec has no law obligation. A returned cell has its old resident result and canonical EdgeLaw.
Use the explicit admission premise for that exact returned lookup and full captured pair. Do not infer admission from the conditional law.
Apply ContextRebase.edge_law to the same canonical empty-domain request and actual result. Agreement supplies the admitted input rank/language transport.
PairAdmission.empty_seen discharges seen coverage because this request uses the literal empty domain.
Retain both EdgeLaw fields. Do not use rank erasure to replace bounded completeness.
No induction, new definition, private helper, local theorem, or extra local type fragment is needed.
This route derives neither operational completion nor admission at publication. Those producers remain separate.
