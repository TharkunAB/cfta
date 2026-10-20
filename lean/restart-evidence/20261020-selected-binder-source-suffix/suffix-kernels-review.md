# Actual two-union terminal source suffix

The fixture builds `union [union [node5 [leaf17, leaf17], node99 []], node100 []]` from the empty heap with no captures. Both source unions have actual later allocation work. It computes the node5 call separately. Its return heap differs from the whole return heap.

The actual whole result contains the same full node5 row. `build_row_origin` derives its SourceRow receipt from the literal completed whole build and the initial rich Context. `reached_initial` supplies the original rooted entry. The proof invokes `terminal_source` once. The public theorem retains the returned nonunion SourceRow, rich Context, Reached, default syntax-size bound, and physical and issued growth from its terminal return to the actual whole return.

The theorem does not identify the existential terminal call with the separate computed node5 call. It does not assume focus, suffix growth, ancestry, or success. It does not infer current callback identity, source uniqueness, generated-child bounds, or termination.

Selected strict attempt 1 has an empty raw log. Selected full printer attempt 1 has one complete constructed statement, proof and axiom report, all eight printer settings, and only standard axioms. Both jobs ran with verified 4 GiB memory.max and memory.high, zero swap, and a five-minute cap. Both completed with exit 0. There were no failed attempts, canonical jobs, repository edits, or new production heads.
