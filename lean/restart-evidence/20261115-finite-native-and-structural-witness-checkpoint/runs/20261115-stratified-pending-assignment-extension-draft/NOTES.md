# Structural extension of fixed pending choices

Status: UNCOMPILED. Root must check the two theorem probes. The new module imports EnumerationAssignment. Existing public files and APIs stay unchanged. The source module has 107 lines.

The existing evaluateSlots uses one constant fallback. Its stratified_assignment theorem also requires every pending slot to have node = none and scs = []. Those interfaces cannot preserve the distinct branch and base choices in the actual proper-path witness.

The new evaluateSlotsWith uses base uv at every unresolved variable and at zero fuel. The stabilization proof follows the existing dependency-level proof and reuses fill_holes_congr. It needs Stratified and actual representative paths. It does not need a model or a domain assumption.

stratified_extend_pending constructs ONE assignment by evaluating at frontier + 1 with representative roots obtained from Safe. Supplied base UF compatibility proves UF compatibility of that assignment. Safe fixes every live stored root. Stabilization then proves every stored enumerated equation in the requested orientation:

    assignment uv = fill assignment fragment

Every pending stored slot keeps exactly base uv. Pending graph handles and suspended buckets can remain present. No domain or bucket emptiness condition is used.

Agreement extends to aliases of a pending root. For a path from uv to root, new UF compatibility gives assignment uv = assignment root. Pending agreement gives assignment root = base root. Supplied base UF compatibility gives base root = base uv. All these facts concern the same state and the same assignment.

Every returned Language.Term is finite. The theorem does not certify native domain membership, suspended path predicates, residual guards or any earlier execution history. It does not supply full EnumerationCorrectness.Satisfies. Root handles the separate weak partial-readback interface and its consumers. No duplicate readback proof is included.

The static checks and dependency hashes do not establish Lean validity. No compiler, live source, Git, board or /tmp write is used. No Haskell change was identified.
