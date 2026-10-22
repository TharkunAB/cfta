Proposed endpoint: completed-result deletion soundness for two literal rows of one fixed original closed parent.
Keep the same source Facts, arbitrary holds, admitted inputModel, its fixed ranked input, original parent, parent availability, empty parent free list, and both literal row memberships.
Use a final physical heap together with source-to-final Grows and its Coherent proof. At an H15 call site, derive these from the incoming growth, returned Extension.heap, and returned Good.
Keep the actual common edge, its residency in this final heap, and the canonical empty-domain EdgeLaw returned for (pivot, candidate).
Conclusion, first arm: common.entry.identity=candidate.entry.identity implies that every term in candidate's physical edgeMeaning is in pivot's physical edgeMeaning, for every ambient environment.
Conclusion, second arm: common.entry.identity=pivot.entry.identity implies the converse physical inclusion, for every ambient environment.
The second implication can be stated without a failed-first-test hypothesis. The actual scan uses it only when the candidate-first test fails.
No same-symbol premise is needed for the soundness adapter itself. Actual H15 call sites still derive and supply same-symbol equality to H15.
No Room, width, operational success, semantic completeness, native Receipt, result equality, or new language law is a public entry premise of a future cluster semantic theorem.
The completed-result adapter uses already derived H15 postconditions as ordinary local arguments. Its use does not discard any runtime packet field.
This text proposes a contract. It is not a Lean declaration and is not a checked theorem.
