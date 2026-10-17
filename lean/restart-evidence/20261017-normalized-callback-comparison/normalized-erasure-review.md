# Pure normalized-callback erasure

The module proves three exact value equalities. It has no heap, physical
availability, source completion, or stored-output premise.

`strip_eraseSelf` removes a bare reference only when that reference already
belongs to the strip list. `finish_true_eq_erase` uses actual Local normal
form and absence of the interned local from deepNames. A free local must
then be the direct-self body. Cleanup and eraseSelf both return empty in
that case. If the local is not free, both return the body.
`eraseSelf_deep` preserves the exact ordered list, because the only changed
value is a bare reference and both that reference and empty have no deep
names.

The strict direct-1 snapshot matches the production bytes. Its log is empty.
The canonical single target passed 538 jobs. The imported public group
checks all three complete signatures, proof terms, and axiom lists. It has
no errors, warnings, sorryAx, or printer omissions. Only the standard axioms
propext, Classical.choice, and Quot.sound are permitted by the verifier.
All checks ran with actual MemoryMax and MemoryHigh of 4294967296 bytes and
MemorySwapMax of zero. No extra constructed scenarios were requested.

These equations support the separate causal candidate proof. They do not
prove the candidate's ordinary-probe equality, the private stored-Mu law,
or full normalized comparison.
