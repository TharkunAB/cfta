# Frozen check6 mixed-reference repair

Status: UNCOMPILED. Root must check the candidate. This packet claims no new proof credit.

Input source: `check6.lean`, SHA256 `a14072bd63ec36dd1b0333bf2bc6cda569532d648753ab075fe04498646a2790`.
Input log: `check6.log`, SHA256 `fe9b2fdc4aa6690696cdac4b20c279d6a872e656e31088f11450b87d061104d4`.
Both files were decompressed from the exact archived check6-reference packet.

The native-spine errors include union/reference constructor exclusions, unassigned node fields, and the impossible equation `Value.reference ... = Value.node ...`.
Each arose during branch unfolding with `rw [execute, onNode, selectedBranch]`.
The candidate uses `rw [execute]` and then `simp only [onNode, selectedBranch]` at all five branch steps.
Checked `SourceSynthesisUniverseBodyReferenceControl` proofs use the same simplification pattern to select the native branch.
The candidate retains all explicit bind continuations.

The final source-wrapper goal already has equal result values and differs only in the heap field.
The log gives `heapSame : { heap := finalHeap, domains := standardSecond.2 }.heap = standardFinal.heap`.
The candidate reduces this hypothesis with `change finalHeap = standardFinal.heap at heapSame` before the existing final simplification.
It also removes the four exact unused simp arguments reported at check6 lines 896, 899, 903, and 906.

All 16 declaration headers are byte-for-byte equal to check6.
The 30,968-byte prefix before the uncompiled mixed-reference draft is byte-for-byte equal to check6.
No operational definition, import, premise, target header, or source identity changes.
This candidate addresses only the mixed-domain ref(U)/Mu(U) theorem.
The body(U)/U half, full two-alias theorem, worker history closure, joint original-root witness, and full original objective remain open.

No live repository file was edited. No compilation, Nix/Lake/heavy job, Git write, push, or board write ran.
`repair.patch` applies to the exact decompressed check6 input, not to the shorter checked public file.
