# Typed source selection repair

Status: UNCOMPILED. The first source qualification draft failed strict checking. It has no proof credit. Root owns the next check.

The failed log reports two issues. The theorem and two proof sites use nodeEdges without opening InternedEdgeResidency. The local Mu compiler simplification unfolds universeValue in the goal but does not match the selected hypothesis. These are Lean elaboration issues. They do not identify a Haskell bug.

This new packet adds an explicit InternedEdgeResidency import and namespace opening. It adds one private abstract-request mu_code helper. The helper compiles the literal rightMu branch selected for that request. The main proof applies it to the same actualIncoming, original body, original full U, and derived selected fact. This replaces only the failed local simp call.

The entire PUBLIC THEOREM declaration is byte-identical, including every premise and the complete conclusion. PUBLIC-DECLARATION.lean.txt and ORIGINAL-PUBLIC-DECLARATION.lean.txt contain those exact bytes. The complete preamble is changed. PUBLIC-HEADER.lean.txt contains the new complete preamble, private helper, and public declaration. ORIGINAL-PUBLIC-HEADER.lean.txt retains the old complete header. EXACT-REPAIR.patch records every source change.

The original raw source, original header, and failed log remain unchanged. The original source/build/stored full U, body/depth/ordinary, full original P, heap Facts and growth, cache inputs, actual keys and handles, and all conclusion clauses remain unchanged. No new assumption, height restriction, heartbeat option, or linter suppression was added.

The scope remains source syntax and key qualification. The draft supplies no future semantic, row-result, model, or warm-cache law. It does not establish worker reachability, query completion, full C/M, both operand orders, admission, one joint witness, or Haskell correspondence.

No compiler, live source, Git, board, Haskell, or /tmp operation was used.
