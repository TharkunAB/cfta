# Exact source receipt equations for the actual callback frames

Status: UNCOMPILED. Root's qualified36 check reported only two frame proofs.
The complete diagnostic was inspected, including both callback sides. The
optimized child, identity narrow, noStop policy, workFuel, recursiveDepth,
metadata, target, captured caller/query and residual update all match.
There is no backend substitution and no depth adjustment.

The captured-generation rfl exposed the private finishReceipt operation.
The source already proves visitCapturedWith_eq_receipts for the SAME visitor,
hook, budget and target. That equation identifies the private finishReceipt
with the literal receipt continuation by matching the actual hook outcome.
The repair uses this existing exact equation, then reduces the observed own
singleton and the captured-frame equation explicitly. It does not replace the
source operation with the shallow adapter or a legacy child.

The selected-callback proof had an unreduced function-pair projection and
let/beta form after rewriting the frame. Its proposition is the literal
consumeSelected complete equation. The repair simplifies the frame equation
and actual consumeSelected definition directly. No callback resource or
operational hypothesis is added.

Only these two proof bodies change in the frame-only repair. All six theorem
headers and all runtime definition bodies are byte exact. FRAME-REPAIR-ONLY
preserves that intermediate owner as a deterministic gzip. Its hash is in
STATIC-CHECKS.json. The final owner appends the latest 3f4 captured-current
resource suffix BYTE FOR BYTE after that repaired prefix. Root can test the
frame-only source and the combined source independently. The final candidate
has 36 intended probes before the independent static capacity proof.

No original initial condition or resource field is removed. All original full
targets and the original prepared16 header/full source remain byte exact.
Every original noStop outcome and earlier emission under later abort stays
in scope. Full source coupled induction, complete parent-tail execution and
next-row NativeFits/Heap/restored-cache framing remain OPEN. No Haskell defect
was found. No compiler, live source, Git, board, Haskell or tmp write occurred.
The clear-writing checks were applied.
