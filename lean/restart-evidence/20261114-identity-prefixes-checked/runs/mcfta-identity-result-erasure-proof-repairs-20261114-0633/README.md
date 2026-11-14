# Scan and receipt proof-body repairs

Status: UNCOMPILED. This candidate starts from Root's exact check2 source, including its five axiom-print commands. The frozen 146-line input and Root check2 remain unchanged.

The scan failure occurs because `simp [eraseFold]` expands `eraseFold` under the visitor lambda. The induction hypothesis then has a different syntactic visitor. The repair proves the one actual completed head's map equation by `rfl` and simplifies with that equation. It leaves the unknown visitor's `eraseFold` call intact, so the unchanged induction hypothesis can rewrite the suffix.

The four receipt failures occur because `cases` cannot replace the hook or advance call while it remains hidden inside `SharedReceiptContinuation.run`. Each affected branch now simplifies that actual definition before case analysis. All map definitions and all five theorem statements and hypotheses retain their exact text. The other three proof bodies and the axiom-print commands remain unchanged.

`manifest.json` pins the actual check2 source and diagnostics. `headers.json` records all five unchanged theorem headers. GNU patch forward and inverse replay with zero fuzz reproduces the exact candidate bytes and restores the exact input bytes. Inverse text replacement also restores the input.

No compiler, probe, live edit, Haskell edit, Git operation, or board write ran. Root must compile the candidate and inspect all five axiom reports before making a proof claim.
