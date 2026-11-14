# Exact child CPS metadata transport

Status: UNCOMPILED. This directory freezes a separate full-body proof draft. It does not change the earlier 146-line map module or Root check2.

The candidate gives eight theorem bodies: `visitChildren_transport`, `visitSelected_transport`, `shallowVisit_erasure`, `consumeSelected_erasure`, `visitCapturedWith_transport`, `eagerChild_erasure`, `runWithChild_transport`, and `prepared_erasure`. It imports the existing five maps from the earlier draft.

The tuple and selected-edge lemmas use an exact equality between the two existing visitors as a mathematical induction premise. The actual eager-child theorem discharges that equality by native-height induction and the actual shallow fallback. The final eager-child and prepared theorems add no visitor guarantee or model assumption. The theorems preserve complete and stopped folds, all processed receipts, all endpoints, and list order and multiplicity.

The captured-edge proof uses the existing public single-receipt continuation on the same explicit receipt. Its result is definitionally the same as the private `finishReceipt` helper. No private source declaration changes.

`headers.json` and `headers.lean.txt` contain all exact theorem headers. `source-pins.json` identifies the source inputs and unchanged earlier map module. `candidate.patch` adds the new module. GNU patch add/remove replay with zero fuzz reproduces the candidate bytes and then removes the file. These mechanical checks do not verify Lean elaboration.

Root reports that the five maps and three earlier supporting laws elaborate, but `scan_erasure` and `receipt_erasure` in the dependency need proof-body repairs. Those repairs will be frozen separately. No compiler, live edit, Git operation, Haskell edit, or message board write ran here. The whole-worker fuel induction is outside this bounded draft.
