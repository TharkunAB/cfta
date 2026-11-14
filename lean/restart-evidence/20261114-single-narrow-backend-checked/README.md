# Checked single narrowing backend

The configured operations use one narrowing backend. Both recursive paths pass
the same narrowing operation. The five configured equations use `rfl`.
All 305 existing theorem headers in the 48 changed files remain unchanged.
The full Audit and three separate totality modules pass. See status.json for
the aggregate theorem count and the separate count of explicit axiom reports.
The import count includes Lean. The project import count is separate.
The source count does not assert a separate check of every source file.
Only propext, Classical.choice and Quot.sound are allowed.

The two identity lemmas in check20 are checked private proofs. They retain the
actual pending read, handle, heap, original queries and literal caller advance.
They do not prove joint finite completion or the public Haskell correspondence.
No Haskell source changed. Keep future Haskell fixes in FINDINGS.md.

Use status.json's checked_code_commit to check out the exact checked source.
Run `nix-shell shell.nix --run 'cd lean && lake build MicroCFTA.Audit'`.
Then run Lean on Audit.lean with `-j1 -DwarningAsError=true` inside that shell.
Build and strictly check SourcePruningEnumerationActionTotal,
SourceCurrentSelectedStepObservedTotal and SourceCurrentSelectedStepAllObservedTotal
separately. They are outside Audit. Check24 records the exact commands.
The final independent-import check prints five wrapper laws and three totality
laws. It does not replace Audit's aggregate imported-theorem dependency check.

Historical drivers are retained as executed. Their root and temporary paths
refer to the original workspace. For a historical run, use baseline_for_deltas,
apply that stage's source-delta.patch and verify its source-pins.json. The private
files are included in their stage directories. Use a separate driver when a
different workspace path is required. Keep the archived driver unchanged.
The preceding draft packet contains checks1-8 and the earlier source review.

Check10's old driver confused printed axiom reports with the aggregate count.
Its build failed before that test ran. Check12 and later full drivers use the
actual aggregate log line and count explicit reports separately. No false pass
was recorded. Check16 did not run Lean; its Python driver was not created before
the premature launch. The no-run record is retained. All compiler failures and
their later repairs remain in this packet. Text logs may use gzip compression.
This packet contains source, patches, scripts and logs. It contains no build
archive. All inputs can be reconstructed from Git and the recorded deltas.
