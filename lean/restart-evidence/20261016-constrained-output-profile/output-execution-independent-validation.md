# Independent output producer validation

Validated 2026-10-16 19:31 CEST.

- Root canonical producer batch output-producer-build-1.log passed with 1136 jobs. Only the historical dependency warning remains.
- Fifteen independent public full signature and axiom pairs passed in output-execution-independent-public-2.log: four OutputExecution declarations, three OutputFinite endpoints including cold, and eight ProfileBudget theorems.
- Four substantive kernel signature and axiom pairs passed on the first attempt in output-execution-independent-kernels-1.log.
- Exact public source EOF whitespace was corrected to one terminal newline. The public probe was rerun once into log2. Prior log1 remains unchanged.
- All probe commands used pinned Lean v4.34.1 and canonical .lake/build/lib/lean imports. Final logs contain no errors, warnings, or sorryAx. The report count includes both “depends on axioms” and “does not depend on any axioms”. The diagnostic check accepts error: and error(…) formats.
- All eight production hashes match frozen-modules.json. No proof source, older source, Audit, Haskell, or Git state was edited. No Lake build was run by this task.

See output-execution-independent-review.md for exact assumptions and integration scope. The prior Stored component remains fifteen public pairs and five kernels; its whitespace-corrected public final log is output-stored-public-2.log.
