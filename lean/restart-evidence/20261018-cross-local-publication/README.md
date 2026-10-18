# Constructed root correctness and cross-local publication evidence

Starting checkpoint: bf12022d. Branch: formalize.
The local proof commit is in `proof-commit.txt`.
Source main remains c0cc8a05. No publication was retried.

Five production modules have seven selected public heads. Three actual
constructed checks have three selected heads. All ten heads retain full
statements, complete proof terms and axiom reports under all eight printer
options. Only the three standard axioms are permitted.
Five production and three constructed strict logs are literally empty.
All five canonical builds pass. The two constructed-entry targets retain
the known earlier unused-input warning. Full Audit passes 3413 jobs and
73115 dependency checks with only that earlier warning.
Each selected job has 4 GiB memory and high limits and zero swap.

The constructed root result derives logical initial Context and guard
facts. With empty inherited constraints, its result language equals the
original expression language. Actual construction, covered field history,
valid interning, guard coverage, resources and successful reduction remain
explicit. Read `progress-review-next-step.md` for the dependency correction
and the primary completion and runtime gaps.

`selected-groups.json` lists each selected head group once.
Component reviews that reuse those groups add no proof count.
`selected-strict.json`, `selected-constructed-strict.json` and
`selected-canonical.json` select the exact final receipts.
Failed and exploratory attempts remain present and unselected.
The older full-audit-1 remains retained. Full-audit-2 includes the fifth
production module and is the selected closing audit.

`verify-checkpoint.py` checks the selected evidence and frozen component
pins. `verify-preservation.py` checks the full starting tracked baseline,
earlier frozen proofs, package bytes, stashes and other worktrees.
`root-scope-manifest.json` pins the closing source, documents and evidence.
`SHA256SUMS` covers every other file in this directory.
After the closing commit, `verify-closure.py` checks filesystem, index and
HEAD, all checksums and exact retained verification reports.

No Haskell bytes change. No repair request is added. FINDINGS keeps all
external Haskell repairs first. The full-library goal remains active.
