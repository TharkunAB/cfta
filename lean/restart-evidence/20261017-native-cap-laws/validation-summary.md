# Native cap checkpoint validation

Proof commits: d60a4fbd, 70401f89, e3b4c09d.
Pinned Lean: leanprover--lean4---v4.34.1.
Full Audit: 2777 jobs, 62293 theorem dependency checks, exit zero.
Only propext, Classical.choice, and Quot.sound occur.
All seven current production files pass absolute-path strict checks.
Every root strict log has zero bytes.
Seven imported groups contain 51 full signature and axiom pairs.
All final imported logs are clean. Six component manifests retain 145 entries.
One historical root integration input resolves to its exact preserved snapshot.
All failed sources and raw logs remain separate.

The source-input error in the first Scope canonical build is preserved.
Its exact failed source is cap-scope-direct-3.source.lean. The corrected
source passes native-scope-build-2.log. An early component status mistook a
trailing date command's exit for the Lean exit. The final independent checks
use the actual Lean exit and inspect the complete log. All linters stay enabled.
Canonical replay retains the older unused-input warning.

Preservation: 10557 initial tracked files, 2769 older non-Audit proof sources,
239 Haskell files, 63 frozen production manifests, and 534 entries.
Seven restart authorities and additive Audit imports are the only permitted
changes to starting files. All other starting files retain their hashes.
Stashes and three other worktrees remain unchanged.

No Haskell source, behavior repair, or test is changed. Current main c0cc8a05
includes PR65 repair b9219b9e. The original Chain derivation returns
Left (FieldAtomOnDatatype "Next" 0). Its standalone holds results remain
opaque. Root FINDINGS records the external handoff first. Reuse the strict
Nix all-component build, 798 examples plus golden, Fourmolu, and Cabal-gild
results for this unchanged source. Remote main was rechecked before publication.

Read checkpoint-validation.json and preservation-final.json for exact hashes.
These checks verify component statements. General mixed native cap closure,
warm and constrained recursive completion, convergence, frontend/runtime
adapters, capacity, serial public pipelines, and whole-library correspondence
remain open. Read next-mixed-native-producer.md for the next obligation.
