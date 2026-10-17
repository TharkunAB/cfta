# Native row histories, original-input exchange, and union normality

Starting published checkpoint: 0068ade6.
Proof commit: f1f77bf182cd11a4754b7eb159ac2d903fd7920a.
Source main: c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

Read `../../notes-proof-status-20261017.md` for the whole-library target.
Read `../../notes-current-native-row-origins.md` for the exact new results.
The four production modules and their hashes are in frozen-modules.json.
Audit adds only their four imports.

## Validation

checkpoint-validation.json identifies every selected public and constructed
probe. Each selected probe explicitly sets all eight proof-printing options.
The selected groups check 26 new public declarations, six existing status
declarations, and six constructed integrations. This is 38 pairs in seven
groups. Four component manifests verify 244 hash references.
Public probes print complete signatures, proofs, and kernel axioms.
Constructed probes check the same concrete declarations and their axioms.
The six existing status declarations are counted separately from new public
declarations. Failed and superseded attempts retain their source and raw logs.

The final production strict logs are empty. Each matches its frozen source.
Canonical targets pass. Full Audit passes 3051 jobs and 67320 dependency
checks. The only permitted axioms are propext, Classical.choice, and Quot.sound.
Audit replays one older ClosedCompletion unused-variable warning.
The new selected source and probe logs contain no diagnostic.

The frozen union-normal public-2 probe sets its printer options in source.
It supplies the linter option on the command line. The final root probe adds
that option explicitly in source. Its other source bytes remain unchanged.
checkpoint-attempt-1 retains the stricter aggregate verifier's rejection.
The final selected group is union-normal-public-final-3. The older group
remains in its unchanged component manifest and is not counted twice.

All heavy checks use heavy-management. Final checks record effective
MemoryMax and MemoryHigh of 4294967296 bytes, with zero swap. The full Audit
peaks at 410 MiB. Initial exploratory checks without an effective readback
remain preserved. They are not selected as final resource evidence.

Component manifests bind source modules, fixtures, raw output, and resource
records to their bytes. component-manifests.json lists those manifests.
SHA256SUMS covers every file in this evidence directory except itself.
The final closure check also compares every tracked blob and executable mode
with the index, filesystem, and HEAD.

Run these checks from the repository root:

```sh
python3 lean/restart-evidence/20261017-native-row-origins/verify-checkpoint.py
python3 lean/restart-evidence/20261017-native-row-origins/verify-preservation.py
python3 lean/restart-evidence/20261017-native-row-origins/verify-closure.py
```

The closure check requires a clean committed worktree. Its optional
`--remote-file` argument checks a captured ls-remote response against HEAD
and the source main recorded above. Closing reports stay outside the hashed
package so that publication does not create a self-referential checksum.

## Preservation and remaining work

The baseline has 17394 files. Preservation retains 3046 older non-Audit proof
sources, all 242 starting Haskell files, all 206 active-package files, both
stashes, and three other worktrees. The 104 frozen module manifests retain
808 hash references, including the four new modules. Updated authority and
status documents and the four Audit imports are the only baseline changes.

preservation-attempt-1 records a verifier failure. Its historical registry
slice crossed the newly inserted proof section. The corrected verifier
checks the repair registry and the complete older proof-section suffix
separately. No frozen evidence or older proof source was changed or removed.

Raw free-name absence now constructs original-input exchange. Normalized
callback no-deep absence does not imply that premise. General recursive
normalization, warm body-to-ordinary provenance, outer-node progress, and
repeated-pass convergence remain open. No desired future result or output
origin is added as a producer premise.

No Haskell behavior change or new production defect is added. FINDINGS keeps
the external repair registry first. Field-pool repair b9219b9e remains merged
and validated. The original Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pools.
The unchanged source reuses the strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild validation. Every later repair must enter FINDINGS
with its failure, executable reproducer, affected paths, commit, checks,
and upstream status.
