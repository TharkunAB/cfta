# Initial Target prerequisites

The starting published checkpoint is f7494679. Proof commit a52aeb5f adds
three production modules and their Audit imports. Source main remains
c0cc8a05, merged at 896b0a1c. No Haskell behavior changes.

The checkpoint proves exact full allocated Merge numeric replay, a pure
source-order Target profile and fuel schedule, and full Target receipt
composition from actual components. The complete initial multi-path Target
execution theorem remains open. Read
`lean/notes-current-target-forecast.md` for the top-level contract,
established components, exact next theorem, and remaining library work.

The full pinned Lean Audit passes 2934 jobs and 64980 dependency checks.
Each production module has an empty final strict log and a successful
canonical target build. Full public signatures and axiom probes use
explicit terms, proof terms, universes, and deep printing. The dependency
audit permits only propext, Classical.choice, and Quot.sound. The full build
repeats one warning from the unchanged earlier
InternedFreshOrdinaryClosedCompletion dependency.

Run `python3 lean/restart-evidence/20261017-initial-target-forecast/verify-checkpoint.py`
to verify source hashes, complete probes, successful logs, and component
manifests. Run `verify-preservation.py --require-current` in this directory
to verify all earlier tracked files, proof manifests, Haskell files,
active-package files, stashes, other worktrees, and historical findings.
Run `verify-closure.py` after commit to compare filesystem bytes and modes
with the index and HEAD. Its optional `--remote-file` argument checks saved
`git ls-remote` output for formalize and main.

Freeze SHA256SUMS last. Do not change this evidence after publication.
Keep subsequent closure reports outside this directory.

The next proof must construct the actual Operand, recursive tail, and
checked query in source order. It must derive every reached Profile,
Frame, cap, inventory, and memo law from initial facts and reservations.
It must retain the exact full allocated worker state at the computed
shared fuel. Do not accept a later completed graph, successful fuel,
returned heap bound, FoldRanges, or TargetRanges as an initial premise.

Root FINDINGS records the merged recursive field-pool repair b9219b9e.
The retained Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Current derivation validation rejects
the invalid configuration. No further Haskell fix is added here.
