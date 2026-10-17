# General Merge accounting checkpoint

The four current production modules are listed in new-modules.json.
Their exact hashes are in frozen-modules.json.
The successful strict source snapshots and empty logs are listed in current-strict-logs.json.
The canonical Audit reports 2916 jobs and 64684 dependency checks.

The component manifests retain exact source, review, and validation bytes.
Each component has a verification script.
verify-checkpoint.py checks current public signatures, allowed axioms, canonical builds, and component manifests.
verify-preservation.py --require-current checks all starting files, older proofs, frozen module manifests, Haskell sources, packages, stashes, and other worktrees.
verify-closure.py checks filesystem, index, committed bytes, modes, final evidence checksums, and the retained reports.
Its --remote-file option checks explicit formalize and main remote identities.

Earlier numbered source attempts and raw logs remain unchanged.
A failed attempt is diagnostic evidence. It is not a checked proof.
An empty earlier strict log can refer to a historical source version.
Use current-strict-logs.json to identify the final checked source.
Use kernel-logs.json to identify final successful public and constructed probes.

The current result is exact direct accounting, measured graph replay, and local resource transfers.
A global initial resource budget for complete general Merge remains open.
Measured replay accepts a completed measured graph and shared selection certificate.
Local resource transfers accept current physical facts and literal input widths.
The next producer must derive those obligations from initial inputs and resources.
The complete public Haskell correctness and termination target remains open.
Read lean/notes-current-general-merge-resources.md for the full proof map and next steps.

No Haskell source changes occur in this increment.
Root FINDINGS records the merged recursive field-pool repair and all earlier repair handoffs.
The unchanged Haskell source reuses the source validation retained in 20261016-drawn-fields-local-worker.
