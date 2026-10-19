# Native edge and child retention checkpoint

Proof commit: `904d230ff`. Start: `1862b2fc6`.
Main remains `184bba662`. The pull imported no new changes.

Read `lean/notes-current-native-edge-child-retention.md` for the contracts.
Root FINDINGS retains the Haskell repair registry first. No Haskell source
changes in this checkpoint. The ordinary child native-provenance gap is
closed for the stated contracts. Global source renewal and general
termination remain open.

Three production modules expose eight public declarations. Four selected
full groups check those declarations and one constructed theorem. Three
production strict logs and one constructed strict log are empty. Three
canonical builds pass. Full-audit-1 is the exact default lake build.
Root observed execution handle 41241 return exit zero: 3462 jobs and 73854
axiom dependency checks. Its sole warning is the older unused inputs binding.

All fifteen raw logs come from entered Lean jobs. Two edge elaborations
failed. The first reader strict attempt returned zero but printed warnings;
it is not selected. Corrected attempts retain distinct names and snapshots.
All selected checks have effective 4 GiB maximum/high limits and zero swap.
Each owner retains an immutable peak snapshot. No missing process was
restarted on the basis of a stale observation.

Six component manifests pin sources, attempts, selected receipts and
reviews. Independent source and current-document reviews have separate
pins. The next native-renewal handoff describes proposed work and adds no
Lean job or theorem. Root-scope pins connect current claims with their
theorem sources. SHA256SUMS covers every evidence file except itself.
Raw logs are staged explicitly because repository rules ignore log files.
The whitespace policy preserves raw evidence bytes. Production and current
documents pass their whitespace check.

From the repository root, run:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-native-edge-child-retention/verify-checkpoint.py
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-native-edge-child-retention/verify-preservation.py
PYTHONDONTWRITEBYTECODE=1 python3 lean/restart-evidence/20261019-native-edge-child-retention/verify-closure.py
```

Closure requires a committed clean worktree. It checks tracked bytes and
modes against the index and HEAD. It requires every evidence file to be
tracked. It rechecks the retained checkpoint and preservation reports.
These commands perform no publication or board write. The pending direct
approval requirement in NEXT-PROMPT remains in force.
