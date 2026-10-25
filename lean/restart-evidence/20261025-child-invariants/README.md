# Child invariant evidence

The checked proof sources are in each strict-check directory.
Each run retains its complete raw output and a command/hash report.
The final passing strict inputs match the committed proof files.
The rejected inputs and their full logs remain. They are not final sources.

`verification.json` checks the reports, final source bytes, public readback,
source-review conclusions and the aggregate audit result.
`public-1/raw.log` contains all seven installed public signatures and axiom sets.
Pretty-printer options affect this separate readback only.
`cap-probe.json` records effective limits for the same cap mechanism.
`heavy-peaks` records the capped proof jobs and that cap probe.
No runtime tests or Haskell source changes are part of this checkpoint.

See `lean/notes-current-pruning-enumeration-child-invariants.md` for the result,
failed proof attempts, scope boundaries and remaining traversal obligations.
