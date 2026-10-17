## Current retained Mu reconstruction and actual writer growth

Updated: 2026-10-17 20:11 CEST. Starting checkpoint is `5ce4cca1`.
Proof commit is `7a441d2d`. Source main remains `c0cc8a05`, merged at `896b0a1c`.
Read `lean/notes-current-retained-mu-reconstruction.md` for the exact results.
Read `lean/notes-proof-status-20261017.md` for the whole-library target and gaps.

Initial Ready and available data now construct both sequential selected-Mu
reconstructions. Both calls replay with their own results at the common
final heap. Actual source execution also produces causal paths with real
cache growth at every stopping outcome. The selected first writer retains
its original callback paths, and both raw callback heaps grow into the
actual reader heap. NoNewMu alone does not supply this growth. Four-table
Grows does not supply issued-reference extension; derive that separately.

Open observations retain bare references, exact row symbols and full guards,
and ordered child relations. Actual Mu unfolding preserves all finite depths
in its exact entry view. This is not transport between different view heaps.
Forty finite trials and two full-value kernel examples support the proposed
two-reconstruction equality. The general equality and retained-used Mu
recursive row relation remain open. Prove reconstruction congruence through
actual selected writers next. General outer progress, convergence, current
frontend/runtime adapters, and full Haskell correspondence also remain open.

Full pinned Audit passes 3095 jobs and 68057 dependency checks under verified
4 GiB MemoryMax, 4 GiB MemoryHigh, zero swap, and 376 MiB peak. All six final
source logs are empty. Canonical builds, 37 public checks, and eight
constructed checks pass. Evidence is in
`lean/restart-evidence/20261017-retained-mu-reconstruction/`.
Earlier proofs, evidence, repairs, counterexamples, drafts, optimized code,
stashes, and other worktrees remain preserved. Keep the whole-library goal active.

No Haskell behavior patch or new production defect is added. The source
explicitly documents smart cleanup of open unused raw Mu during substitution.
FINDINGS keeps the external repair registry first. Field-pool repair b9219b9e
remains merged and validated. Record every later repair there with its
reproducer, paths, commit, checks, and upstream status.
