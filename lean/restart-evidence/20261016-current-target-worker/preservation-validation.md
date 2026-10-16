# Current target checkpoint preservation

The final `--require-current` run passed on 2026-10-16. It checks baseline `740c6e5c` with current source main `ccebf0f7`.

All 4765 baseline files remain. All 2416 older non-Audit Lean source files retain their exact bytes. The only changed baseline files are the seven authorized restart documents and `Audit.lean`.

All 23 frozen manifests pass. They cover 182 module entries. The current manifest covers eight new modules and has SHA256 `5fa832a73fa03860039341b3e6f64b11b41b4e763bede984a0fb5ceb4a4d843a`.

All 205 tracked files in the four active source packages retain their baseline bytes and file set. These include 188 Haskell files. All 232 tracked Haskell files across the repository retain their bytes. There are no allowed upstream paths in this checkpoint.

The complete FINDINGS registry prefix matches `740c6e5c`. The reference prefix ends before `Current source refresh and literal merge execution`. The current prefix ends before the new `Current literal checked targets and shared leaves` heading. Both prefix hashes are `e8194d3ad32cb34a5239d082acda63fad795f4a314c2b17b229c0cb14ec44e6d`. This retains the four repair entries, registry metadata, and the PR #55 source handoff.

Stashes retain their original records. All three other worktree records retain their original bytes. Their existing prunable metadata remains unchanged.

The verifier has SHA256 `b6e04b1940565b9eabcbb6710ce90139a87659a7ad97824805305456dcbcdae4`. The final report and raw log have SHA256 `92299f02219628d643d9cc4cacd0e5799bff39820cbb325512e6a01ca76f30d5`. The earlier mid-document transition report is retained separately. It predates the explicit new-heading extraction rule and is not the final result.

This task wrote only the new verifier and current evidence. It changed no proof, source package, restart document, Git state, stash, or worktree.
