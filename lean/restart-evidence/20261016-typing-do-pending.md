# Upstream advance found during publication

At 2026-10-16 13:14 CEST, formalize checkpoint
`27a4722c261829341112758f10f1fe73c2ad232c` is published and the tree is clean.
The complete frontend validation remains against source main `999c04a5`.
It passes 791 examples plus golden, the strict build, format, metadata, and
unchanged Lean Audit. The current recursive field-pool counterexample is
confirmed and unfixed. Its semantic question remains unresolved.

The publication readback found remote main
`5399d3104687343ec8d26f7eaf7a3b008276560f`. Bounded fetch session 5972
completed with exit zero and advanced origin/main from `999c04a5` to this
head. No merge or validation of the new delta occurred.

The new commits are `5399d310` (PR #63) and `3b80bafe` (qualified typing
do-notation). The diff has 175 additions in five generator files:

- `cfta-generator/CHANGELOG.md`.
- `cfta-generator/cfta-generator.cabal`.
- `cfta-generator/src/Data/CFTA/Gen/Typing.hs`.
- `cfta-generator/src/Data/CFTA/Gen/Typing/Do.hs` (new, 117 lines).
- `cfta-generator/test/Data/CFTA/Gen/TypingSpec.hs`.

Next inspect this source and its rules. Snapshot all current files, refs,
stashes, and worktrees before merging. Preserve all 2443 older non-Audit
proof sources, Audit, prior evidence, counterexamples, repairs, and drafts.
Use the documented Nix build and source validation. Record any Haskell repair
first in root FINDINGS.md. The new API requires its own frontend adapter;
do not claim that the existing Lean Audit proves it.

Then resume the literal first-seeded checked query and Scan plan in
`20261016-current-conjunction-worker/scan-worker-next.md`. Keep the full
library goal active. No board posts or deployments. Push only the authorized
formalize branch. This record is progress, not a completed goal.
