# One proof argument-order repair

2026-11-15 04:23:30 CET.

Status: NEW UNCOMPILED CANDIDATE. Root owns compilation and publication.

The failed private check reports one argument mismatch at line 167.
`EqualityNormalize.mem_members` takes `(path : Path)` before `(classes : Constraints)`.
The new module changes only `mem_members classes path` to `mem_members path classes`.
All four public headers are byte-identical. All premises, conclusions, and
remaining proof bytes are unchanged. The original packet and diagnostic stay
unchanged. The audit in `../20261115-prefix-free-arrow-bucket-draft/AUDIT.md`
still states the exact structural conditions and full-goal limits.

No compiler, live source, Git, board, Haskell, or /tmp operation was performed.
Full same-root finite witness remains OPEN. No proof credit before validation.

Module SHA256: `c3ce204a28c80426979999ecd758f6f1aa1a90877af031e10b4107da42d7124e`.
