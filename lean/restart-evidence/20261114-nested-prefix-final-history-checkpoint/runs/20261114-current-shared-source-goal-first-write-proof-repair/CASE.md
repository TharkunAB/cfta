# Source-goal first-write elaboration repair

Frozen: 2026-11-14 22:46 CET. This candidate is uncompiled.

Candidate SHA-256:
`18225a144631d89a82bbc15357683311becddee93d1f99258887b82d5188dcaa`.

The original candidate remains unchanged and uncredited.
Its full diagnostic log is
`20261114-nested-child-and-source-provenance-check/source-goal-first-write-1.txt`.
All reported errors and the unused-simp error were inspected.

The public header changes only one ambiguous name.
`goalHeap : State Symbol Constraint` now uses the full
`InternedConstructorTemplates.State` name.
A text check confirms that the rest of the header is byte-identical.
No premise, operation, endpoint, or conclusion changed.

The actual shared control equation first reduces the observed branches.
It then uses `congrArg` to transport the exact pure finish equation through
the returned tuple. This avoids a failed simplifier match between the
expanded read-core record and its local name. The failed `raw` simp entry
was removed. The intermediate raw outcome now has an explicit list type
and explicit `Except.ok` constructors.

The first packet's scope and remaining producer still apply. This proves
only the actual prepared direct goal child's observed first assignment.
It retains the original inventory and the literal descendant partition.
It does not replace later descendant values with a parent source literal.
Root owns compilation and publication. No compiler, live source, Git,
board, Haskell, or `/tmp` action occurred.
