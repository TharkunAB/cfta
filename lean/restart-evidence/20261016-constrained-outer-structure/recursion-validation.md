# Conditional recursion helper validation

Validated on 2026-10-16 with pinned Lean 4.34.1.
The two sources are frozen.

`OuterRecursionDefs.lean`: 50 lines; SHA256 `e69293e4045037c3fe21e288eebdf656ef5fbd08c8f1ddb101831c39691f5a3e`.
`OuterChildren.lean`: 123 lines; SHA256 `230751dfebf4d4febc18dfac308ca3dd608ef4e85c2fc7b60b73b52dff09c3ea`.

NodeResult contains its own actual node graph, strict reads, Checks, physical Post, result residency,
three structural cache certificates, input-relative domain/height bound, and independent NodeLaw.
Below applies only to nodes strictly below the supplied natural rank.
Its premises are initial current invariants, input domain/residency, active-owner exclusion,
and an entry range plan at that smaller node's actual initial state.
The root strong induction must derive Below.
Neither definition alone asserts general graph existence.

Walk and Children construct their own ordered graphs and strict reads.
The literal descent receipt supplies the actual child inherited payload and caller state.
The root plan restricts to this entry before the child succeeds.
The suffix plan restricts only after the actual earlier child graph completes.
Reverse active-frame preservation restores the sibling cap.
The result retains every original forest position, all three structural caches, and input-relative height bounds.
Contradiction erases positions without child calls.

Direct definition check: `recursion-defs-direct-1.log`, exit 0, no warnings.
Root canonical definition build: `recursion-defs-build-1.log`, exit 0, 1522 jobs.
Root canonical child build: `children-build-1.log`, exit 0, 1523 jobs.
Only the historical unused `inputs` dependency warning occurs.
Root owns and observed both canonical process completions.

Final imported `recursion-public-1.log` passes with exit 0 and no warnings.
It contains four public axiom checks and four full signature checks.
`recursion-kernels-1.log` passes with exit 0 and no warnings.
It contains two named integration proofs, two axiom checks, and two signature checks.
The empty walk derives Below at rank zero by contradiction and returns its exact whole caller without a smaller-call hypothesis.
The second proof derives the independent WalkLaw from the same constructed graph and reads as the positional structural bounds.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. No `sorryAx` occurs.

The rooted entry plan remains an explicit machine-range obligation.
These are induction helpers. Their strict Below interface must not be reported as a completed root progress theorem.
No old source, Audit, Haskell, documentation authority, or Git state was changed by this task.
