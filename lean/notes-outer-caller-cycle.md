# A closed input repeats an outer caller key

Source: `TharkunAB/cfta`, main `239feb64`, merged at `b3d06a08`.
The source-comment correction changes no algorithm. This note supersedes
the unconditional caller-rank target in [the earlier boundary note](notes-origin-boundaries.md).

## Closed source fixture

Let `W(n)` be the ordinary node `w(n)`. Let `eq01` be the normalized
class `0 = 1`. Use these closed source nodes:

```text
B = mu r. a | p(W(r), W(r))
C = p(W(B), W(B))
A = mu r. a | p(W(r), W(C)) [eq01]
R = p(W(A), W(C)) [eq01]
```

The `a` and `w` edges have Top constraints. Both recursive variables are
used. A is a constrained productive Mu. The selected endpoints at R are
closed ordinary wrappers. The source gate accepts them without inspecting
the constrained Mu below the first endpoint.

The retained Haskell reproduction checks exact physical identities:
`intersect A B = A`, `intersect C B = C`, and `intersect A C = R`.
The actual `reduceEdgeIntersection EmptyConstraints` call on R's edge
returns children `[W(R), W(R)]`. Its original local class remains `eq01`.
Physical combination with EmptyConstraints and descent through child 0
returns EmptyConstraints. The W edge has no own equalities. Its local
prefix retains R, and its physical combination and descent again return
EmptyConstraints. The outer calls therefore have these dependencies:

```text
(EmptyConstraints, R) -> (EmptyConstraints, W(R)) -> (EmptyConstraints, R)
```

This is an actual caller-key cycle. It is stronger than an increase in a
candidate height or a manually repeated sequence of intersections.

## Kernel evidence

`SourceEqualityOuterCallerCycle.source_valid` proves closed original syntax
and normalized physical annotations. `observation` runs actual source
construction, the concrete guarded native prefix at R, physical payload
readback, combination, and descent. It then runs the wrapper prefix at the
actual returned warm state and reads its next physical inherited payload.
The six worker bounds are `(4,4,2,2,2,1024)`, with 32-bit native words.

`actual_cycle` checks that the returned physical node reference equals R's
original reference. It checks that both inherited payloads have the literal
empty physical constructor. `cycle` retains the actual observation witness.
`Dependency` contains the two observed child-to-parent key dependencies.
`not_wellFounded` proves that this relation is not well founded. No strict
well-founded rank on these physical memo keys can cover both dependencies.

These theorems do not model the outer Haskell result table or GHC evaluation.
They do not assert that no finite monadic caller graph exists at every
possible warm state. The next source comparison must retain this boundary.
Existing successful-worker and equality-free-region theorems remain valid.

## Result memo and strict source demand

`memo2TypeableWith` keys the outer call by the inherited constraint and node.
`memoWith` supplies the unevaluated result to `insertKeepingFirst`.
The lazy map installs that result thunk before it is evaluated. A repeated
key returns the same stored thunk. There is no pending-entry branch that
returns the original node.

`modifyNode` compares rebuilt edge identities before it returns a node.
Edge interning hashes child node identities. Thus the child result must be
evaluated before the root result can return a constructor. The dependency
cycle demands the unfinished root result again. This explains the source
self-demand. It does not claim a particular runtime exception.

Relevant source locations are `Equality/Operations.hs:79-95,127-130`,
`Interned/Memo.hs:93-94,120-129`, `Interned/Cache.hs:149-155`, and
`Interned/Type.hs:321-325,499-525,620-627`.

## Live reproduction and validation

[The retained reproduction](repro/OuterCallerCycle.hs) prints `Just True`
for closedness, the three intersection identities, the actual local prefix,
and both empty inherited descents. A demand for the full pass's node identity
times out after three seconds. A fresh process with `--cold` also times out.
The observed outputs are `Just True`, `Nothing`, and `Nothing`.
Timeouts alone do not prove divergence. The exact dependency certificate
and source demand analysis identify the issue independently of the timeout.

The reproduction compiles with `-Wall -Werror` in Nix. Fourmolu and all four
Cabal-gild checks pass. Logs are
`/tmp/mcfta-outer-caller-cycle-retained-20261015.log` and
`/tmp/mcfta-outer-caller-cycle-format-20261015.log`.
The pinned aggregate Lean audit passes 1,891 jobs and checks dependencies
of 48,849 theorems. Only `propext`, `Classical.choice`, and `Quot.sound`
occur. The older unused `inputs` warning remains. Log:
`/tmp/mcfta-outer-caller-cycle-audit-20261015.log`.
The upstream integration's strict build, six Haskell suites, benchmark build,
and metadata checks were not repeated after this comment-only source edit.

## Next target

Model the outer lazy result memo and the strict constructor demands. Connect
the checked key cycle to that operational model. Keep runtime correspondence
separate. A total intended reduction needs an explicit cycle policy and a
finite-progress argument. A pending-entry fallback alone would not prove
termination on an infinite sequence of distinct keys. Do not attempt an
unconditional decreasing physical-key rank for the unchanged source.

No production repair has been applied. General caller completion, open
contexts, repeated fixed points, getAllAtPath, native containers, GHC
scheduling, decision-model, and extraction remain open. Preserve the optimized
interned core, older constructor and equality work, and all Sized contracts.
