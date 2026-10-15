# Completed result cells through actual recursive reduction

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Proofs: `45d7249a` and `51a5922c`.
Read [the worker definition and runtime boundary](notes-result-memo-worker.md).
This note supersedes its completed-cell proof target.

## Stored requests and physical keys

`FlatMemoThunkReturned` retains the original request and full returned value.
Lookup, demand, and unrelated completion preserve existing returned cells.
`SourceEqualityPartialKeyTransport` relates a recorded constraint identity to
the ordered physical trie key. Under valid ascending records and a coherent
resident heap, equal physical keys give equal inherited satisfaction.
Equal available node references give equal immutable node values.

`SourceEqualityPartialMemoFrame.run_frame` follows every actual bounded run.
It retains valid key-linked tables, constraint and publication table growth,
running ancestor requests, and all previously returned cells. This theorem
also covers errors and incomplete observations. It requires neither successful
completion nor a semantic law for a supplied recursive callback.

`SourceEqualityPartialMemoSound.Sound` checks every actual stored cell at the
current native heap. Every original request is resident, closed, and has a
well-formed inherited payload. Each returned result is also resident and
closed. Its independent language narrows the original language. The two
languages are equal when the original inherited payload is satisfied.
Empty tables derive this invariant without supplied cached answers.

## Actual recursive effects and ready hits

The body proofs follow actual native prefixes, indexed child calls, ordered
rows, edge allocation, and node reconstruction. Native heap preservation
transports immutable request and result proofs. The body check plans retain
reached native word checks and actual callback receipts. They contain no
future cache soundness assumption.

`SourceEqualityPartialMemoRequestProofs.verified` covers actual publication,
demand, ready reuse, and successful completion of the original stored request.
`SourceEqualityPartialResultMemoProofs.run_verified` discharges the smaller
callback law by induction on the body bound. Successful checked execution
derives final Sound and the existing contextual NodeLaw. It does not assume
successful execution for every input.

`SourceEqualityPartialResultMemoSource.public_exact` starts at actual closed,
normalized source construction and empty tables. Successful checked execution
then derives final Sound, native Scope, heap preservation, resident closed
output, and exact original public language with empty inheritance.
The names `PartialResultMemoProofs` and `PartialResultMemoSource` distinguish
these modules from the preserved older gate-memo modules.

`SourceEqualityPartialMemoReuse.run_ready` proves that a repeated original
completed request returns its full stored value and identical full state.
It applies at every body bound, including zero. Semantic ready reuse uses
the current resident cell proof and physical key transport. It does not
replay native effects or require equality with a nonmemoized execution.

## Successful and busy executions

`SourceEqualityPartialMemoCompletedExample` constructs `p(a,a)` from cold
tables. Kernel evaluation checks successful recursive execution with body
bound 2, native bounds `(2,2,2,2,2,8)`, and 8-bit words. The two child positions
share one leaf value. Exactly two result cells are allocated, and both are
returned. The concrete reached check plan supplies no semantic oracle.
The source public theorem derives final Sound and exact original language.

`SourceEqualityOuterMemoCycleInvariant` preserves the original closed cycle.
Its actual full returned observation has valid key-linked tables, exactly
two evaluating requests, no other allocated cells, and no completed answer
at any key. This is a finite observation. It does not prove a GHC exception,
divergence, or the absence of success at every larger bound.

## Remaining source obligations

The constraint identities are reconstructed. Native prefixes do not expose
every production EqConstraints allocation event. Next relate the physical
constraint interner to production allocation up to identity renaming. Retain
ordered trie equality, cache validity, extension, and result-memo key links.
Do not equate numeric identities across independently allocated tables.

The sequential adapter does not prove the complete Haskell demand order.
GHC scheduling, unsafe global tables, native containers, exception thunks,
and extraction remain separate. General successful caller completion, open
contexts, repeated fixed points, getAllAtPath, decision-model, named measures,
and the changed parser and constructor decoder also remain open.

## Validation and preservation

Focused final semantic build:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityPartialResultMemoSource
```

This passes 1,072 jobs. Log: `/tmp/mcfta-memo-source-20261015.log`.
The completed fixture passes 1,073 focused jobs. Its build and dependency
logs are `/tmp/mcfta-partial-memo-completed-build-20261015.log` and
`/tmp/mcfta-partial-memo-completed-axioms-20261015.log`.
The full command `lake -d lean build` passes 1,914 jobs and checks the axiom
dependencies of 49,869 theorems. Log:
`/tmp/mcfta-memo-invariant-audit-20261015.log`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The existing unused-input warning remains.

No Haskell file changes in this checkpoint. The prior six suites, strict Nix
build, Fourmolu, Cabal-gild, package metadata checks, and 205-rank example
comparison retain their prior source evidence. They were not repeated.
All older Lean proofs except Audit imports remain byte-identical.
Reproductions, marked drafts, stashes, and other worktrees remain preserved.
