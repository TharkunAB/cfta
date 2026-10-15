# Ordered graph import at main 5c53de80

Main `5c53de80` is merged at `ea7d8b05`. The delta from `e16f3b50` changes
five files. Production changes occur only in Interned.fromRows. Equality,
native workers, enumeration, and Sized bodies are unchanged. Full library
scope and the optimized interned core remain.

## Current source schedule

The source trims rows and retains an initial-state row. A depth-first walk
assigns positional indexes in first-encounter order. Its successors are
prepended to pending work. Actual stronglyConnComp labels these positions.
Rows and child occurrences retain their source list order.

One State map memoizes by the full bound IntSet and current position. A hit
returns its stored node. A miss builds the body with the current state bound.
The completed body's freeVars test decides whether createMu/substFree is
needed. The result is inserted AFTER the body. No busy cell is inserted.

Child dispatch first resets the bound set for a different component. A bound
child of the same component returns Rec. An unbound child keeps exactly the
bound positions below it. The old lazy maps and induced-cycle schedule are
removed. Older BinderSchedule/BinderCycles source correspondence is now
historical. Its independent semantic lemmas remain useful specifications.

## Ordered schedule, rank, and finite execution

`SourceOrderedBinderImport` starts at completed finite positional rows and
component labels. Its selector models the literal three branches. Ordered
contexts are ascending distinct positions below the current position.
Every recursive child preserves this domain. The finite global key
inventory has length 2^width - 1. This count is not a proof of the source's
per-component physical node count or sharing cost.

Build/Children/Rows retain ordered mapM execution and the post-body insert.
Completed receipts preserve all entries present at their start. Build.present
derives exact final publication. Rows.fields retains literal symbols and
constraints; Children.length retains every repeated source occurrence.
Constructor operations remain an explicit completed-function interface.

`SourceOrderedBinderRank` assigns greater binary weight to lower positions.
Adding an absent child outweighs all removed higher positions. The resulting
natural rank strictly decreases at every bounded same-component recursive
child. Context cardinality does not give this proof. A kernel fixture drops
the context length while the proved rank still decreases.

`SourceOrderedBinderComplete` combines that rank with component height.
Actual child-position closure and a strict height drop on every cross-component
source edge derive every recursive Build. No completed body or total recursive
callback is supplied. `root_complete` derives a finite completed schedule
from position zero, empty context, and empty memo.

## Remaining source and semantic bridge

Actual trim, DFS numbering, child closure, SCC labels, and condensation height
must still be connected to these finite input facts. The constructor interface
does not prove mkEdge/mkNode, freeVars, createMu, or substFree semantics or
termination in the Haskell runtime. Full imported-language/run preservation,
physical sharing/count bounds, Int capacity, and Map/IntSet correspondence
remain open. Map.Strict and State.Strict demands do not establish full body
or child evaluation. Completed schedule proofs are not GHC demand proofs.

The GHC delta adds 31 component laws and one test example. It is tied to
GHC 9.14 unfoldings and retains a negative recursive listToMaybe case.
NormalForm and fit-filter production bodies are unchanged. The completed
normal-key quotient, pair-eta partial-value exception, and unbounded
normalization boundary remain as before.

## Validation

Required Nix strict build includes all packages, tests, and benchmarks with
-Werror. All six suites pass: 22 decision-model, 157 refinement, 316 unit,
19 GHC fit, and 210 generator examples, plus golden checks. Total: 724.
Fourmolu passes four changed Haskell files. All four Cabal-gild checks pass.

Focused rank/import/completion builds pass. Nineteen public import axiom
probes and five kernel fixtures pass. Root rank/history probes also pass.
The aggregate audit passes 2,120 jobs and 52,960 dependency checks. Only the
permitted Lean foundations occur. No new warning occurs. Evidence uses
`/tmp/mcfta-required-support-*`. All earlier proofs, repairs, repros, and
marked drafts remain.
