# Literal parent and mutual outer workers

## Full objective

Prove that the current Haskell library implements independent mathematical
specifications for its automata and generators. Preserve separate contracts
for accepted languages, exact node-count size classes, finite execution,
counts, ordered ranks and both inverses, probability laws, and transformations.
Accepting runs, distinct terms, and generated values are different objects.
Each source path needs its own implementation correspondence. A checked
component or a passing source suite does not establish the full objective.

For the current reduction target, the intended endpoint has this shape:

```text
legitimate initial state and justified execution domain
  -> finite execution of the actual reduction
  -> returned state satisfies the physical and memo invariants
  -> for every finite term t, accepts(result, t) iff accepts(input, t)
```

The existing `SourceCurrentAllocatedPartialActual.root_exact` proves the last
two conclusions for a supplied completed strict-read call with an allocated
empty inherited payload. Its premises include initial Context, resident
input, ready inherited data, and reached machine checks. It does not prove
that this completed call exists. A future-body completion premise cannot
close that gap.

## Current source and preserved work

Source main is `c0cc8a05`, merged at `896b0a1c`. The preceding published
checkpoint is `ade9584d`. The backup branch is
`backup/formalize-before-parent-worker-20261016-1407`.
The opening pull and fetch found no source delta. All Haskell source and
the optimized interned core retain their bytes. No Haskell repair is added.
Root FINDINGS.md keeps the external Haskell repair handoff first.

The earlier local worker checkpoint supplies the current precheck, original
record Scan, required children, ordered class editing, empty propagation,
and their strict source reads and full caller receipts. The new parent
worker composes that literal execution with the checked edge constructor.
Older proof sources and their counterexamples remain unchanged.
Parent proof commit is `155da673`. The outer definition is `849d1509`.
Its completion and stability proof commit is `7d9d503d`.

## Literal parent

`SourceCurrentAllocatedParentWorker` checks raw contradiction before field
lookup or child work. Rejection executes the actual sentinel constructor.
A live branch loads the original field from the actual initial cache, runs
the literal local reducer, and constructs the returned edge. Every failure
retains its phase, full lower observation, checked state, and both warm memos.
Constructor failure retains the constructor's actual returned state.

ParentWorkerCompletion derives nine sufficient stable bounds from an actual
finite parent graph and its reached field equation. ParentWorkerStability
preserves the complete successful return under larger bounds and proves
whole-return uniqueness. The conjunction budget stays fixed.

ParentWorkerActual constructs stable execution, the same parent graph,
strict Reads, language Receipt, and full caller Post from initial Context
and live-only inputs. Its resident endpoints derive the original field and
child support from actual edge residency. They return the same source
EdgeBody and its immutable EdgeLaw. The computed inventory is shared by
Receipt and Post. Raw rejection needs no field, inherited-readiness, child,
or local-range premise. Supplied success is identified with that same return.

## Literal outer execution

`SourceCurrentAllocatedPartialWorker` defines all eight source families:
nodeCall, nodeBody, edgeCall, edgeBody, rows, descendants, children, and walk.
It carries the complete caller state and both outer result tables.
Begin and demand precede body work. Ready hits need no positive bound.
Evaluation uses the stored original request and finishes the same handle
only after success. Busy, absent, unexpected reference, pending Mu, parent
failure, inherited error, missing payload, and exhaustion remain distinct.
Failures retain the actual reached caller and full underlying diagnostic.

An ordinary node runs original rows in order. Each row runs the edge call,
then descendants of its RETURNED parent edge, then the original suffix.
Descendants run the inherited prefix once at its actual operation state.
Contradiction erases slots without child calls. The live walk performs each
indexed descent at the current state and passes the returned caller to the
next child. Final raw edge reconstruction and ordered node modification use
their literal implementations. Mu reconstruction retains its actual pending
heap. No identity shortcut replaces it.

The outer recursion bound and nine lower bounds remain separate. Ordinary
node bodies and nonempty row and child walks consume outer fuel. This makes
the bounded observer total. It does not prove general Haskell completion.

PartialWorkerCompletion derives ten sufficient stable bounds from each
actual finite outer graph. Shared induction covers all eight families and
all sixteen constructors. It retains the exact result and full caller state.
It uses the graph's literal equations and the parent completion theorem.
It does not assume an independent body completion callback.

PartialWorkerStability proves successful monotonicity for all eight families
under ten independent larger bounds. It also proves output and full caller
uniqueness across arbitrary successful bounds. The strong outer-fuel
induction derives every smaller-call transport. No physical invariant,
semantic law, future completion, or callback premise is required.

## Remaining proof boundaries

1. Connect the literal outer worker's own successful execution to its same
   physical graph and strict Reads under legitimate initial facts and reached
   machine checks. The parent adapter now supplies its local part. Apply
   PartialActual to that same return, without a future body-law premise.
2. Prove a decreasing-domain argument for general constrained recursive
   requests. Exclude unfinished owner demands on that domain. Finite graph
   realizability and successful-bound stability do not prove graph existence.
   Unequal-length path classes can move constrained structure deeper.
3. Keep repeated-pass convergence separate. Current reducePartially performs
   one pass. Language inclusion or a finite language does not establish
   convergence of newly allocated identities.
4. Complete remaining frontend and query adapters. These include drawn
   fields, validation errors and order, recursive typed and refinement
   generators, original sorted graph rows, and generator-specific ranks.
   Exact size classes, counts, ordered ranks, inverses, and probabilities
   remain separate contracts. Language equality alone does not preserve rank.
5. Transfer the logical model to GHC demand and concrete execution. Logical
   serial Reads do not prove lazy list or IntMap forcing, publication events,
   black-hole exclusion, the noConstraint CAF, concrete containers, stable
   identities, machine limits, solver IO, random draws, callbacks, or codecs.

All older constructor and equality targets remain in scope. Preserve every
proof, counterexample, repair, and marked draft. This is progress toward the
full-library objective. It is not whole-library verification.

## Evidence

Current evidence is in `lean/restart-evidence/20261016-parent-worker/`.
The pinned full Audit passes 2471 jobs and 58623 dependency checks.
Only the permitted foundations and old unused-input warning remain.
The seven new modules pass focused canonical builds, public declaration
checks, and integration kernels. Preservation retains all 5383 starting
files and all 2463 older non-Audit proof sources. Twenty-eight frozen
manifests check 228 module entries. Historical repairs, stashes, and the
three other worktrees remain. Read outer-actual-next.md for the next target.
Independent parent and outer reviews check source order, stored ownership,
returned sentinel children, literal Mu behavior, and complete failure states.
The previous source validation remains applicable because no Haskell file
changes: strict Nix all-component build, 798 examples plus golden, six-file
Fourmolu, and four-package Cabal-gild and metadata checks. The unchanged
Chain reproducer returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds retains its opaque-pool interpretation. FINDINGS.md records
the repair, reproducer, files, commit, checks, and upstream status first.
