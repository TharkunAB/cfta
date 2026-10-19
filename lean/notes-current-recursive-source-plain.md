# Original-source exclusion in recursive observations

Updated: 2026-10-19 11:54 CEST. Start: `cec4415b`.
Source main remains `c0cc8a05`. Proof checkpoint: `e619dc99a`.

## Current system guarantee

Fresh construction always finishes in the Lean model. Under the stated
guard conditions, the result represents exactly the specified finite trees.
A completed supported root reduction with empty inherited constraints
preserves that exact language. General reduction completion and Haskell
refinement remain open. Read `notes-current-system-claim.md` for the contracts.

## Original recursive sources

`SourceCurrentRecursiveSourcePlain.annotated` passes hereditary annotations
through a literal ordinary-child `Occurs`. The relation does not follow
stored Mu bodies, union members or observed unfolding rows.

`origin` transports a recursive occurrence through the existing Required
`Origin`. It retains the exact same complete value and natural child path
in the original input, or proves that value plain. Row reconstruction
retains its actual source row index and ordered child origin. An ordinary
rebuild cannot create a Mu or union at its root.

`gate` proves that an original false primary trace makes any recursive
ordinary-child prefix plain. Its finite shortcut excludes recursive values
with actual coherent depth, closedness and union normality. Its branch
case replays every original row at the actual returned heap. It does not
invent a child trace when the finite shortcut skipped that child.

`required` composes these results. It uses the original false gate at
`positions ++ remaining`. The prepared value needs no false gate. This
distinction is required: an earlier checked example shows that Required
can change the primary gate from false to true.

## Actual selected readers

`SourceCurrentRecursivePlainRead.project` preserves a hereditary annotation
through an actual signed projection. It handles recursive Heads and the
literal ordered union reads. It needs no whole-value closedness premise.
`project_read` proves the annotation on a selected complete row in a later
actual read. Its reader semantic support, forward `Keeps` and causal guard
heap remain explicit.

`SourceCurrentRecursiveEntryPlainRead.entry` needs only the annotation on
the exact first recursive value. It does not assume the whole edited input
plain. Ordinary Entry steps follow their exact `ProjectionFrame`. Actual
projection and read prefixes derive child availability, semantics and costs.
Actual suffixes derive the forward interval to that operand read. Causal
guard heaps restrict backward along these actual intervals. No forward
guard-heap transport follows from heap growth alone.

## Composed event source

`SourceCurrentRecursiveObservationOrigins.fold_positive` takes an actual
`RequireChildren`, actual chronological `FoldReads`, and the literal
selected projection and complete row read. The Required return supplies
the fold's exact input forest. The producer derives its ordered Required
origins and the fold's final physical support. The initial selected-path
domain passes through the fold.

The original false `PathTrace` refers to the forest BEFORE Required.
The selected reader derives its exact first recursive Entry and natural
prefix. Its path equation derives the natural suffix. If the fold ancestry
names an initial prepared value, the actual Required origin and original
gate make that exact recursive value plain. The Entry reader then makes
the selected row plain. This excludes that case for a nonplain row.

The result is an ordinary `Route` in the FINAL fold value, or an actual
earlier native/Head `FoldEvent` contains the exact first recursive value
at a literal residual `Occurs` path. The ordinary alternative is not an
initial source-row theorem. The recursive alternative retains the exact
Entry, including its selected projection and read history.

Initial Required exposure safety, semantic support, costs, availability
and guard heap remain explicit. Initial fold readiness, inventory, class
coherence, active paths, domains, memo support, validity and native history
remain explicit. The fold's returned causal guard heap and the later
reader's semantics, forward Keeps and guard heap remain explicit.

The preparation and fold graphs share a returned forest. Their supported
heaps remain separate. This theorem composes completed graphs. It does not
derive the complete chronological execution of one outer call.

## Constructed checks

One source-built example has a positive ordinary wrapper and a plain used
Mu child. An empty Required call retains its source occurrence at `[0]`.
A literal nonempty Required call exposes the Mu and moves that same value
to ordinary child path `[0,0]`. That path has no original literal occurrence.
The actual original gate is false. The new source theorem proves the
prepared recursive value plain without a changed-value gate premise.

A separate plain used-Mu example checks an actual empty-path projection
with a Mu row read, and an actual nonempty projection with a recursive
Head and terminal row read. The exact Entry root and Head cases invoke
the new reader theorems. Construction and actual effects derive their
annotations, semantic support, availability, Keeps and causal guard heaps.
Neither example claims a complete class-fold event observation or an outer
driver selection. Neither asserts finite productivity or a Haskell defect.

## Remaining work and checks

The native event case still needs an observation handoff through later
class edits. Exact literal value ancestry does not produce a completed
projection of the unchanged whole event value. The progress proof then
needs a bound on renewed calls and active-owner exclusion, including empty
owners. General outer completion, repeated-pass convergence and Haskell
refinement remain open. The full-library objective remains active.

All four production strict logs are empty. All eight new public theorem
heads pass complete proof printing and standard-axiom checks. Two constructed
theorems pass strict and full proof checks. The default build passes 3451
jobs. Audit checks 73748 axiom dependencies. Its only warning is the unchanged
unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion.lean:24:5`.
All Lean jobs use Lean 4.34.1, a 4 GiB cap and zero swap. Failed attempts
remain in `restart-evidence/20261019-recursive-source-plain/`.

No Haskell bytes change or repair request is added. `FINDINGS.md` retains
every external repair first. Field-pool fix `b9219b9e` remains in main
`c0cc8a05`. All earlier proofs and evidence remain preserved. Publication
awaits direct approval. No push or board write is attempted.
