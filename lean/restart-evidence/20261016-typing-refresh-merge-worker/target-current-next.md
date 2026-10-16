# Next: literal checked Target and shared Force/Leaf

Read NEXT-PROMPT.md, HANDOFF.md, root FINDINGS.md, CONTEXT.md,
docs/adr/0004-explicit-graph-boundary.md, and lean/notes-current-merge-worker.md.
Current source main is ccebf0f7. The interned core and Sized source are unchanged.

## Completed dependency

The literal current allocated merge worker is implemented and verified.
SourceCurrentAllocatedMergeWorker.execute/call retain the full heap,
equality operations, and merge memo. WorkerSound derives the identical graph.
WorkerCompletion proves stable bounds and both finite-graph equivalences.
WorkerActual.finite constructs stable literal execution from initial warm
Context and input availability and derives the full caller Post.

Use these current APIs. The older MemoMergeWorker stores only the older heap
state. It does not implement the current equality allocation. No source
execution should be implemented by choosing a proof of existential completion.

## Immediate dependency order

1. Implement checked Target using the current NativeDemand.State, current
   inventory and actual selected operands, and the new allocated merge call.
   Execute actual field loads and readiness checks in source order. Retain
   the returned equality operations, native tables, domain cache, merge memo,
   and exact reached failures. Connect successful returns to the same checked
   target relation and strict read evidence. Then derive sufficient stable
   bounds from its justified current completion domain.
2. Implement shared Force/Leaf. Preserve actual target-slot states and first
   stored owners. A ready hit needs no body work. A miss constructs its target
   once. Leaf must query its target/input at the force return. An unchanged
   output need not mean unchanged state. Keep the fourth memo and all warm
   caller fields. Do not reset caches to use cold theorems.
3. Implement checked edits, the class right fold and full pass, dynamic
   conjunction rows/worklist, Scan, local child reduction, parent construction,
   and finally the outer two-family caller. The exact dependency and error
   inventory is in
   ../20261016-current-mutual-caller/mutual-effects-review-worker-plan.md.
   Its first merge item is now complete. Later items remain active.

The worker must retain unsuccessful reached states: missing fields,
unexpected Rec, accessor/constraint failures, native failed/blocked/yielded,
selection pending/unresolved/exhausted, busy or absent cells, and execution
fuel exhaustion. Do not turn a failed body into a completed answer or an
emptiness result. Do not demand skipped suffixes. Keep algorithm admission
budgets, primitive exposure bounds, and outer execution fuel distinct.

The outer worker must start with actual begin/demand. Evaluate the stored
first owner on a suspended hit. Finish only successful bodies. Ordinary rows
run parent reduction, descendants of the RETURNED parent, and then the suffix.
Use inherited-first prefix combination, actual indexed child payloads,
same-arity raw rebuilding, and the returned full guard. Preserve actual Mu
reconstruction and pending state.

Every successful execution must derive the same completed graph and strict
source-aligned Reads. Apply SourceCurrentAllocatedPartialActual to that same
return. Equal erased heaps do not identify different read schedules. A
constructed logical query receipt is not concrete host table execution.

## Full objective remains active

General constrained outer termination is open. Unequal-length path classes
can move constrained structure deeper. Local finiteness and semantic
narrowing do not supply a decreasing recursive measure. Repeated-pass
convergence is separate from the public one-pass reducePartially operation.

Current typing inputs, Binders, type domains, GHC pruning, deriveLTAOn,
generator ranks, all separate Sized contracts, runtime forcing, noConstraint
CAF, lazy publication, concrete containers, concurrency, identity lifetime,
machine bounds, solver IO, random draws, callbacks, codecs, and older
constructor/equality work remain active. See frontend-proof-coverage.md.
Preserve every older proof and the optimized interned core.

Record every Haskell fix first in root FINDINGS.md with failure, reproducer,
files, commit, checks, and upstream status. This increment has no Haskell
behavior or test edit. The source refresh has already passed the strict Nix
build, 788 examples plus golden, 15-file Fourmolu, and four-package metadata
and Cabal-gild checks. Do not rerun unchanged checks without a new reason.

The full Audit passes 2417 jobs and 57607 dependency checks. One canonical
Lake process may run at a time. Track its actual process handle to terminal
completion. Retain raw failure logs beside corrected final validation.
Commit reviewable changes and push verified formalize checkpoints regularly.
No board posts or deployments. Do not mark the full goal complete here.
