# Next: literal checked structural edits and class pass

Read NEXT-PROMPT.md, HANDOFF.md, root FINDINGS.md, CONTEXT.md,
docs/adr/0004-explicit-graph-boundary.md, and lean/notes-current-target-worker.md.
Source main remains ccebf0f7. The preceding published checkpoint is 740c6e5c.

## Completed worker dependencies

The current allocated merge, Target, and shared Force/Leaf workers are
implemented. TargetWorker retains NativeDemand.State and the allocated merge
memo. TargetWorkerCompletion gives finite-graph stable bounds and direct
success monotonicity. TargetWorkerActual derives full caller Post at the
computed next inventory. SharedTargetWorker retains complete checked state,
class slots, and merge memo. SharedTargetWorkerCompletion and Actual give
stable finite execution and the full force/leaf receipts at actual returns.

Native success alone does not imply physical input checks. Use the proved
TargetWorkerNative bridge on its initial physical domain. Do not replace a
current checked worker by an older NativeState worker or erase its equality
operations, native tables, domain cache, fourth memo, or outer result cells.

## Exact next implementation

1. Implement the current shared EditNode, EditChildren, EditRows, and EditList
   from SourceCurrentAllocatedSharedEditGraph. Use its advanceHeap helper
   for constructor-only work. Generalize the executable shared Outcome over
   its actual output type in a NEW additive module, or use an equivalent
   local wrapper. Preserve every existing proof source byte.
2. At editAt, run the new literal shared leaf. At editBelow, keep Empty,
   reference failure, ordinary ordered row rebuild, and recursive Head
   exposure distinct. Use the actual SourceEqualityRequiredWorker.head and
   retain pending, unresolved, exhausted, and returned heaps. Use six separate
   edit/projection/read/merge/selection/native bounds. A failure skips the
   continuation and retains the same reached checked state and slots.
3. Child scans use the signed entry lookup at the actual index. Unselected
   children retain their values while later selected children may change
   state. Rebuild each edge at the child's actual return, then the suffix.
   Same-length source setChildren uses raw makeEdge with its original full
   constraint. Do not allocate a new equality field for that raw rebuild.
4. Prove successful execution to the SAME current graph and Reads, using
   legitimate initial Ready, selected domains, safe edits, and reached ranges.
   SharedEditRanges and SharedEditComplete supply the precise existing domain.
   Derive stable bounds from finite graphs. Then compose SharedEditEffects,
   SharedEditLanguage, and ProbeEdits at the supplied actual returned state.
5. Implement compiled Class from SourceCurrentAllocatedClassEdits using
   ClassEditPlan.compiled. Start only class-local slots empty over the full
   supplied checked state and warm merge memo. Preserve returned inventory,
   captured forest, physical effects, and all old warm tables.
6. Implement ClassPass.Fold tail first, then head at that tail's actual forest,
   state, and merge memo. Finish with literal propagate. Connect every success
   to the same Fold/Pass graph, strict read schedule, full receipt, and probes.

The old SourceCurrentMemoSharedEditWorker is useful syntax reference. It
uses the older native state. It is not a proof of current checked execution.
The exact available relation files are SharedEditGraph, SharedEditRanges,
SharedEditComplete, SharedEditEffects, SharedEditLanguage, ClassEditPlan,
ClassEdits, and ClassPass. Current ProbeEdits and ProbeClassPass retain
filtered-probe heaps. Confirm file and theorem names before reuse.

## Later dependencies and full goal

After class execution, implement dynamic conjunction rows/worklist, Scan,
local child reduction, parent construction, and the outer two-family worker.
The older mutual-effects-review-worker-plan.md in
../20261016-current-mutual-caller/ retains their source order and error
inventory. Its merge and target/Force/Leaf items are now complete. Other
items remain active. Do not choose an existential completion proof as code.

General constrained outer termination, unequal-length path classes, and
repeated-pass convergence remain open. Current reducePartially performs one
pass. GHC forcing, pending publication, noConstraint CAF, concrete containers,
identity lifetime, concurrency, machine bounds, solver IO, random draws,
callbacks, codecs, frontend and generator adapters, separate Sized contracts,
older constructor/equality work, and full pipeline correspondence remain.

This increment changes no Haskell implementation or test. Reuse the validated
strict Nix build, 788 examples plus golden, 15-file Fourmolu, and four-package
Cabal-gild/metadata checks. Record every later Haskell fix FIRST in root
FINDINGS.md with failure, reproducer, files, commit, checks, and upstream state.
All older proof bytes and marked drafts must remain. No board posts or
deployments. Pull before work. Run one canonical Lake at a time and inspect
the actual process handle to terminal. Push verified formalize checkpoints
regularly. Keep the full-library goal active.
