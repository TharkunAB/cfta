# Literal checked targets and shared leaves

Updated: 2026-10-16. Source main remains `ccebf0f7`. The preceding published
checkpoint is `740c6e5c`. Proof commits are `817e4459`, `0d636786`, and `2a8afe4d`.
Eight additive modules implement current targets,
shared forcing, and leaf intersection. No Haskell behavior or test changes.
Root FINDINGS.md keeps the external Haskell repair registry first.

## Literal execution

SourceCurrentAllocatedTargetWorker retains the complete NativeDemand.State
and allocated merge memo. It runs forest projection before the actual
allocated merge. It advances both the returned heap and equality operations.
Its five bounds control projection, row reads, merge work, selection, and
checked native instructions. Native yielded, failed, constraintError, and
blocked observations retain their exact control and state. A failed prefix
does not enter its continuation.

The source first operand is the fold seed. Each remaining head operand
executes before its tail. Intersection starts at that tail's actual return.
For operands a, b, c, the order is b intersect (c intersect a). An empty target
returns EmptyNode and the identical state and memo without using fuel.

SourceCurrentAllocatedSharedTargetWorker retains complete checked state,
class-local slots, and warm merge memo. A hit returns the whole input state
at any bounds, including zero. A miss stores only a completed target. A
failed target retains its returned checked state and merge table without
installing a slot. Leaf forcing precedes checked intersection with the leaf
input. Every native observation retains slots and merge entries unchanged.

These are literal serial models. They do not identify the GHC forcing order,
lazy publication schedule, concrete Set/IntMap iteration, or noConstraint CAF.

## Soundness and physical checks

TargetWorkerSound proves projection, merge, and operand graph soundness
without semantic entry assumptions. Checked leaf and fold soundness need
the physical input domain. TargetWorkerNative.of_done derives the physical
Step from initial Good, idle cells, closed resident operands, reached word
ranges, and the supplied literal native success. It independently constructs
a physical trace and aligns the whole return by success uniqueness. It
does not assert that arbitrary native success implies physical validity.

Fold soundness derives each actual tail's Ready, available operands, and
closedness from the earlier operand and fold receipts. Its public premises
are legitimate initial Ready/At, captured Values, selected path domains,
warm Stored/CacheCovers, actual-prefix ranges, and initial global validity.
It contains no completed native-body callback or future result law.

SharedTargetWorkerActual derives each actual force and leaf graph from the
same legitimate initial facts. A stored hit needs no new target range plan.
The checked leaf step uses the actual returned force state. Its receipt
proves narrowing and preservation of class-satisfying selected subterms.

## Stable finite execution and full caller receipts

TargetWorkerCompletion derives five stable bounds from every finite current
Operand, Fold, and Target graph. It also proves successful execution stable
under larger bounds without heap or semantic premises. Two successful runs
from one entry have the same result, full checked state, and merge memo.

TargetWorkerActual.verified derives the complete existing target receipt
and ProbeHeap for a supplied successful literal return. Its finite theorem
constructs both the graph and stable literal execution from initial selected
support. caller and caller_finite derive the full outer Post at the computed
next inventory. They retain both outer result families and the fourth memo.
The target language law is common selected-subterm inclusion on proper paths,
not exact language equality.

SharedTargetWorkerCompletion derives stable literal Force and Leaf bounds
from their finite current graphs. SharedTargetWorkerActual.force_finite and
leaf_finite construct those graphs from initial class support. Their results
retain the same actual returned receipt, slots, merge history, closed output,
and probes. Supplied successful force and leaf returns also derive their own
receipts. Fourth correctness follows from the same receipt's physical effects.

Global query receipts are constructed logical read evidence. These workers
do not execute concrete host global-query tables. Initial warm invariants,
selected domains, and reached machine checks remain explicit.

## Validation and preservation

The full pinned Audit passes 2425 jobs and 57723 theorem dependency checks.
Only propext, Classical.choice, Quot.sound, and the old unused-input warning
remain. New modules have no warning. Public signatures, axiom reports,
integration kernels, independent reviews, frozen sources, and raw logs are
in lean/restart-evidence/20261016-current-target-worker/.

The interned core and all Haskell package source bytes remain unchanged.
Reuse the strict Nix build, 788 examples plus golden, 15-file Fourmolu, and
four-package Cabal-gild/metadata checks from the preceding source refresh.
Each later Haskell fix must first enter root FINDINGS.md with its failure,
reproducer, files, commit, checks, and upstream status.

## Next dependency and full objective

Implement literal checked structural EditNode, EditChildren, and EditRows
using the shared leaf worker. Preserve selected path positions, unrelated
open siblings, actual Head exposure, and returned states. Same-length
setChildren uses raw interning and the original full guard. Then implement
the compiled class edit and right-folded class pass, with only class-local
slots reset. Read checked-edits-next.md in the evidence directory.

Dynamic conjunction, Scan, local child reduction, parent construction, and
the outer two-family worker follow. General constrained outer termination,
unequal-length path classes, and repeated-pass convergence remain open.
The public reducePartially operation performs one pass. All frontend and
generator adapters, separate Sized contracts, host containers, lazy forcing,
publication, identity lifetime, concurrency, machine bounds, solver IO,
random draws, callbacks, codecs, and older constructor/equality targets
remain active. Preserve the optimized interned core and every local proof,
counterexample, repair, and draft. This checkpoint is progress.
