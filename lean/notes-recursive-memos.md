# Actual source gate memos through recursive equality reduction

Proofs: `29ce7e5c` and `51f5f888`.
Source: `TharkunAB/cfta`, `origin/main` at `c351674e`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.
Read [the checked worker proof](notes-checked-recursion.md) and
[the upstream Sized comparison](notes-canonical-upstream.md).

## Closed warm gate inputs

SourceClosedGateMemoNodes lifts actual complete source gate node traces.
Closed available inputs cannot take the open-binder unfolding branch.
The unfolding memo stays unchanged. Each reached Mu still executes the
actual predicate memo lookup or insertion. Coherent residency identifies
the exact immutable input on hits. The returned predicate memo is correct.
Actual ordered child and edge scans retain their short-circuit behavior.
The proof needs physical record facts, availability, and closure. It needs
no unfolding-cost heap or original source construction history.

SourceClosedGateMemoSelection lifts actual child, path, and class traces.
Later false paths and later classes use the returned predicate memo. A true
path stops its class. The complete selection retains the original child
list and constructor heap. Both source memo call graphs are explicit.

## Concrete local equality prefixes

SourceEqualityClosedMemoReads.StageReads uses the actual selection graph.
It retains both initially empty source memo tables, the unchanged returned
unfolding memo, the returned predicate memo, coherence of both tables, and
the exact unchanged selection heap. PassReads records the actual source
precheck branch. EdgeReads retains actual physical payload readback and
the complete native pass. The pass and edge theorems derive these receipts
at any closed warm physical scope. No future heap premise is supplied.

The older SourceEqualityOnePassSource.StageMemos includes complete gate
readiness, with an unfolding-cost heap for open calls. This new certificate
does not assert that extra invariant. It proves the concrete memo calls
and table coherence needed for closed recursive calls. Older certificates
and proofs remain unchanged. No cost heap is inferred from IdleReady.

## Complete recursive graph and public entry

SourceEqualityPartialMemoGraph indexes the existing actual node, row, child,
and indexed walk graphs. Every row retains its exact local EdgeReads plus
the actual child and tail memo receipts. It introduces no language law.

SourceEqualityPartialMemoCases derives each later scope from actual native
effects, the proved completed child effects, and literal edge construction.
Earlier row and child availability passes through the exact returned
histories. SourceEqualityPartialMemoProofs.node performs the complete mutual
graph induction. Its checked theorem derives the graph and all these memo
receipts from actual bounded worker success and its reached-check plan.
It assumes no global Callback, recursive memo law, or future heap invariant.

SourceEqualityPartialMemoSource.public_exact composes both actual memo
receipts with public language and stable full-state replay. It also retains
native readiness, normalized annotations, both filtered probes, availability,
closure, and histories. closed derives the initial scope from actual
original normalized closed source construction. Every checked successful
public entry therefore has the complete result without a supplied graph.

## Validation and next target

All seven new modules pass focused builds. The aggregate audit passes
1,857 jobs and 48,168 dependency checks with only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-recursive-memos-20261015-audit.log`.
All older proofs except audit imports, counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged.
No Haskell source changes after the upstream checkpoint. Its 650 examples
and formatter checks were not repeated.

General outer success and finite execution remain unproved. Start with
finite single-pass existence for equality-free ordinary regions above
opaque Mu and union boundaries. Use the actual empty precheck, physical
payload combination and descent, literal edge requests, and smaller
structural child calls. Carry returned scope and histories. Then study the
general selected-narrowing case with a valid measure or a focused
counterexample. Native intersection can increase ordinary depth.

The outer reduction memo table, open contexts, repeated fixed points,
getAllAtPath, native containers, GHC lazy scheduling, and extraction remain
separate. The source gate receipts do not prove these statements. Keep
Sized exact classes, finite size execution, size order, and both rank
inverses unchanged. No Lava or Rocq dependency is added.
