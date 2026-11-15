# Parked class isolation through actual shared operations

Date: 2026-11-15 04:42 CET.
Status: NEW UNCOMPILED CANDIDATE. Root owns validation and publication.
All source paths below are relative to the repository root.

## Answer and exact boundary

Existing proofs support the proposed isolation strategy along one actual
branch. They do not yet prove it for every later supplied-budget Source step
and every retained outcome. Several exact shared primitives already exist.
The new candidate removes a real input-separation premise at one actual
prepared shared child call. It does not claim the full worker invariant.

The branch qualification is essential. At
`SourcePruningEnumerationSharedSelectedContinuations.lean:619`,
`NativeContinuations.run` invokes the head continuation on its returned cache,
then runs sibling alternatives from the SAME captured `before` cache. It
threads only the returned native caller and queries across that sibling cut.
A class allocated or parked in the head continuation need not exist in the
restored sibling cache. An all-later-steps assertion over the whole invocation
does not follow from state-local isolation. Each output needs its own causal
history. Earlier outputs remain relevant after a later stop.

## Existing exact producers; do not duplicate them

`EnumerationDischargeHistory.IsolatedPending held handle state`, in
`SourcePruningEnumerationIsolatedPending.lean:20`, contains:

- `held` remains a UF root;
- its exact stored payload is `.unenumerated (some handle) []`;
- every stored suspended reference avoids its current class.

It does not state full semantic validity or preservation of the class's
complete pre-step membership. That latter fact is `EnumerationDriver.Protected.classes`.

`SourcePruningEnumerationCreatedIsolation.lean:23`
(`checkRepeated_created_isolated`) derives isolation from the actual true
recursion check plus Ready and IncomingAvoid. The packet-level
`packet_parked_created_isolated:104` derives those facts from actual selection
and retains the real read/check/cache-adaptation equations. Thus creation at
an actual selected clear is already proved.

`SourcePruningEnumerationIsolatedBoundary.lean:20`
(`IsolatedPending.disabled`) proves that the exact native boundary has
`expandable held = false`. `packet_restart_ne:81` derives a different selected
target from the actual restart equation. It needs the original handle's real
lookup and a recursive-boundary proof. Native Post/Keeps receipts must retain
that readback at later callers; slot identity alone does not prove it.

`SourcePruningEnumerationIsolatedPrefixOperations.lean` already handles real
reads, another clear, another handle write, and actual nonempty preparation.
`IsolationReads` handles entry, row entry, and recordTypes. The same raw held
root and handle remain explicit in these statements.

The shared terminal source has genuine current-backend observers:

- `TerminalPrefix.run_isolated`, in
  `SourcePruningEnumerationPreparedTerminalIsolationOperations.lean:22`, uses
  the actual prefix success at its original fuel. It proves isolation, excludes
  the held root from recorded sources/winner, and preserves its complete class.
- `SharedFoldState.dispatch_frame:69` and `run_state:149` describe the actual
  shared dispatcher/fold state. The forest stays fixed. `dispatch_allowed:217`
  and `run_allowed:235` preserve the fixed allowed-reference predicate.
- `SourcePruningEnumerationSharedChildIsolation.observed_isolated_pending:302`
  uses the literal supplied-budget shared ChildDispatch singleton and its actual
  cache. It includes terminal prefix, shared rawFold, and shared incoming
  execution. Safe, bounded inputs, IsolatedPending, and input Avoids are its
  premises. There is no later success, semantic model, or capacity supplier.

The shared child file also contains private exact observers:
`shared_fold_observed_isolated_pending:55` covers EVERY fold result tag and
its returned outer Core, including native faults and rejection.
`shared_incoming_observed_isolated_pending:154` covers the actual incoming
read endpoint for EVERY result tag and any successful returned singleton.
They use the literal shared backend. They are not legacy dispatcher results.
Root may export an existing helper if needed. This packet does not copy it.

The public shared child conclusion retains IsolatedPending only. It does NOT
retain `Protected.classes` from the complete child call. The internal proof
has the necessary terminal-prefix class exclusion, shared-fold forest equality,
and incoming compression facts, but the public conclusion drops the final
class equivalence. Do not infer that equivalence from IsolatedPending alone.

## New actual source input producer

The candidate theorem is
`SourcePruningEnumerationPreparedSharedChildIsolation.prepared_stored_child_isolated`.
Its inputs retain:

- the actual stored parent bucket at the captured Core;
- the same original isolated raw root and handle;
- literal `CachedOwn.prepare` success with its exact staged list/cache;
- an indexed staged child occurrence;
- the literal shared ChildDispatch singleton at that OWN cache, with unchanged
  supplied `r n p h k`, caller, queries, returned Core, outer Core, and cache.

It has NO input Avoids premise and NO future provider.

`prepare_scalars` supplies the actual suspended-state endpoint.
`suspension_protected` preserves every member of the old held class through
fresh allocation. `suspension_allowed` retains no incoming stored SC target.
The exact stored parent payload derives its own avoidance from IncomingAvoid.
`fresh_avoids` proves that every fresh own target avoids the old class.
`prepare_inputs` and the indexed list observation identify the complete child
bucket as the inherited descent plus the fresh own descent. `descend_avoids`
retains both exclusions. No equal-trie-to-target identification is used.

The proof also derives the child's real bounds from the stored parent bounds,
fresh allocation bounds, and the actual own counter. It then uses the existing
public shared child observer at the SAME supplied budgets and endpoints.

The conclusion contains complete class protection through the own prefix,
IsolatedPending at own, actual child-bucket avoidance, and IsolatedPending at
the actual returned child cache. No new primitive implementation is added.
It does not yet claim complete held-class equivalence across that final child
call, arbitrary later siblings, or every rejection/stop cache.

## First missing actual-step coverage

1. Publish a shared-child observation of `Protected.classes` for an excluded
   isolated held root at the ACTUAL returned singleton Core. The source proof
   should compose the existing prefix class law, fixed shared-fold forest,
   and real incoming compression. The current public isolation projection
   alone is insufficient to claim that no new variable merged into that class.
2. Extend the cached shared child observation to every retained empty/rejected
   cache. A concrete first case is
   `SharedCachedTerminal.incomingCacheAdapter` with raw `[]` and `some after`.
   `SourcePruningEnumerationIncomingCacheAdapter.adapt:22` writes a native
   empty sentinel at its actual target and appends supplied references there.
   Its cache is not simply the unchanged outer read Core. The actual excluded
   target and input-origin laws must protect held in that cache as well.
   Fault/unsupported paths without a retained cache do not create a next-state
   obligation, but their native endpoint and earlier outputs must remain exact.
3. Compose these local effects through actual tuple tails, rows, selected frame
   returns, finalization, callbacks, restart, and native Post/Keeps history.
   Deferred bucket inputs need a source origin or frame relation. IncomingAvoid
   quantifies only the CURRENT store; it does not itself quantify an arbitrary
   bucket captured in an earlier continuation. Restored sibling snapshots need
   branch-local histories rather than one global chronological state chain.

Private owner helpers `child_inputs_isolated_pending:1203` and
`finalized_child_inputs_isolated_pending:1231`, in the current
`SourcePruningEnumerationSharedEagerReservation.lean`, already compose isolation
from genuine ChildInputs protection/reference effects. Do not replace closing
the actual SourceTask cases by assuming ChildInputs for every future step.

These are proof boundaries, not an accepted-source failing trace.

## What a temporal dependency order would and would not prove

With complete same-branch preservation, a later cleared owner and all its
bucket targets avoid every earlier isolated owner class. Historical owner
dependencies then point toward later owners. Reverse chronological assignment
construction can keep later chosen pending values fixed while it reconstructs
an earlier owner. This is a concrete benefit for the main witness proof.

It does NOT prove that the earlier bucket can be realized with those fixed
later target values. Equal path positions need equal endpoint values. Nested
path positions need genuine subtree compatibility. In particular, UF-equivalent
targets at strictly nested paths remain impossible even if every owner-to-target
edge follows an acyclic temporal owner graph. A bucket can impose such an
internal obstruction without a cycle between cleared owners.

The checked prefix-free-arrow construction currently assigns `var1` to all raw
targets. Reconstructing an old owner with prescribed later target values needs
a more general simultaneous leaf construction and target/path compatibility.
Temporal isolation is not a substitute for that missing constructive step.

Stored expanded fragments can contain holes for isolated pending roots.
Residual obligations can also contain such fragments. IncomingAvoid excludes
stored SC targets; it does not exclude those fragment dependencies or prove
residual guards after reassignment. Fragment reconstruction and source residual
coverage need their own producers. Closed native handle membership at every
pending slot also remains separate.

Keep the original full goal: ONE finite accepted completion of the SAME emitted
original root, with ONE assignment satisfying supported domains, aliases,
retained paths, residuals, readback, parked backward recompletion, and EVERY
historical removed occurrence on that branch. Preserve duplicate indices,
original budgets/noStop, all outcomes, and outputs before a later stop.
The full goal remains OPEN. No Haskell change or defect is established.
