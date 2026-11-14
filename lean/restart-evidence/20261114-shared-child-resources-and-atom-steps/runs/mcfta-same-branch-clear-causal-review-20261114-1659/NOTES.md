# Same-branch ancestry, actual clear, and the earlier Left callback

Status: SOURCE REVIEW with three UNCOMPILED proof candidates. No accepted-source
execution with a true-clear was constructed. The branch below is a symbolic
case of the actual definitions. It is not a reachable counterexample. No
Haskell defect or fix was established. No compiler, live write, Git, board,
or child task was used. The prose uses the clear-writing skill.

## What the actual branch does

An earlier expansion and a later true-clear are separate events. A true-clear
does not invoke a Left callback for the slot it clears.

1. SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, lines43-62, reads
   the selected bucket and runs the actual checkRepeated. On its false branch,
   it proceeds through actual narrowing and the Right callback. The current
   identity policy and empty catalog keep that callback pure.
2. SourcePruningEnumerationEntry.enter, line16, reads the pending handle and
   representative. At a recursive boundary it sets expansionAncestry to
   eraseDups(recursionKey handle bucket :: recursionAncestry target). The state
   stores the key, but no old target ID, bucket, alias map, or expansion receipt.
3. During that expansion, fresh own-class variables and shallow children inherit
   the active keys. EnumerationState.inheritAncestry, line126, unions them into
   a slot's history. EnumerationState.allocate, line132, calls that operation.
   EdgeInputs.children, line15, retains actual suspended target IDs while it
   descends their tries and adds fresh own-class targets. This richer incidence
   information is in the bucket and fragments. It is absent from the key.
4. Actual SharedIncomingNode.run, line41, invokes the common IncomingNode.finish
   helper after its actual shared native query. That helper writes incomingScs
   ++ oldScs and calls inheritAncestry at the actual representative. Actual
   SharedDispatch.afterQuery, line36, invokes the common Assimilation.finish
   action. That action writes sourceScs ++ targetScs, eliminates the source,
   and unions both histories at the target. These are the actual shared routes.
   The common write helpers do not retain a map to an old expansion instance.
5. SharedChildVisitors.visitCapturedWith, line80, performs actual finalization.
   Finalize.run, line24, stores the completed fragment and clears only the active
   expansionAncestry. Per-slot recursionAncestry remains. SharedReceiptContinuation
   then invokes the actual prepared hook for that complete receipt.
6. SharedPreparedRecursive.continueWith, line74, runs recordTypes with Left
   fragment. recordTypes_empty, line84, shows that the current graph [] callback
   returns false and updates metadata only. It does not read a model, reconstruct
   removed constraints, or test the ancestry key. The recursive call retains the
   same native caller and query memo and receives the actual returned core.
7. A later selected boundary can take checkRepeated's true branch, line17.
   It resolves the current representative, tests key membership, and writes the
   same handle with bucket[]. SelectedStep then emits its .parked observation.
   ParkedRestart.adapt rebuilds the indexes. Restart.run, line27, preserves the
   exact metadata and state unless its decision is stuck. resumeWithNarrow,
   line39, recurses directly on the parked result. It performs no Left callback,
   new entry, fragment construction, or removed-Holds check for this slot.

Steps1-7 describe one possible control-flow lineage. Their source conditions
have not been produced together from a concrete accepted input.

## Which checked producer supplies the old expansion instance?

No inspected producer supplies that instance together with its target/alias
incidence. Entry.enter_history exposes the actual insertion and keeps complete
per-slot histories. CachedOrdinaryAncestry.prepareOrdinary_ancestry exposes
fresh inheritance. CachedAssimilationAncestry.finish_ancestry exposes source
history transfer. AncestryExtension.Extends exposes retained membership.
KeyAncestry and PathKeyAncestry bound only the stored key's path shape.
None of these conclusions names an earlier entry's target, removed bucket,
fragment, callback, or a substitution that fits later domains and aliases.

A stronger key-provenance certificate could record the exact insertion event
and each concrete transfer to the later representative. That would be a useful
first causal result. It would still need a finite compatible assignment.
The semantic relation cannot be inferred from equal keys alone.

The implementation's recursionKey retains a handle and a set of trie shapes.
It forgets each trie's equality-target ID and the incidence of duplicate shapes.
The small key-only example [(p,a),(p,b)] versus [(p,c)] has equal keys. It need
not have a bijection between its target IDs. This is an algebraic key example,
not a source-reachable trace or a no-finite-model claim. A bijection alone would
also need to preserve target domains, alias classes, fragments, and residuals.
Equating the old and new expansion roots is not an appropriate general premise:
a later occurrence can be a proper descendant of the earlier stored fragment.

## Checked laws do not construct the missing assignment

checkRepeated_true_satisfies, ParkedLanguage line68, gives a SAME-assignment iff.
It requires all removed Suspended.Holds in the reverse direction. The candidate
checkRepeated_exists_satisfies_iff moves the quantifier correctly across that
iff. It creates no model. The candidate recursionKey_retarget proves that changing
all target IDs leaves the key unchanged. The candidate resumeWithNarrow_parked
exposes the direct parked recursive call. All three candidates remain UNCOMPILED.

The earlier callback's empty-catalog exactness does not supply missing target
incidence. An initial model cannot be assumed: firstOrderRaw acceptance is a
construction receipt. An arbitrary post-clear model cannot be extended by a
universal removed-Holds inference. A future branch certificate cannot be added
as an input to the source theorem. RELATION-TARGET.md states the required derived
causal relation and existential obligation without inventing a checked trace API.

## Matching Haskell operations

Enumeration.hs recursionKey, line287, uses nodeIdentity and the HashSet of tries.
inheritAncestry, line407, transfers the active keys. mergeNodeIntoUVarVal, line516,
merges the actual bucket and inherits keys. assimilateUvarVal, line490, transfers
source ancestry after the actual pending-slot merge. enumerateOutUVarWith,
line889, records the key, stores the produced fragment, and resets active ancestry.
enumerateUntil' true-hit, line1006, clears the bucket and recurses before the local
continue function that invokes Left oracle. orderedPrepare, line1542, also clears
and recurses. Its matching comment motivates repetition but supplies no proof
about current equality targets. These are read source correspondences only.

Generated-Type closure, finite productivity, joint consistency, and the full
original-root witness remain open. No original scope clause was removed.
