# Joint finite witness: exact goal and current proof boundary

Recorded: 2026-11-15 02:54 CET.
Status: SOURCE AUDIT ONLY. No new theorem or compilation credit.
No Haskell source, runtime, live Lean source, Git state, or board changed.

## The full target is still a specification

`ORIGINAL-RELATION-TARGET.md` is an exact copy of:

`lean/restart-evidence/20261114-shared-child-resources-and-atom-steps/runs/mcfta-same-branch-clear-causal-review-20261114-1659/RELATION-TARGET.md`.

Its first status is **SPECIFICATION ONLY**. It supplies no checked trace datatype.
I found no live Lean declaration that packages its full existential conclusion.
The precise target is not a theorem named `accepted_initial_identity_emitted_history`.
That checked declaration has a resource conclusion. Do not count its name as a
joint-model proof.

For EACH actual emitted occurrence of the original accepted-source invocation,
construct ONE `rho : Nat → Language.Term Symbol`. Its terms are finite. Require:

1. `EnumerationCorrectness.Satisfies` at the actual output core, under the actual
   output native language and residual-guard meaning. This includes every stored
   domain and fragment equation, UF alias, retained suspended path, and residual.
2. For EVERY historical removed bucket on that occurrence's own derived branch,
   EVERY indexed original suspended occurrence, and EVERY represented path `p`,
   `(rho historicalTarget).atPath p = some (rho sc.var)`.
3. The SAME `rho 0` belongs to the SAME original native root. The actual partial
   root readback `Completes` to `rho 0` under that same assignment.

The source, original root, identity narrow, Unit metadata, empty catalog,
`noStop`, default order, original supplied work fuel, recursive depth, and
original budgets remain fixed. Keep output occurrence indices and duplicates.
Keep earlier outputs when a later alternative stops. A successful larger-fuel
family cannot replace that supplied-fuel obligation.

The full target also retains typing/depth adequacy and completeness, both LPO
and preprocessing language directions, exact stream order/multiplicity/demand,
exact accepted node-count classes, counts/weights/training, both rank inverses,
host bounds, and compiled Haskell correspondence. This audit closes none of them.

## Exact existing interfaces

All paths below are relative to `/home/tritlo/Code/mcfta`. `SOURCE-PINS.json`
records the inspected bytes. Public source declarations retain their own namespace.

| Exact declaration or target | Path and starting line | What it supplies |
| --- | --- | --- |
| `MicroCFTA.SourceSynthesisCurrentProgramEagerResources.accepted_initial_identity_emitted_history` | `lean/MicroCFTA/SourceSynthesisCurrentProgramIdentityEagerResources.lean:42` | SAME accepted initializer/build, native Context, Program roles, initial Packet, fixed resource forecast, stable `bound + extra` worker family, emitted pending references and stratification. No existential assignment. |
| `MicroCFTA.SourceSynthesisCurrentProgramEagerOutputs.accepted` | `lean/MicroCFTA/SourceSynthesisCurrentProgramEagerOutputs.lean:44` | Actual partial readback, all its resource/frame receipts, one Program projection, conditional `Satisfies → Completes`. No finite Type assignment. Its worker uses the real narrow; it is not a replacement identity execution. |
| `MicroCFTA.SourcePruningEnumerationRecursion.clear_satisfies` | `lean/MicroCFTA/SourcePruningEnumerationParkedLanguage.lean:19` | Exact SAME-assignment equivalence across the actual bucket clear. Header copied here. |
| `MicroCFTA.SourcePruningEnumerationRecursion.checkRepeated_true_satisfies` | same file, line 68 | Exact true-check variant. Header copied here. |
| `MicroCFTA.SourcePruningEnumerationSharedBucketWriteToClear.written_bucket_removed_after_finalize_callback` | `lean/MicroCFTA/SourcePruningEnumerationSharedBucketWriteToClear.lean:42` | Actual incoming write → finalization → Left callback → SAME-raw-target parked clear. Exact full removed list, representative paths, indices, duplicates and actual configured continuation. Header copied here. No intervening-task or model theorem. |
| `MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.prepared_terminal_child_written_path_origins` | `lean/MicroCFTA/SourcePruningEnumerationPreparedSharedWrittenPathOrigins.lean:62` | Each written occurrence/path comes from the exact parent descent, fresh own suspension descent, or exact indexed older stored bucket. Successful terminal child only. |
| `MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_terminal_observer` | `lean/MicroCFTA/SourcePruningEnumerationSharedChildTerminalObserver.lean:28` | Actual final/read UF aliases imply original EMPTY-path terminal Holds under a supplied UF assignment observer. No assignment construction. |
| `MicroCFTA.SourcePruningEnumerationFinalize.written_semantics` | `lean/MicroCFTA/SourcePruningEnumerationFinalizeLanguage.lean:20` | Written state is equivalent to the neutralized state plus the actual filled-fragment equation. Does not restore the old pending native restriction. Header copied here. |
| `MicroCFTA.SourcePruningEnumerationPartialOutput.rootPartial_complete` | `lean/MicroCFTA/SourcePruningEnumerationPartialOutput.lean:159` | Finite partial rendering under Safe/Stratified/root allocation, with conditional SAME-assignment completion. Header copied here. |
| `runEager_identity_emitted_resources_at_any_budget` | `lean/restart-evidence/20261115-actual-source-origin-controlled-repair/ANY-BUDGET-EMITTED-RESOURCES-TARGET-UNPROVED.lean.txt:25` | MARKED OPEN RESOURCE TARGET. Per actual supplied-fuel emitted member, derive `OutputResources`. No proof body, no model conclusion. |
| `identity_prepared_emitted_complete_at_any_budget` | adjacent `MISSING-PREPARED-TARGET-UNPROVED.lean.txt:3` | MARKED OPEN PREPARED RESOURCE TARGET. No model conclusion or proof body. |

`EnumerationCorrectness.Satisfies` is defined at
`lean/MicroCFTA/EnumerationCorrectness.lean:142`. Its two components are
`Fragments.stateSatisfies` and retained `guardsHold`.
`EnumerationState.Suspended.Holds` is defined at
`lean/MicroCFTA/EnumerationState.lean:27`. It quantifies over EVERY represented
trie path. A terminal-path-only statement does not meet this definition for a
nonterminal trie.

The older legacy `run_finite_complete_resources_render_sound` in
`SourcePruningEnumerationFiniteHistoryRendering.lean:31` requires legacy resource
history, discharged output, checked rendering and residual success. The legacy
prepared finite-history soundness theorem similarly requires discharged output
and a supplied output model. These checked conditional results do not supply
the optimized shared partial-output witness.

## The precise semantic use of the new causal fragment

The checked write-to-clear receipt gives the actual intermediate state `resolved`,
representative `found.representative`, and full bucket `incomingScs ++ oldScs`.
It gives BOTH the exact stored slot and an actual `Success (setValue ...)`.
Therefore `clear_satisfies` applies immediately, with no extra resource theorem:

```text
Satisfies language meaning rho resolved
  iff
Satisfies language meaning rho checked
  and every sc in incomingScs ++ oldScs Holds at rho found.representative.
```

This is an exact existing conditional equivalence, not a witness construction.
It cannot be used by choosing independent witnesses for its two right-hand
conjuncts. A backward whole-history proof must retain one rho across every clear,
allocation, alias, native restriction, finalized fragment and residual.

The actual prepared terminal-child write has the exact list:

```text
nonterminal(descend position parentBucket)
++ nonterminal(descend position(suspendedVars captured.core.counter tries))
++ oldScs.
```

Here `nonterminal` is the literal filter `fun sc => !isTerminal sc.trie`.
The terminal observer processes the complementary terminal partition of the
child input. It therefore does not supply the proper-path restrictions that the
incoming write stores and the later clear removes. The old bucket is also not
replaced by the newly descended bucket.

The path-origin theorem gives exact raw variables and `position :: path`
incidence. It does not prove those equations true. Equal tries or recursion
keys cannot identify the target UF class. Finalization gives a fragment equation
but neutralizes the captured pending slot. It cannot supply old parent bucket
Holds or the removed native domain without a separate semantic proof.

## One concrete next semantic target

Target the actual proper-path case of this literal write/finalize/clear segment
inside an actual original-source emitted branch. The desired producer must
construct ONE finite rho that satisfies the actual output core AND the exact
removed `(incomingScs ++ oldScs)` proper-path occurrences. Preserve all previously
removed occurrences under that same rho. Retain SAME original-root acceptance
and actual partial-readback completion in its final composition.

The conclusion must be existential. Do not assume a model of `resolved`, a
model of the output, a compatible substitution, a future finite witness, or a
universal `postModel → removedHolds` premise. The next implementation must derive
both the segment's branch membership and its grounding from actual source calls.
There is no checked full-history datatype in the inspected goal interface, so
this paragraph is a semantic proof obligation, not an invented Lean declaration.
A local producer for one actual removed proper-path occurrence would be useful;
it must state honestly which other domains/history it also preserves.

The exact missing local construction is simultaneous finite grounding of the
cleared target and the original raw target at its represented proper path,
compatible with the actual native domains, final fragment equations, all aliases,
older bucket occurrences and residuals. Existing receipts retain the required
identities but do not establish that this joint constraint system has a finite
model. No source-reachable failure is established by this audit.

## Is the full worker-resource induction a prerequisite?

Not as a logical dependency of the semantic case. The new actual causal receipt
uses `UnionFind.Total` and literal call observations. `clear_satisfies` uses only
the exact slot and clear. Neither requires a common-bound worker completion,
`Fits`, the global source forecast, or every SourceTask Current case.

The full resource induction remains important work. Its actual past SourceOrigin
and captured FrameLedger provide a route to the required whole-execution source
and callback coverage. It must still derive current resources for every reachable
task, every output occurrence, restored sibling scope and stopped prefix. The
current resource interfaces contain no common rho or removed-obligation Holds.
For example, `IdentityActualSourcePoint.Inputs` and `IdentityActualSourceCurrent`
in the pinned owner contain Packet, Keeps, TupleInputs, pending bounds, Fits, Heap
and reservation. They do not assert finite satisfiability.

Semantic work can proceed in parallel on actual supplied-fuel observations with
locally derived Context, identity/path incidence and causal membership. Completing
all quantitative resource cases cannot establish finite model existence by itself.
Conversely, a local semantic case does not close whole-worker coverage. Keep these
two missing results distinct in the checkpoint and FINDINGS.

The checked zero-depth theorem says accepted current sources emit nothing at
recursive depth zero. The concrete accepted empty native root also emits nothing
at every depth. Neither frontend acceptance nor its empty native root is an
emitted counterexample. Finite productivity for positive-depth emitted Type
constraints remains separate from partial-render termination.

## Boundaries of this packet

Only this new evidence directory was written. Exact copied headers have no proof
bodies. Original target bytes are unchanged. No live proof or Haskell fix is
claimed. `HANDOFF.md` and `FINDINGS.md` have a 01:28 prefix in the inspected bytes;
Root reported newer checked resource cases at 02:33. Those newer local checks do
not change the existential gap described here.
