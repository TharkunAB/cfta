# Ordinary typing, terminal support and actual reached head

All four source modules pass strict checking. Embedded notes retain proposal-time
wording where present. This header and checked.json state current results.
No production Haskell or Liquid Haskell file changes.


## ordinary-typing-note.md

# Independent ordinary synthesis typing foundation

2026-11-12 07:13 CET. Owned new source: `lean/MicroCFTA/SourceSynthesisOrdinaryTyping.lean`, 129 lines / five public laws. Import: `MicroCFTA.SourceSynthesisTypeSubstitutionWitnesses`. Reuses existing raw Ty, Library, Query, Program, simultaneous substTy, and rigidTerm. No compilation, Git, old-source, root-document, evidence, Haskell, or subagent actions. Frozen for Root strict verification.

Definitions in `MicroCFTA.SourceSynthesisOrdinaryTyping`:

- `normalizeTy` normalizes ONLY the documented TCons Fun with exactly two arguments to tFun, recursively. Other constructor tags and arities remain ordinary raw types. Raw TVar and TCons tags stay distinct.
- `Equivalent first second` means their normalized raw types are equal. It is independent of native Term equality. The false converse from rigidTerm equality is not claimed.
- `queryLookup arguments name` uses List.lookup on the reversed actual association list. It chooses the last matching query binding. It applies no raw substitution to that binding.
- `Typed lib query program typ` has exactly five constructors: group instance with per-occurrence rho; argumentOnly instance with per-occurrence rho; rigid queryArgument lookup; ordinary application; conversion under Equivalent. No new Program AST is introduced.

The ordinary judgment contains no TypeIn, AliasSafe, constructorCatalog, pruning, role flag, component count, required-argument token count, source winner, source permutation, source result equation, source typing derivation, or automaton membership premise. The argumentOnly ordinary rule does not limit its syntactic position. Source role checks remain an external admission condition. Each component occurrence supplies its own rho; no library-wide monomorphic substitution exists.

Public laws:

1. `rigidTerm_normalize typ`: rigidTerm (normalizeTy typ) = rigidTerm typ. Structural Ty induction handles raw arrows, Fun/2, all other constructor arities, and their actual child order.
2. `equivalent_rigidTerm first second same`: ordinary equivalence implies equal rigid encodings. This direction has no AliasSafe or universe hypothesis. Reflection is deliberately absent.
3. `funAlias_equivalent argument result`: literal Fun/2 is equivalent to the corresponding raw function type.
4. `queryLookup_member arguments name typ found`: a successful ordinary last lookup supplies an actual input pair. Uses the current public Std List.lookup_eq_some_iff and membership under reverse. It assumes no source selection winner.
5. `Typed.application_funAlias first second`: an ordinary function typed with literal Fun/2 supports application to its ordinary domain. It uses the independent conversion and application constructors.

Scope and semantic choices:

This foundation concerns initial group-representative Programs. Group membership is an overload alternative under the literal representative name. Query lookup uses the last query binding. No local-over-global lexical priority is added between the separate group and query constructors when their String names collide. No claim about the separate Haskell expand/representative operations is made.

The module does not prove every current source result has an ordinary typing derivation. The kernel-checked and now runtime-reproduced reserved variable/constant collision disproves unrestricted encoding reflection on the exported raw API. It does not weaken the public input contract or add a validator. It does not prove ordinary typing implies source admission or full Program completeness.

The next bounded bridge can combine these ordinary constructors and conversion with checked R229 raw instance leaves and R228 rigid query leaves. Per-use original AliasSafe and demanded TypeIn obligations must stay outside Typed. A query leaf bridge can use queryLookup_member for the unrestricted terms pool. A relevant/root bridge still needs actual resolver/winner correspondence and token accounting; the terms-pool membership law does not supply those facts. Reverse source typing needs the separately audited annotation reification, row-origin, lookup, and proper-encoding obligations.

Frozen source SHA256: `7a862339ed0dd29e30ec5fe0e66ec138b50f8994d408809dbc275dc5c1fd50a5`.


## ordinary-collision-note.md

# Independent ordinary typing failure for the executed collision

2026-11-12 07:26 CET. Owned new source: `lean/MicroCFTA/SourceSynthesisOrdinaryTypeCollision.lean`, 98 lines / two public laws. Imports: `SourceSynthesisOrdinaryTyping` and `SourceSynthesisTypeEncodingCollision`. The ordinary foundation passed Root strict checking at SHA 7a862339ed0dd29e30ec5fe0e66ec138b50f8994d408809dbc275dc5c1fd50a5. It remains unchanged. No compilation, Git, old-source, root-document, evidence, Haskell, or subagent actions. Frozen for Root strict verification.

Literal definitions:

- `emptyLibrary` has empty libraryGroups, libraryArgumentOnly, and libraryAvoid; libraryEncoding is firstOrder.
- `badQuery` has f : tFun (tVar a) (tCons B []) and x : tCons var1 []; its goal is tCons B []. These are the actual existing raw Ty and Query records. There is no new Program AST or source model.

Public laws in `MicroCFTA.SourceSynthesisOrdinaryTypeCollision`:

1. `badQuery_untypable (typ : Ty)`: no `SourceSynthesisOrdinaryTyping.Typed emptyLibrary badQuery (Program.app (Program.var f) (Program.var x)) typ` exists. The result holds for every raw result type, not only the query goal.
2. `same_annotation_but_no_ordinary_type (typ : Ty)`: the existing native annotation equality between tVar a and tCons var1 [] holds together with that independent ordinary typing failure. This reuses the checked R229 `reserved_variable_constant_collision` law.

Private proof structure:

- Compute the two ordinary last query lookups from the literal input.
- `variable_origin` inverts a Typed derivation at any variable. Empty library rules have impossible membership. The rigid query rule supplies its actual binding. Conversion composes raw normalized equality. Application cannot produce a variable Program.
- `no_bad_application` inverts an arbitrary typing derivation whose Program is the literal f x. In its application case, variable_origin supplies the rigid f and x types. Normalizing the function forces normalizeTy domain = tVar a. Normalizing the argument forces that same domain to equal tCons var1 []. The existing raw-constructor mismatch is a contradiction. Conversion preserves the Program and delegates to its induction hypothesis.

No encoding reflection, source membership, source result equation, TypeIn, AliasSafe, source role, pruning, relevance token, winner, or future semantic supplier occurs as a theorem premise. Native annotation equality is used only to report the combined counterexample. The untypability proof uses raw normalized types and query lookup.

This connects the concrete executed output, separately retained by Root in FINDINGS and the R229 packet, to the new independent ordinary typing specification. This source does not prove the Haskell runtime result itself or an end-to-end runtime correspondence theorem. It does not add an API restriction, change the public input contract, or repair production Haskell.

Frozen source SHA256: `459befcd1a51f8c885d32723327abc244460e9d644dffa26276b5d14fdf382cd`.

Focused first-check repair: explicitly unfold List.lookup in the literal f lookup, because the default simp set stopped at the first nonmatching x binding. The typed inversion and contradiction proof produced no further errors. No theorem header, hypothesis, lint, or limit changes. Frozen for Root recheck.


## generated-terminal-projectable-note.md

# Generated native terminal support

Status: source frozen for ROOT's strict compiler. This worker did not compile.
Owned new source only:
`lean/MicroCFTA/SourcePruningEnumerationNativeGeneratedTerminalProjectable.lean`
(144 lines), importing the frozen R229 generated-prefix module.
SHA256: `104bb675646f8b769ac9e17c2012d46dbcdf60e9886605a64a47d53525292feb`.

Public namespace:
`MicroCFTA.SourcePruningEnumerationNativeGeneratedTerminalProjectable`.

- `node_query_outcome_projectable` (97).
- `edge_query_outcome_projectable` (113).
- `body_outcome_projectable` (129).

Each law takes current Good, current support Heap, the physical InputsThrough
plan of the SAME finite execution, and its literal observed execute equation.
Body also takes its current resident operands. Each conclusion applies the
existing annotation Heap predicate directly to observed.state.native.machine.heap.
The observation retains its full actual native state. There is no replacement
endpoint, future support supplier, or new invariant type.

All five NativeDemand outcome constructors are covered: done, failed,
constraintError, blocked, and yielded (including fuel zero/exhaustion). The laws
therefore complement the earlier successful endpoint laws and cover the exact
error, busy/absent/missing-field, and pending optional-binder caches. They assert
support of those heaps, not successful completion of the observations.

Private terminal_step_heap (29) handles the final non-yielding instruction.
Checked bodies retain the complete native state even if operations change.
Node/edge publication retains the physical heap. Optional binding reuses the
existing predicate-parametric AnnotationStoredSyntax.optionalBinder theorem,
including its actual pending cache. Unchecked Code.work always yields, so it is
excluded from this terminal step argument; no arbitrary-Code work support claim
is made. The node_step_heap helper reused from the arity module is only a physical
heap equality. No Fits predicate is used as support.

Private execute_heap_from_prefixes (64) follows the actual physical execution.
At each yielded instruction it constructs a physical one-step Trace, gets the
supported reached heap from the already-proved generated prefix law, and carries
Good/static physical fields to the next actual state. It composes the actual
Trace for recursive execution. At a final non-yielding instruction it applies
terminal_step_heap. The bounded prefix callback stays private and is supplied
internally by the three closed R229 generated-prefix theorems. It is not a public
future-state premise. The literal execution equation identifies the observed
state in each public result.

No source-shape or state-shape counterexample was found or required. No Haskell
fix or production defect was established. The R229 source and earlier notes
were kept frozen. No compiler, Git, existing-source, root documentation,
evidence, Haskell, or agent changes were made.

Open: transport through all outer parent/local-pass/outer-row producers and
selected exposure histories; every earlier scan hook continuing; sufficient
recursive source depth/common work; full Haskell/runtime correspondence.
The current physical plan is explicit. The laws do not derive that plan or
prove that any incomplete observation eventually completes. The original input
and all alternatives remain the proof objective.

ROOT's first strict pass elaborated both private proofs. It rejected the three
public applications because their control metavariable was unresolved when Lean
checked physical Fields. Each wrapper now passes its literal generated control
explicitly. No public header or premise changed. Frozen for ROOT's focused rerun.


## scan-prepared-head-note.md

# Actual ordinary prefix and its reached selected head

Source frozen after ROOT strict PASS at 2026-11-12 07:31 CET. ROOT verified one public law at the final hash below. ROOT remains the sole serial capped verifier and publisher.

Owned source: `lean/MicroCFTA/SourcePruningEnumerationSharedScanPreparedHead.lean`.
SHA256: `3439c6ac416fdba3c1c4a905980c53bca05db4a4e86a814b885659d3a176b2e1`.
Size: 310 lines, 23231 bytes.

Public theorem:

```
MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources
  .witnessed_prefix_complete_resources_models_work_proper
```

The public header starts at line 46. It uses the complete current input header of `SharedScanModels.alternatives_finite_complete_resources_models`. It adds only the current chosen row/index/readback, captured-cache properness, original assignment origins, pending-size bound, and chosen-edge acceptance. The current readback binder is `selectedAt`.

## Retained packets

The result retains the ENTIRE finite prefix resource/model tuple on `selectedEdges.take index`: one actual bound, processed receipts, outputs, returned caller/inventory/full Memos, result, native running family, Post, current Packet at the original captured metadata/cache, current stage Fits/Heap, length bound, receipt/output certificates, complete-or-stopped shape, and SAME original assignment's model at the returned heap.

The literal full-list append equation retains stopped prefix results unchanged. A completed prefix supplies its actual caller/query to `chosen :: selectedEdges.drop (index+1)`. This equation does not assume that the chosen hook or remaining suffix completes.

Only in the returned completed-prefix implication does the theorem return the selected-head packet. It retains the ENTIRE `CapturedEdge.complete_models_resources_work_proper_progress_prepared` result at the ACTUAL prefix caller/inventory/full Memos: all five native bounds, actual result, returned native endpoint, full global Memos and inventory, roots/cache/resource laws, one extended model, origins, fill equalities, strict pending-size/scalar-work progress, properness, and local non-stuck statement. It additionally composes the head's Post back to the original caller.

A stopped prefix still exposes its full original result, exact outputs, stopped certificate, and optional endpoint alternative. It supplies no claim that the chosen row was reached.

## Construction

The proof calls `SharedScanModels.alternatives_finite_complete_resources_models` ONCE and the selected head model/resource/proper producer ONCE in the completed-prefix branch. The prefix producer already derives the SAME original assignment through `NativeLanguage.satisfies_keeps`; the proof retains that exact returned model. No independent semantic assignment or global memo witness is joined.

The original stored parent remains available at the returned heap by `prefixPost.effects.keeps.available`. `SelectedEdgeAdmission.selected_admission` consumes `prefixPost.context`, whose annotation heap has current normalized/cached equalities. It derives the actual chosen projection, inherited arity, and guard/residual facts from the SAME original assignment and suspended holds. The head consumes the returned Packet's roots, realization, waiting counts and candidate flags. The captured cache remains unchanged, as the actual sibling worker requires.

The current seed is `stage recursiveFuel seed capturedMass inherited index`. The proof derives the exact remaining schedule through `ScanReserved.after_prefix`, then `.head.edge`, using the current edge shape/cost bounds. It does not use a stage-zero reservation for a positive prefix index.

The selected-head result also gives one sufficient common native stage fuel, the sum of the prefix bound and its five head bounds. At every larger native fuel, the SAME actual prefix completes at the retained endpoint and the SAME selected head runs there. The actual hook in the prefix is the source `continueWith (resume ... w recursiveFuel) ... w`, with the same native `w`. This is a common stage budget, not a bound on total recursive runtime work.

## Compiler repairs

ROOT's first strict check reported three unresolved predicates and one append-match conversion failure. The source now opens the existing `EnumerationDependencies`, `SourcePruningEnumerationNodes`, and `SourcePruningEnumerationObservation` namespaces. These opens resolve `PendingRealized`, `InputsPending`, and `PendingFragment`; no predicate or public premise was added.

The append proof now cases the SAME `prefixResult`. In the completed branch it first reduces the constructor-valued outer matches in both the retained append equation and the goal. It then generalizes the SAME actual suffix run in both places and cases that result. The final exact proof therefore compares reduced observations, not two unreduced match expressions that print alike. The first attempt omitted the outer match reduction; ROOT's second focused log identified that remaining step.

The final strict check passed at `3439c6ac416fdba3c1c4a905980c53bca05db4a4e86a814b885659d3a176b2e1`. All public inputs, complete packets, actual caller/query arguments, stop alternatives, and current reservation obligations remain intact. No linter was disabled or check limit changed.

## Limits and dependencies

Direct imports: `SharedScanModels`, `SharedCapturedProgressWork`, `SelectedEdgeAdmission`, and `SharedRecursiveReservationBounds`. The list decomposition uses current `selectedAt` and standard List take/drop lemmas. The output event position binder is distinct from the chosen row index.

A stopped prefix remains an actual possible result. Its receipt/output prefix, failure, certificates, and optional endpoint are retained. The accepting later row does not prove that those earlier hooks complete. The reached-head clause applies only when the internally derived prefix completes.

The selected head has an actual complete receipt and one extended assignment. This theorem does not yet attach that head's actual Left `recordTypes` callback, false verdict, updated refutation, and recursive restart to the same ordinary scan boundary. A later additive cut can use the existing callback producer with this SAME head assignment and final full Memos. Its extra inputs should be only current original `OriginPolicies` and pending refutation. Old-variable agreement and the current captured Packet's pending bounds transfer that refutation. The callback stage must be included in the common native stage fuel; no future callback result or independent head model may be supplied.

The current full ScanReserved input pays the requested bounded recursive depth. It does not prove that this depth is adequate, that recursive calls or all remaining rows complete, or that the entire driver has a uniform native budget. A one-stage reservation is not claimed to pay positive-depth scans. No callback model is attached to the finite prefix's entire recursive output. Whole termination, complete all-row traversal, and Haskell/default eager-order correspondence remain open. No Haskell defect is established.

Only the new owned source and this runtime note were written by this task. ROOT ran the strict compiler checks. This task did not compile or change Git, existing source, root documentation, evidence, Haskell, or subagents. R229 source and its source note remain frozen.


## next-outer-projectable.md (frozen uncompiled next-cut audit)

# Next outer support and physical-plan cut — read-only audit

TerminalProjectable passed ROOT strict at
104bb675646f8b769ac9e17c2012d46dbcdf60e9886605a64a47d53525292feb.
No compilation, Git, source, root-documentation, evidence, or Haskell changes
were made for this audit. The next implementation below is an unproved plan.

## What is closed and what the current caller supplies

OriginalGuardsProjectable.complete derives the actual source expression/build
and whole original physical support Heap from Library, Query, and nonnegative
signed size. The predicate is existing AnnotationHeap.Heap instantiated with
`fun c => exists cs, sourceEqualities c = some cs`. No new invariant is needed.
R229 generated prefix laws and R230 TerminalProjectable cover all physical edge
records after actual generated requestNode/requestEdge/checked-body execution.
TerminalProjectable.node_query_outcome_projectable:97 (edge:113, body:129) still
takes CURRENT Good, CURRENT support, and a physical InputsThrough plan for the
same finite observed execute. Body also takes current EdgeReady operands.
It preserves done/failed/constraintError/blocked/yielded endpoints exactly.

PhysicalExecution.Inputs:47–66 includes constructor operands, current available
optional-binder body, node/edge operands and finite-word request-key safety,
and actual evaluating ownership for finishNode/finishEdge. InputsThrough:216–222
follows only reached controls. Guard support does not establish those facts.
AnnotationHeap.Heap:15 mentions only physical edgeRecords. For example, it can
hold vacuously on an empty edgeRecords table while an external requested operand
is not Available; then InputsThrough 0 for its requestNode fails already at
Inputs. This is a predicate-level separation, not a reproduced source-program
counterexample or Haskell defect. Source production must derive operand residency.

Current Good supplies coherent native state, operation validity, cached resident
fields, and physical readiness. Whole support plus residency gives each row's own
sourceEqualities Some via AnnotationHeap.edge:40. It cannot replace native key
widths or running-cell ownership. RequestBounds.WordRanges:134–136 independently
requires Words at every actual raw yielded prefix. It is explicitly carried in
current TargetQuery admission; do not report it as derived from support.

## The actual query producer already derives the physical plan

TargetQuery.finite:78–99 takes current Ready, inventory At, current operand
Available/closedness, current WordRanges for the actual empty-domain request,
and current global Memos validity. Ready is ClassScan.Ready:110–115, including
.good, semantic/cost readiness, scope, and idle caches. It calls
NativeInventoryState.query_complete:85 once. That result internally obtains the
full successful physical query receipt, Trace, and exact caller/native endpoint.
TargetQuery.Step:32 stores that actual Trace; Receipt:55 retains Step plus Ready,
inventory admission, physical Effects/Extension, Available/closed result, exact
intersection meaning, complete global memo validity, and no-global event history.
The complete receipt must remain one conjunct rather than being projected away.

PhysicalTraceCompletion.Trace.plan:80 proves InputsThrough at trace length+1.
A short induction on the SAME pure-return Trace strengthens this to EVERY finite
fuel: at a cons instruction, zero fuel requires its recorded current Inputs and
successor fuel uses the recorded yielded step plus induction; at the final pure
control, Inputs is True and its next step is done, so no later plan is demanded.
This needs no new current or future support premise, completion supplier, model,
capacity, or machine bound. It does not derive WordRanges. It is a new small
corollary of the existing trace, not an assumption about future physical checks.

## Smallest genuine next theorem

New file SourcePruningEnumerationTargetQueryProjectable.lean, primary node query:

    finite
      (formulas solver inventory left right before)
      (ready : Ready before) (admitted : At ... inventory before)
      (current : AnnotationHeap.Heap (fun c => exists cs, sourceEqualities c = some cs)
        before.native.machine.heap)
      (leftAvailable rightAvailable leftClosed rightClosed)
      (ranges : WordRanges actualEmptyDomainRequest before)
      (memos) (valid : Valid before.native.machine.heap memos) :
      exists next value after count,
        next.source = before.native.machine.heap /\
        next.roots = inventory.roots ++ [left,right] /\
        ENTIRE TargetQuery.Receipt ... next ... value after memos /\
        Trace count actualRequest before (code (pure value)) after /\
        support after.native.machine.heap /\
        (forall fuel, InputsThrough fuel actualRequest before) /\
        (forall fuel observed, execute fuel actualRequest before = observed ->
          support observed.state.native.machine.heap)

Call existing TargetQuery.finite ONCE. Extract its actual Step Trace internally.
Use R229 prefix support for its exact returned heap. Derive all finite physical
plans from that Trace. Use R230 terminal laws for each actual finite observation.
No public InputsThrough/completion callback remains. The only support premise
concerns the literal current entry heap. Existing source completion supplies the
original initial Heap; later state composition remains the next obligation.
The primary node producer is enough for the current empty-domain query route;
a standalone edge producer would require additional source request/admission work.

## Where this connects to outer parent history

SeededWorker.leaf:55–60 executes precisely that empty-domain request and retains
the actual native observation on failure. Its fold:63–69 threads operand and tail
states before leaf. SharedScanWorker.query:67–71 calls seeded at the actual class
entry. Thus finite support can be instantiated at each actual reached leaf; it
must not be assumed at a future fold return. Existing operand/required/exposure
producers must separately transport the current support predicate.

SharedLocalWorker.reduce:134–143 changes operations only before classes; its
unchanged/emptyChildren/error branches keep the same native heap. classes:122–131
can stop before required/pass work and must preserve that exact stopping state.
SharedParentWorker.edge:110–121 rejects raw contradiction immediately or runs
actual local child reduction then checked build:57–62. MkEdge.finite:109 already
constructs the full checked receipt from current fields/readiness/children.
CheckedArity.checked_projected_arity and NativeCheckedProjectable.observed_build_projectable
cover both kept guard and Top/[empty] sentinel. Combine their selected guard fact
with AnnotationHeap.edgeStep/run to preserve ALL old/new record keys, including
canonical hits. Do not infer new-key support from heap extension alone.

Full local scan/pass/required/outer-row history transport is still open. The next
query theorem closes a concrete plan supplier at actual class leaves; it does not
complete that entire induction. Preserve failed/blocked/fuel-stopped states and
full memos/receipts when composing. Every prior enumeration hook continuing,
recursive-depth/common-work adequacy, source roles/sizes, and full Haskell/runtime
correspondence remain separate. Arbitrary Code.work preservation is excluded.


## next-ordinary-callback.md (frozen uncompiled next-cut audit)

# Ordinary reached-head recording and false restart

Read-only audit frozen at 2026-11-12 07:37 CET. The R230 scan-head source is strictly verified. The composition below is a proposed next result, not a verified new theorem.

## Minimal public header

Suggested source module: `SourcePruningEnumerationSharedScanRecordedRestart.lean`.
Suggested public namespace/name:

```
MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources
  .witnessed_prefix_complete_resources_models_work_proper_restart
```

Use EXACTLY the R230 current header of `SharedScanPreparedHead.witnessed_prefix_complete_resources_models_work_proper`, `SourcePruningEnumerationSharedScanPreparedHead.lean:46–88`. Add ONLY:

```
(policies : SourcePruningTemplates.OriginPolicies templates whole)
(refuted : forall group in metadata.pending, Refutes assignment group)
```

Use the canonical `Refutes` notation already used in `SourcePruningEnumerationSharedPolicyPreparedRestart.lean:54–55`:

```
@SourcePruningResume.Refutes Symbol
  (@instDecidableEqProd String FullSyntax.Formula inferInstance
    FormulaExecutable.formulaDecidableEq)
```

Do not add future prefix completion, model, head assignment, refutation, heap, metadata, or callback-result premises. Keep the full prefix/head packets and the current ScanReserved requirement. Do not replace it with a one-stage reservation.

## The prefix-refutation seam is closed

There is no missing prefix-refutation lemma here. The actual sibling worker keeps the captured metadata and cache fixed. R230's actual prefix hook closes over `metadata` (`SharedScanPreparedHead.lean:92–96`), and its returned Packet is literally `Packet ... prefixCaller prefixMemos metadata before` (line 98). Its original assignment is the SAME function `assignment`; the original pending groups are the SAME `metadata.pending`. Refutation does not inspect the changed native heap or memo tables.

Thus `refuted` already proves refutation under the prefix's SAME original sigma. No pending-group or metadata congruence theorem is needed across prior effects. Earlier recursive outputs may have their own metadata and models; those are not the captured metadata or model used for the next sibling.

The selected head extends sigma to chi with agreement for every key below the ORIGINAL `before.core.counter` (`SharedScanPreparedHead.lean:165–168`). Apply the existing public helper:

```
SourcePruningRecordTypes.pending_refutes_extension
  before.core.counter assignment extended metadata
  capturedPacket.bounded headAgreement refuted
```

The helper is `SourcePruningEnumerationPolicyOrigins.lean:48–57`. Original `packet.bounded` also has the correct range because the captured cache and metadata are unchanged. Only agreement below that original limit is needed; no agreement on newly allocated variables is assumed.

The callback producer then uses chi with itself at its own HEAD counter. Its internal false-verdict proof uses `headPacket.bounded` and reflexive agreement (`SharedRecordedModelProgress.lean:110–115`). These are two distinct ranges: original-counter agreement transfers old refutation from sigma to chi; head-counter reflexive agreement supports the recording theorem on chi.

## Derive the actual head Packet

The completed-prefix clause returns one head resource/model packet, at the actual `prefixCaller`, `prefixNext`, and `prefixMemos` (`SharedScanPreparedHead.lean:130–190`). Retain its SAME fragment, chi, after cache, afterCaller, final global Memos, and next inventory. Do not call another head model producer.

Its complete shape supplies Safe, allocated FragmentBound, written target, cleared expansion ancestry, root, pending fragment, order gain, growth, returned cache validity, and pending-reference transfer. Use those fields as in R228 `SharedPolicyPreparedRestart.lean:563–600` to construct:

- `Admitted uv (.complete fragment afterCaller final.query after)`;
- `FragmentHistory before.core` for that SAME receipt;
- pending references from the captured Packet and CURRENT `IncomingAvoid`;
- the actual head Packet by `SharedPreparedRecursive.receipt_packet`, `SharedPreparedHookCertificates.lean:32–50`.

The head resource states `final.query = savedQueries` (`SharedScanPreparedHead.lean:137`). Use the SAME full `final : Memos`; its query projection is the actual head saved query. The original-to-head Post is already retained. No uniqueness argument for independent full memo witnesses is needed.

The target is in range at the head by `ready.inside` and head counter growth. The head's SAME model gives `fill chi fragment = chi uv` and origins of chi. Properness is already returned. The exact callback seed is

```
advance (stage recursiveFuel seed capturedMass inherited index)
  (SelectedEdge.cost chosen scs before.core.counter tries)
```

The head resource already gives Fits/Heap for that seed. Do not substitute the prefix seed or original caller.

## One actual callback and full false-restart packet

Call `SharedPreparedRecursive.callback_complete_resources_models_work`, `SharedRecordedModelWork.lean:39`, ONCE with the actual head caller, SAME full final Memos/next inventory, head cache and Packet, allocated fragment, exact seed, properness, head output model, and chi origins. Preserve its ENTIRE returned resource/model/work packet. It retains the returned Packet, RenderStable/Frame, literal Success and raw singleton at all larger callback fuels, updated types, unchanged openHoles and typing, native Fits/Heap, properness, chi model/origins, local non-stuck decision, conditional verdict/refutation, pending-size equality, and scalar-work equality for every coefficient.

Discharge the returned conditional false/refutation statement with CURRENT policies, transferred old pending refutation, target-in-range, and the SAME filled/origins facts. This derives `recorded.1 = false` and refutation of `recorded.2.pending` under the SAME chi. No new metadata agreement premise is required. Do not assume that typing/openHoles preservation implies pending-group identity; updated pending refutation is an actual callback result.

The raw callback is at `after.core`, on the head's actual caller heap. The false equation is, for arbitrary recur and stop/order:

```
continueWith recur graph templates stop order w metadata uv fragment
  afterCaller savedQueries after
=
recur recorded.2 afterCaller savedQueries (frame callbackCore after)
  (Restart.decision stop order recorded.2 (frame callbackCore after)).
```

The query equality above transports the producer's `final.query` equation to `savedQueries`. R228's private adapter at `SharedPolicyPreparedRestart.lean:127–140` gives the exact proof pattern; the helper itself is private and cannot be called from a new module.

Callback pending size and scalar work are neutral under chi. Compose these equalities with the SAME head's original-input strict P/W decrease. Preserve the complete existing head packet and append the callback inside the SAME fragment/chi existential. Do not use another model to re-prove progress.

## Common fuel and actual operational boundaries

R230 already returns one adequate native prefix/head stage bound over fixed endpoints (`SharedScanPreparedHead.lean:191–198`, proof 293–308). Choose `F = thatBound + callbackFuel`. At every `w = F+extra`, reindex that SAME prefix/head family and callback family. This supplies literal actual prefix, head, and recording observations at one native fuel. The scalar coefficient `initialBound` remains separate from native stage fuel.

The prefix still uses the ACTUAL bounded hook `continueWith (resume ... w recursiveFuel) ... w metadata uv`. Arbitrary `recur` is valid only for the later callback equation. Replacing recur globally in the prefix would change its actual execution and is not justified by the prefix certificate.

For the actual list, instantiate the callback equation with `resume ... w recursiveFuel`, then use the retained `NativeContinuations.run_append` equation and the cons clause. Keep both selected-hook outcomes. A stopped recursive result retains the selected receipt and exact outputs. A completed recursive result supplies its actual caller/query to the remaining suffix. Keep `NativeContinuations.stopped_hook:679` and `completed_head:661` as the exact local laws.

If the result is lifted through the outer prepared worker, retain `SharedPreparedRecursive.finish`, `SharedPreparedRecursive.lean:62–65`. Its stopped branch wraps the stop as `.alternatives uv processed current`. The whole scan/worker is not equal to the naked recursive call in general. A small literal finish equation can state the result with those wrappers intact; it cannot infer that the recursive call completes.

A stopped earlier prefix remains possible, with exact receipt/output prefix, failure, and optional endpoint. Its selected-head/callback clause is unreached. The cut proves no adequate depth, non-stopping prefix, full all-row traversal, total runtime work bound, uniform budget over all future states, whole termination, or Haskell correspondence. The confirmed Fun application constructor defect and its repair tracking in FINDINGS are separate from this callback composition; this audit changes no Haskell assumptions or source.


## next-ordinary-bridge.md (frozen uncompiled next-cut audit)

# Next ordinary-typing to actual source bridge

2026-11-12 07:40 CET. Bounded read-only audit after strict verification of OrdinaryTyping and OrdinaryTypeCollision. No source, compiler, Git, root-document, evidence, Haskell, or subagent changes. R230 sources and their notes remain frozen.

## Direction and smallest closed cut

Use the constructive forward direction. A supplied independent ordinary derivation, with per-occurrence admission proved separately, should produce membership of its SAME literal typed term in an actual source terms cell. Do not prove a conjunction of an ordinary constructor receipt and a separate source receipt. Do not attempt unrestricted native-encoding reflection. The reserved-name runtime example and `badQuery_untypable` already refute that converse on the public raw domain.

The smallest manageable cut handles every ordinary derivation of a variable Program, including arbitrary conversion chains and all three binding origins. It constructs the exact literal term `.node (literal name) [rigidTerm typ]`. The independent Program, raw result type, annotation child, source membership, projection, and decoder result all refer to that term.

Proposed new module: `SourceSynthesisOrdinaryLeafAdmission.lean`. Imports need only the checked `SourceSynthesisOrdinaryTyping` and `SourceSynthesisEncodedSubstitutionLift`; R228 is already a dependency. Do not modify old modules.

## Admission remains outside Typed

One small proof-indexed predicate records the actual instance used by the supplied ordinary derivation. It does not quantify over every library scheme or every raw substitution. It contains no source typing, future row membership, semantic model, or result equation.

Source-level predicate definition, with the existing abbreviated names:

```lean
def LeafEligible {lib : Library} {query : Query} (asArgument : Bool) :
    {program : Program} → {typ : Ty} → Typed lib query program typ → Prop
  | _, _, .group entry _binding rho =>
      AliasSafe entry.2.1 ∧
        ∀ raw, variableSymbol raw ∈ variables entry.2.1 →
          TypeIn (constructorCatalog lib query) (rigidTerm (rho raw))
  | _, _, .argumentOnly entry _binding rho =>
      asArgument = true ∧ AliasSafe entry.2 ∧
        ∀ raw, variableSymbol raw ∈ variables entry.2 →
          TypeIn (constructorCatalog lib query) (rigidTerm (rho raw))
  | _, _, .queryArgument _found => True
  | _, _, .application _first _second => False
  | _, _, .conversion typed _same => LeafEligible asArgument typed
```

This is a predicate on the ordinary derivation. It does not change the existing Typed rules or the public Library/Query domain. The application branch is false because this first cut is explicitly a leaf cut. It is not a claim that well-typed applications are invalid. There is no encoded sigma argument: R229 derives it from this occurrence's raw rho.

## Exact proposed public headers

Here `Typed` is `SourceSynthesisOrdinaryTyping.Typed`, `TermsTyping` is `SourceSynthesisSourceTermsTyping.TermsTyping`, `Symbol` abbreviates `SourceObservations.Label FullSyntax.Formula`, and `literal` is `SourceSynthesisLabelProgramBuildRoles.literal`.

```lean
theorem typed_leaf_terms {lib : Library} {query : Query} {asArgument : Bool}
    {name : String} {typ : Ty}
    (typed : Typed lib query (.var name) typ)
    (eligible : LeafEligible asArgument typed) :
  TermsTyping lib query asArgument 1 (.var name) (rigidTerm typ)
    (.node (literal name) [rigidTerm typ])

theorem typed_leaf_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {name : String} {typ : Ty}
    (typed : Typed lib query (.var name) typ)
    (eligible : LeafEligible asArgument typed) :
  let term : Term Symbol := .node (literal name) [rigidTerm typ]
  ∃ expression ∈ termsRows (context lib query) asArgument 1,
    evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term ∧
      term.atPath [0] = some (rigidTerm typ) ∧
      Projection literal Prod.fst term (.var name) ∧
      toProgram literal Prod.fst term = .var name
```

Neither header assumes TermsTyping, source membership, successful .ok, or an encoded substitution. The only admission data are the explicit per-use raw image and role facts. The second theorem constructs an actual source alternative and proves membership of the exact given Program's literal term. It also identifies the actual repaired decoder output.

## Exact dependent proof route

A private induction can first generalize program and derive: for eligible typed, there exists name with program = .var name and TermsTyping for the literal node at rigidTerm typ. This avoids induction on the fixed compound index `.var name`. It is the same index-generalization pattern already checked in OrdinaryTypeCollision.variable_origin, but its output is a constructed source derivation.

- Ordinary group case: unfold the eligibility conjunction. Apply R229 `group_instance_terms` to the actual entry/binding/rho and that exact pair of AliasSafe/image facts. It returns both the desired literal Program and the exact literal annotation node (`SourceSynthesisEncodedSubstitutionLift.lean:190-200`).
- Ordinary argumentOnly case: use the eligibility equality to set asArgument=true, then apply R229 `argumentOnly_instance_terms` (`202-212`). The role premise is local to this actual occurrence.
- Ordinary queryArgument case: `SourceSynthesisOrdinaryTyping.queryLookup_member` supplies membership of the actual pair (`SourceSynthesisOrdinaryTyping.lean:111-119`). Apply R228 `query_argument_terms` (`SourceSynthesisTypeSubstitutionWitnesses.lean:186-197`) at the supplied flag. No AliasSafe or universe premise is needed.
- Ordinary application case: eliminate the false leaf eligibility.
- Ordinary conversion case: apply the induction hypothesis to the underlying derivation. Use `equivalent_rigidTerm` (`SourceSynthesisOrdinaryTyping.lean:98-104`) to rewrite BOTH the source annotation index and the same literal term's child. This uses only the forward implication. It never decodes an arbitrary native annotation.

Then `typed_leaf_terms` selects the fixed name. `TermsTyping.member` produces the actual expression and acceptance (`SourceSynthesisSourceTermsTyping.lean:233-239`). `TermsTyping.shape` supplies annotation and projection for that same literal term (`151-156`). `Projection.toProgram_eq` supplies the decoder equation (`SourceSynthesisProgramTermSize.lean:60-68`). Reuse these laws. Do not duplicate the membership or projection proofs. A separate size-count wrapper is unnecessary: the source derivation already has size1 and its shape theorem supplies components=1.

## Useful next extension after the leaf cut

A bounded whole-Program extension can first handle unpruned libraries with an explicit theorem premise `lib.libraryAvoid = []`. Keep the same per-instance group/query/argument-only admission fields. In a new external eligibility predicate, replace the leaf-only false application branch by eligibility of the function at false, eligibility of the argument at true, and `TypeIn catalog (rigidTerm codomain)` for THAT application. Conversion still recurses. Do not add any of these facts to Typed.

Precise target for that later theorem:

```lean
theorem typed_unpruned_terms {lib : Library} {query : Query} {asArgument : Bool}
    {program : Program} {typ : Ty}
    (unpruned : lib.libraryAvoid = [])
    (typed : Typed lib query program typ)
    (eligible : TermEligible asArgument typed) :
  ∃ term, TermsTyping lib query asArgument program.components program (rigidTerm typ) term
```

Its application induction is concrete. Derive positive child component counts by Program induction. If the sum is2, both counts are1. Invert the already-derived function IH at source size1 to obtain its actual leaf row. With no avoid entries, fallbackFunctionRows equals component rows plus rigid query rows; oneRows false has the same alternatives in the other order. Thus the selected function row belongs to the actual fallback pool. Apply TermsTyping.fallback and the derived argument IH. If the sum is at least3, use TermsTyping.split at the actual function component count. The fresh application's codomain eligibility supplies exactly the required result TypeIn. These are outputs of the induction, not assumed source typing suppliers.

Do not silently extend that theorem to nonempty avoid lists. Their size2 restricted/fallback branches need separate literal row-origin and inclusion/exclusion certificates (`SourceSynthesisSourceTermsTyping.lean:85-105`; actual code `SourceSynthesisFirstOrderConstruction.lean:89-96`). Query function rows and group function rows have different filtering behavior. A names-only predicate without origin data can confuse them when names collide.

## Positional type and relevant/root limits

Ground Fun/0 and Fun/3 remain ordinary raw constructors. Their literal query leaves need no TypeIn. Ground group leaves also need no all-rigid universe premise when no scheme variable is demanded. Fun/2 normalizes to an arrow on both ordinary and rigid sides. The catalog nevertheless excludes ALL Fun arities (`SourceSynthesisTypeSyntax.lean:69-74`). A demanded polymorphic image, or an application result in the later whole-Program extension, must satisfy TypeIn at that position. Do not ban every Fun/0 or Fun/3 leaf or impose universe admission on all query types. The same positional rule preserves the existing var_e rigid-leaf exception.

The leaf theorem is membership in the unrestricted terms table, not the relevant table or root. Source terms size1 includes all rigid query rows (`SourceSynthesisFirstOrderConstruction.lean:84-88`), whereas ordinary lookup selects the last matching binding. Input membership is enough for this forward terms bridge. It does not prove agreement with an actual relevant singleton winner, required argument tokens, take/drop re-resolution, or root permutations (`SourceSynthesisSourceTermsTyping.lean:116-140`).

A root corollary for queryArguments=[] can later use the actual empty names resolution and selected root permutation, then the checked `firstOrderRaw_member_total` (`SourceSynthesisFirstOrderTotality.lean:118-142`). A nonempty-query root bridge needs a separate derivation of the actual required tokens and resolved winners. Do not assume RelevantTyping or a future root .ok result as its supplier.

These are FirstOrder constructor-syntax statements. They do not establish Curried correspondence or an executed Haskell pipeline theorem. The target context implements the FirstOrder branch independently of the raw record's encoding field; a later Haskell rawSearchSpace correspondence must select its actual FirstOrder dispatch explicitly.

The full objective remains open beyond these stated cuts. The executed nominal collision still prevents unrestricted source-to-ordinary soundness until its production repair or an explicit public-domain account. Ordinary typing also does not imply source completeness without actual finite-image, positional codomain, role, pruning, argument-token, and winner admission. No public contract is strengthened in this audit.


## Executed Fun-arity boundary

The tracked 20261112-fun-arity-universe packet reproduces the parsed Fun/0 and
Fun/3 application-result failures. Ordinary Z/Fun2 result controls succeed.
The rigid Fun/0 leaf succeeds. No application case times out. Own source discovery
excludes Fun at every arity, while encoding aliases only Fun/2. No production
repair is applied. Root FINDINGS.md states the minimum repair and mode limits.
