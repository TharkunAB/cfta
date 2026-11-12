# Source totality and checked projection audit

All four source packets passed their focused strict checks. The last two notes identify open work.
No Haskell production file changes in this checkpoint.

## recorded-work-note.md

# Work at one actual shared recording callback

2026-11-12 05:07 CET. Source task on verified R226 publication `61f01f90fcf7eb3fed9b314789a76c98ebe7646e`. Only the assigned new `lean/MicroCFTA/SourcePruningEnumerationSharedRecordedModelWork.lean` was added. No existing source, Haskell, root documentation, or evidence file was changed. No compilation, Git operation, or subdelegation was performed. Root must run strict verification.

Public name: `MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources_models_work`.

The header is identical to `SharedRecordedModelProgress.callback_complete_resources_models`. It adds no current or future input. Its output is:

```lean
⟨fuel, result, after, retained, pendingEq, workEq⟩
```

`retained` is the ENTIRE existing R223 callback output. It keeps the actual callback Packet and full memos, RenderStable/Frame, updated types, unchanged openHoles/typing, Fits/Heap, literal `Success` and `ExceptT.run` equations for all extra fuel, and the exact `continueWith` equation for either verdict. It also keeps current-assignment Satisfies, origins, ProperState, local non-stuck restart, empty-template false verdict, and the original conditional false/refutation result under inside/fill/OriginPolicies/current pending-refutation inputs.

The two added equations use the SAME current assignment:

```lean
pendingSize after assignment = pendingSize before.core assignment
∀ initialBound,
  NativeWork.work initialBound (EnumerationExpandableIndex.frame after before) assignment =
    NativeWork.work initialBound before assignment
```

The proof calls `callback_complete_resources_models` ONCE. It observes the returned resource tuple and its exact `Success` at `fuel+0`. The same returned Frame.values gives pending-size equality. `NativeWork.recordTypes_work`, with that actual Success and the CURRENT forest-total proof `packet.safe.1.total`, gives scalar equality for every coefficient. No second callback, model, memo, or independent endpoint producer is used.

The source imports only `SourcePruningEnumerationSharedRecordedModelProgress` and `SourcePruningEnumerationNativeWork`. It does not reprove template refutation or change the verdict conditions. It preserves either callback verdict. It contains no `sorry` or `axiom`.

Frozen source SHA256: `45a17c4c9481ab34e182899e6b4dd400471924d8b23d056921f50b79f221247d`. Source review is complete; strict compilation is pending Root's serial capped check.

This result ends at the SAME callback/restart boundary. It preserves a head's already established strict work decrease when the actual callback continues. It does not prove the callback verdict false without the retained current policy/refutation conditions. It does not execute or complete recursion, derive adequate source depth or one common work fuel, cover actual preceding siblings or all failed/dead alternatives, establish public Program decoding/typing, or prove default Haskell ordered correspondence. No Haskell defect was established by this source task.


## selection-closure-note.md

# R227 pure source selection closure

2026-11-12 05:17 CET. Only owned source: `lean/MicroCFTA/SourceSynthesisSelectionClosure.lean`, 269 lines / seven public laws. No compilation, Git, existing-source, root-document, evidence, Haskell, or subagent actions. Root owns strict verification and publication. Source frozen for its first check.

Imports: `MicroCFTA.SourceSynthesisSelections`, `Init.Data.List.Perm`. The original enumerator is unchanged. The proofs do not add a DecidableEq or distinct-name assumption. They preserve duplicate occurrences.

Public laws, namespace `MicroCFTA.SourceSynthesisSelectionClosure`:

- `subsequences_spec (inputs selected : List α)`: source subsequence membership iff selected.Sublist inputs.
- `permutations_spec (inputs output : List α)`: source permutation membership iff output.Perm inputs. This is membership equivalence; source order and multiplicity remain unchanged.
- `selections_spec (inputs selected : List (String × α))`: membership iff the selected list permutes a source sublist.
- `selections_sublist_closed inputs winner child member part`: every sublist of an actual selection is another actual selection.
- `take_mem_selections (inputs winner) (member : winner ∈ selections inputs) (offset : Nat)`: winner.take offset ∈ selections inputs.
- `drop_mem_selections (inputs winner) (member : winner ∈ selections inputs) (offset : Nat)`: winner.drop offset ∈ selections inputs.
- `resolveSelection_take_drop inputs names winner resolved offset`: both names-only take/drop keys resolve to some actual last winner in the SAME source input. It does not equate those winners with the supplied slices.

Root totality can use the two take/drop membership laws directly with the actual winner membership from the existing resolveSelection_spec. The existing root_lookup_exists/permutation_mem_selections and winner-name identity are reused; this module does not reprove them.

The private permutation core uses strong induction on total length and an inner suffix induction. Its worker completeness result keeps an arbitrary semantic permutation of the consumed prefix followed by the unchanged suffix, OR supplies an actual perms worker member. This avoids a circular completeness claim at the total original length. The interleaveAux membership specification records insertion only before a nonempty remaining segment and includes every later output. A separate fst law retains its exact selected++suffix result. Std List.exists_perm_sublist transfers actual winner sublists to source input sublists without sets, deduplication, or occurrence loss.

The intended closure seam is fully implemented in the source, pending Root verification. It has no unchecked theorem placeholder or future lookup supplier. It does not itself prove relevantRows/firstOrderRaw all-mapM totality; Root owns that consumer module. It does not establish ordinary well-typedness to source-admissible typing, inhabitance, universe admission, native/Haskell correspondence, or Curried behavior. Reserved variable aliases, rigid var_e, positional universe conditions, and catalog exceptions remain unchanged. No Haskell defect or fix was established.

Root returned a parser error for the private worker variable `prefix`, which is a Lean syntax keyword. Renamed it and its local proof names to `front`, `frontPerm`, and `frontEq`. No public statement or proof scope changed. Frozen for Root recheck.


## first-order-totality-note.md

# First-order source construction totality

The five public laws in SourceSynthesisFirstOrderTotality pass the project Nix/Lake checker.
The own-source report treats warnings as errors and checks all public namespaces and axioms.
The source SHA256 is 0b0b7a5258355037facb83e873c311336b268c8623f88751f05f4ec657aeb988.

relevantRows_total_of_resolution starts with the current context, natural size, role, and names.
Its only lookup premise is current resolution. Strong size induction covers all splits and offsets.
The actual GHC-style selection proofs derive resolution for take/drop names. They do not assert that
physical winner rows survive a names-only lookup. Both recursive sizes decrease. Existing pure_mapM_total
then supplies every split and offset result, including rows that a later membership proof does not use.
relevantRows_ok_iff_resolves states the exact success boundary for an arbitrary current cell.

firstOrderRaw_total takes only the original finite library, query, signed size, and size >= 0.
It derives all root lookup results from actual permutations and returns an actual .ok expression.
firstOrderRaw_ok_iff_nonnegative proves the exact signed success domain of this source constructor.
At size zero, success can contain an empty language. Constructor success does not imply inhabitance.

firstOrderRaw_member_total joins that internally derived .ok expression with the prior actual-source
membership theorem. Its inputs include a current source-admissible RelevantTyping derivation at an
actual root permutation and the rigid query-goal annotation. Its output contains the actual constructor
equation, filter membership, the existing role-directed Program projection, and components=size.toNat.
It has no future successful-construction or table-membership supplier.

The proof does not show that every ordinarily typed Program is source-admissible. The finite universe,
pruning, roles, and last-name winner conditions remain explicit. It does not cover Curried, actual
Haskell decoding, machine overflow, lazy productivity, or runtime correspondence.

The first compile exposed two unavailable Mathlib-style proof names in the draft. Nat.strongRecOn and
core by_cases resolved them. The next strict report required removal of redundant simp arguments and
replacement of deprecated if_neg with ite_eq_right. No limits or lint rules changed. No Haskell file changed.


## checked-projectable-note.md

# R227 checked projection source cut

Status: source frozen for ROOT's strict compiler. This worker did not compile.
Owned new source only:
`lean/MicroCFTA/SourcePruningEnumerationNativeCheckedProjectable.lean` (109 lines).
SHA256: `51ae1cf648cc0cd5094e5b6f80d9d896f64976411b1a81c0ed03d4e3be8ab130`.

Public names in `MicroCFTA.SourcePruningEnumerationNativeCheckedProjectable`:

- `ready_projectable` (line 21) has the identical current inputs as
  `SourcePruningEnumerationNativeCheckedOriginArity.ready_fits`. It derives
  actual acceptance, an existential sourceEqualities Some witness, exact
  canonical project Some, valid tries, and the existing Fits result. The proof
  uses the actual allocated intersection gate and run_correct. It exposes the
  witness already derived inside ready_fits; it adds no support/completion/
  model/capacity supplier.
- `observed_build_projectable` (line 74) takes an observed checked build return.
  It derives sourceEqualities Some, exact canonical project Some, valid tries,
  and all fresh-start own arity bounds for that same returned edge. It reuses
  `SourcePruningEnumerationCheckedArity.checked_projected_arity` and identifies
  the actual observed edge from the exact build equation. Both the accepted
  original edge and the rejected Top/[empty] sentinel are covered.

The actual SourceEqualityNativeDemand intersection route checks the combined
constraint before child work. Generic unchecked makeEdge alone does not describe
that route. No Haskell defect or required Haskell fix was established.

The results do not assign checked history to arbitrary resident rows. Deriving
initial source-generated support, retaining that support through complete current
parent/query/exposure histories, and proving every earlier scan hook continues
remain open. Existing same-sigma Post/Packet/resource/reservation results remain
applicable. Recursive-depth and common-work adequacy remain separate. No existing
source, root documentation, evidence, Haskell, Git state, or compiler output was
changed by this worker.


## next-callback-restart.md

# The same head model at its actual callback and restart

Read-only audit, 2026-11-12 05:17 CET. Focal files: R227 SharedRecordedModelWork, R226 SharedPolicyPreparedWork, PolicyOrigins and its pure refutation dependencies, and actual SharedPreparedHookCertificates. No source, Git, compilation, evidence, root documentation or Haskell changes were made. Only this audit note was written.

## Answer and smallest current conditions

Yes. Refutation of the ORIGINAL metadata.pending at the original assignment sigma transfers to the SAME ordinary or opaque head extension chi. The existing pure lemma already proves this transfer. It is not a missing semantic bridge.

For a general current R226 policy entry, retain its complete existing header and add only these current semantic conditions to a callback-continuation wrapper:

```lean
(policies : SourcePruningTemplates.OriginPolicies templates whole)
(refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group)
```

Do not add a supplier of head assignments, head models, future refutation, a future callback result or recursive depth. R226 constructs each head assignment internally. All callback resource, model, origin, fill, properness and target-range inputs come from that SAME head packet. A possible public wrapper name is `SharedPolicyPreparedWork.complete_models_resources_work_callback_progress`, with these two additions to the existing current-input header and an appended actual false-callback/restart packet for each derived complete head. Preserve the entire R226 result.

At actual startup, the existing `SourcePruningEnumerationInitialOrigins.initial_packet_models_origins`:32-65 takes current `metadata.pending=[]` (:38) and an accepted original term. It returns the same initial model, initial pending refutation and AssignmentOrigins together (:60-65). Thus startup needs no independent refutation or origin supplier. At later current entries, keep the established refutation as an invariant. Empty pending makes initial refutation vacuous; a group that is itself empty cannot be refuted.

`OriginPolicies` is sufficient for the general nonempty template catalog. The empty-catalog path skips the oracle: its false verdict needs no OriginPolicies. Its pending list is unchanged, so updated refutation follows from the transferred old refutation. A minimal case-split wrapper can therefore require policies only when templates is nonempty. No source encoding policy is needed merely to prove the empty-catalog verdict false.

## Exact existing refutation transfer

Let N be ORIGINAL `before.core.counter`, sigma the original R226 assignment, and chi the one returned by the chosen ordinary or opaque head. Keep N, not the larger head counter, as the agreement limit.

- `SourcePruningPartialMatch.PendingBound`:17 means every raw pending entry ID is below its limit. It does not mean the pending group is refuted.
- `SourcePruningEnumerationRecursive.Packet.bounded` (RecursivePacket:35) gives `∀ group∈metadata.pending, PendingBound N group` at original entry.
- R226 admission gives `narrowedCache.counter=before.counter` (:140). Its SAME preparation gives `entered.counter=narrowedCache.counter` (:162). Both head results give `∀ held<entered.counter, chi held=sigma held` (ordinary :235; opaque :286). Restrict this agreement to N using those two equalities. The opaque explicit install law (:285) supplies the same fact; do not choose another installation.
- `SourcePruningResume.refutes_assignment_congr` (AssignmentRefutation:15-30) states `Refutes chi group ↔ Refutes sigma group` for bounded IDs and old agreement. It handles raw IDs directly. Representative canonicalization is not a new condition for this transfer.
- `SourcePruningRecordTypes.pending_refutes_extension` (PolicyOrigins:48-56) applies that equivalence to the whole current metadata.pending list. Use original `packet.bounded`, not headPacket.bounded: the latter permits fresh IDs at which old agreement need not hold.

Exact internal proof shape:

```lean
have headAgree : ∀ key < before.core.counter, extended key = assignment key := by
  intro key inside
  apply agree key
  simpa only [enteredCounter, narrowedCounter] using inside
have headRefuted := SourcePruningRecordTypes.pending_refutes_extension
  before.core.counter assignment extended metadata packet.bounded headAgree refuted
```

This calculation belongs AFTER one R226 producer returns its SAME head extension. It must not become a future-head-refutation premise on the top-level theorem. Prefix and preparation retain the original assignment; the actual Right callback is `pure(false,metadata)`. Therefore the old metadata.pending used here is the same list used by the later Left callback.

## One full current Packet and callback bundle

Opaque: the R226 resource shape already contains `Packet formulas solver next headCaller final metadata after` (:273-275). The SAME model's completed receipt (:284) excludes stopped/rejected alternatives. Extract the complete branch at that receipt, with its SAME final/query witness. Admitted also supplies current FragmentBound and Safe. Do not run the finite opaque continuation producer to obtain another bundle.

Ordinary: construct the current head Packet from the SAME R226 resource and semantic tuple. Its fields supply the actual Post/query, counter growth, roots, StorageValid, PendingRealized, both index invariants, and the complete shape's Safe/FragmentBound/final slot/ancestry/root/order/PendingFragment (:204-228). The model's `result=.complete` (:234) excludes the stopped shape.

Use `SharedPreparedRecursive.receipt_packet` (SharedPreparedHookCertificates:32-49), rather than invent a new packet type. Its current context is `headPost.context`. Build Admitted and FragmentHistory from the retained fields. Obtain pending-reference preservation from the retained implication (:219-220), enteredPacket.pending and the SAME admission IncomingAvoid transported through preparation RenderStable. Use enteredPacket.ordered and enteredPacket.bounded for the captured originalCore. Rewrite `final.query=savedQueries` to identify the literal receipt. This keeps the one resource/global witness. The head packet's enlarged pending bound follows from the retained counter growth; no new pending-range assumption is needed.

Inside target: the actual chosen decision gives `uv<before.counter`. The two equal counters move this to entered.counter, and head counter growth gives `uv<after.counter`. All of these are retained R226 facts. Head AssignmentOrigins therefore gives the origin of `chi uv`; it is not an assumed future origin.

Call R227 `SharedPreparedRecursive.callback_complete_resources_models_work` (SharedRecordedModelWork:39) ONCE with that current head Packet, FragmentBound, actual head Fits/Heap, properness, outputModel, AssignmentOrigins, head caller and full final memos. Its seed is the actual returned head seed: ordinary uses `advance (preparedSeed seed) SelectedEdge.cost`; opaque uses `advance (preparedSeed seed) (scs.length+1)`. Its assignment is the SAME chi.

The returned shape is `⟨callbackFuel, verdict, callbackCore, retained, pendingEq, workEq⟩`. The full retained resource carries actual Success/ExceptT.run and continueWith equations. Its final conditional clause (SharedRecordedModelWork:84-87) consumes derived inside target, the SAME head's `fill chi fragment=chi uv`, original policies, and derived headRefuted. It returns `verdict.1=false` AND refutation of every updated pending group under chi. No second callback or semantic producer is required.

Alternatively, `SourcePruningRecordTypes.recordTypes_inl_refutes_of_origin` (PolicyOrigins:59-83) accepts original sigma and extended chi explicitly, the original bound N and agreement, the original refutation, actual head model/fill/origin, and the SAME actual callback Success. It proves the same false/updated-refutation pair. Prefer the retained R227 conditional clause after `pending_refutes_extension` because it keeps the public composition small.

With false, the actual continueWith equation selects the actual restart on `verdict.2` and `frame callbackCore headCache`. R227 preserves chi's model, origins, properness and non-stuck decision, and returns P equality and work equality for every fixed B. Thus ordinary strict work decrease and opaque exact one-unit decrease from R226 transfer to THIS restart. Its returned Packet supplies the UPDATED metadata.pending bound for the next iteration. The chi-refutation result becomes the next CURRENT invariant. The parked route retains sigma and the Right-identity metadata directly; it does not need a fabricated Left callback.

## What is present, and the actual source-policy seam

Current Packet is exactly context, Safe, pending-reference avoidance, CacheValid, a stratification witness, and the bound on metadata.pending raw IDs (RecursivePacket:21-35). It supplies total current union-find storage and the range facts required by the actual callback. Current fragment range comes from the head's FragmentBound. No additional metadata.types/openHoles range premise is needed for this callback/refutation argument.

Packet does NOT assert pending refutation, AssignmentOrigins, OriginPolicies, a semantic typing invariant for metadata.typing, or sortedness/uniqueness/range of metadata.types/openHoles. R226 supplies the head origins/model/properness separately. R227 retains `types=updatedTypes`, unchanged openHoles and unchanged typing. Those equalities do not prove that a typing state is semantically correct or that its selected hole policies are compatible at every future raw ID. The metadata lists model native IntSet observations; the representation correspondence conditions remain separate.

`OriginPolicies templates whole` (PolicyOrigins:18-20) means that every structural origin term avoids templates at its actual ProgramAt positions, and every such selected program has ProgramEncoding. ProgramAt (ProgramSemantics:18-33) follows application function/argument children and filter program children. ProgramEncoding (StructuralTemplateMeaning:17-25) requires annotated constants and the fixed `(->)` marker with recursively encoded application children. It is a source-shape condition as well as forbidden-template avoidance.

The real source-policy bridge is deriving this original-term policy from the intended public accepted-program predicate and the actual template/term encoding. Neither generic native Satisfies nor the selected unary/app/filter fits/admits tests establish it. Proving every native model avoids forbidden templates would be wrong: the callback intentionally rejects forbidden terms. State completeness for a target that meets the public policy, then prove that policy implies the formal OriginPolicies. At actual startup the initial model/refutation/origin mechanism is already available; the missing work is this public-policy/encoding connection and its correspondence to source inputs.

For another selected hole, metadata.typing remaining equal is not enough. R226's three compatibility tests are about the CURRENT uv and sigma uv. A whole-cycle induction must derive them for the ACTUAL next selected hole from the intended typing/decoding invariant. It cannot assume a future selected-hole compatibility oracle. No new old-variable-refutation transfer lemma is needed.

This cut still stops at one actual callback/restart. It does not establish whole recursive completion, one adequate common native work fuel, source-derived recursive depth, preceding-sibling traversal or rejected/dead/all-alternative coverage, backward opaque-bucket soundness, public Program typing/size, or default eager Haskell ordered correspondence. No Haskell defect was established by this audit.


## next-source-projectability.md

# R227 source projectability audit — unproved next-step plan

Read-only audit against published `61f01f90fcf7eb3fed9b314789a76c98ebe7646e`.
No compilation, source changes, Haskell changes, Git actions, or reproduction.
Focal sources: SourcePruningEnumerationConstraint, SourceSynthesisFirstOrderConstruction,
SourceEqualityPCSGuard, and SourcePruningNativeView. Other reads followed their
operational constructors, checked intersection, and pure guard dependencies.

## Closed facts to reuse first

`SourcePruningEnumerationCheckedArity.checked_projected_arity` (line 10) already
proves that BOTH outcomes of the actual checked constructor return an edge with
`sourceEqualities = some classes`, exact successful `project`, valid tries, own
arity, residency, heap preservation, and exact operation-state receipts. A
rejected request returns the Top/[empty] sentinel. Do not reprove this result.

The actual allocated intersection also checks its guard before child work.
`SourcePruningEnumerationSharedIncomingQuery.complete:41` calls the checked
TargetQuery boundary. `SourceCurrentAllocatedTargetQuery.Step:32` records
`SourceEqualityNativeDemand.execute` of `requestNode`. NativeDemand.step:87–102
intercepts edge requests; body:65–84 runs
`SourceEqualityIntersectionEdgeAllocation.run`. Rejected/mismatched branches
emit the sentinel. Only `.ready combined` emits child instructions.
`SourceEqualityIntersectionEdgeAllocation.source:31–37` and run:40–53 include
the checked conjunction/arity gate. `SourceEqualityNativeCheckedCode.children:24`
interns its checked combined guard after the ordered child walk; sentinel:31
interns Top/[empty]. Thus generic unchecked kernel `makeEdge` is NOT evidence
that the actual allocated query retains unchecked contradictory rows.

`SourcePruningEnumerationNativeCheckedOriginArity.ready_fits:26` already derives
`accepted = true` (42–56), `fits = true` (57–64), and an actual `classes` witness
with `sourceEqualities = some classes` (65–66). It obtains exact successful
projection through `project_complete` (67–69). Its public conclusion returns
only conditional `Fits`; the stronger witness is discarded.

## What projection requires

`SourcePruningEnumerationConstraint.project:10–17` returns None exactly when
`sourceEqualities` is None. Non-positive residual syntax does not cause failure:
it returns the entire constraint as the residual. `project_complete:20–37`
proves that a cached constraint with None cannot accept any term.
`SourceEqualityPCSGuard.own_sat:85` also shows that acceptance of an edge implies
its own payload is satisfiable, for positive and residual guards. This supports
one accepting edge, not every earlier edge in the physical row scan.

`SourceCompactGuards.sourceEqualities:488–491` uses stored equalities directly
for non-positive guards and Top. Positive guard extraction can add normalized
equalities. Its nested Option distinguishes residual syntax from contradiction.
Cached payloads do not prove projectability: Cached None is vacuous.
Likewise `SourcePruningEnumerationArityOrigins.Fits:25–28` quantifies over a
successful projection; `Heap:31–32` permits None vacuously. Existing Fits/Heap
preservation must not be reported as an all-row projectability result.

## Actual FirstOrder grammar

`SourceSynthesisFirstOrderConstruction.component:43` uses Top; application:47
uses the fixed three equality classes; ofType:52 uses the fixed filter class.
Generalized Types use `eqGuard (equalityClasses typ)` through
`SourceSynthesisGeneralizeSyntax.generalize:109`.
`eqGuard_eq_source:113–115` gives the completed source-normalizer payload and
`eqGuard_residual:124` gives residual Top. Consequently Top projects directly;
an eqGuard projects exactly when its completed normalization returns Some.
This audit did not prove that every generalized Type payload normalizes to Some.
The fixed app/filter equations are finite normalization goals, not checked here.
Do not replace that missing fact with the weaker active/cached theorem.

`SourceSynthesisOriginalGuardAlphabet.alphabet:30–33` lists precisely Top,
application, filter, and generalized library/argument-only Type guards.
`SourceSynthesisOriginalGuardsCached.firstOrderRaw_guards_cached:321` already
covers every actual generated guard, but only establishes Cached.
`SourceSynthesisNativeGuardOrigins.Origin:35`, initial_heap:63, trace_heap:83,
and request_heap:100 already derive actual generated/conjoined guard origins.
A small useful invariant is `Origin lib c -> c.guard = .top`: use eqGuard_residual,
Derived induction, `SourceEqualityConstraintConstructors.conjoin:20–22`, and
`GuardConjunction.merge:257–259` on Top/Top. This does NOT prove stored equalities
are Some. Arbitrary conjunction origins need not be consistent. The actual
checked intersection gate, rather than generic origin closure, removes that issue.

## Exact source boundary

Haskell `cfta/src/Data/CFTA/Interned/Type.hs:563–568` makes mkEdge return emptyEdge
when contradictory or arity-rejected. emptyEdge:541–544 is unconstrained with one
EmptyNode child. mkNode:582–585 removes empty edges. Actual intersection in
`cfta/src/Data/CFTA/Interned/Operations.hs:397–402` calls this mkEdge with the
combined guard and zipped child intersections. The Lean checked NativeDemand
route above models this branch boundary; the local checked constructor law is
already proved. Raw generic constructor and arbitrary closed native grammar
remain distinct domains. No Haskell defect or required fix was established.

`SourcePruningNativeView.narrowAt:33–40` filters existing rows using keeps:21–30,
then makes a node. The tests concern labels/annotations, not guard consistency.
`narrowAt_complete:60` exposes exactly the surviving retained rows. Narrowing
can preserve an established support invariant; it does not establish one.
`SourcePruningEnumerationSelectedValueInvariants.run_heaps:23` already transports
an arbitrary known guard predicate through selected exposure/unfolding.

## Smallest additive implementation, not yet proved

1. Expose `ready_projectable` with the SAME current inputs as ready_fits. Reuse
   run_correct, its actual `.ready` equality, accepted/fits, and fits_exact to
   return `exists classes, sourceEqualities (readback combined) = some classes`.
   Add successful `project` using its existing cached result. This requires no
   supplied future projection, endpoint, model, completion, or capacity.
   A checked-build observer can similarly expose the existential already in
   checked_projected_arity using the observed build equality.
2. Track `Projectable c := exists classes, sourceEqualities c = some classes`
   for actual current edge records. Derive initial support from actual source
   constructors or prove normalization Some for the literal generated alphabet.
   The source construction expression alone is separate from native checked
   normalization (FirstOrderConstruction header:12); keep that seam explicit.
   Propagate the invariant through actual checked parent returns and native
   query prefixes, using ready_projectable for accepted work and Top for rejected
   work. Reuse the existing origin/trace decomposition rather than an arbitrary
   conjunction-closed predicate. NativeQueryPrefixArity.node_query_prefix_heap:54
   and NativeBodyPrefixArity.body_prefix_heap:57 give the existing checked-trace
   pattern. Their Fits invariant alone is insufficient. Initial current support,
   full trace lifting, and actual parent/exposure composition remain unproved
   in this audit; no absence-of-theorem claim beyond the inspected path.
3. At actual scan entry, derive supported earlier rows from this source-created
   current heap and residency, then combine it with existing exact Post/Packet/
   Fits/Heap/reservation and same-sigma prefix facts. Do not assume support at a
   future endpoint or simply ask for all preceding rows to be supported.

Successful projection alone does not make an accepting row reached. Every prior
hook must continue, and the source recursion depth/work bounds still need their
own adequacy proof. Increasing finite depth is not a proof that every earlier
alternative completes. A dead row is language-empty; retaining it can still
change scan stopping. This distinction is a formalization/correspondence boundary,
not a reproduced production failure. Preserve the original input, all alternatives,
actual source role/size conditions, and full Haskell correspondence objective.
