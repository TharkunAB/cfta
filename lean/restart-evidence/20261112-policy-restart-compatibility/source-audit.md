# Upstream integration

Main PR208, dedd47da878e78aa5be9947247d8156675956b59, changes only two Specftacular
comparison documents. It changes no Haskell or Lean source. All checked source
hashes remain exact. Its empirical tables are not formal correctness evidence.

# Policy restart, fixed prefix and source guard audit

All five source packets pass focused strict checking. The last two notes are open work plans.
No Haskell production file changes in this checkpoint.
The initial-guard part of the history plan is now closed by OriginalGuardsProjectable.
The first leaf-substitution part of the admission plan is also closed. Later history
and full Program typing remain open. The frozen history audit has an illustrative
filter-witness error: correct children are [s, node [s]]. The new source and its
strict check use this corrected witness. Its source note records the correction.

## accepted-projectable-note.md

# R228 accepted native projection

Status: source frozen for ROOT's strict compiler. This worker did not compile.
Owned new source only:
`lean/MicroCFTA/SourcePruningEnumerationNativeAcceptedProjectable.lean` (170 lines).
SHA256: `25c8e62e6b1249feac8ef267528b447b584aec48a6106eaa36941e2cd74c28f4`.

Public namespace: `MicroCFTA.SourcePruningEnumerationNativeAcceptedProjectable`.

- `accepted_body_projectable` (line 24) has the same current gate, rich actual
  child walk, and state inputs as NativeCheckedOriginArity.accepted_body_produced.
  Its first conjunct retains that complete existing result once: exact execution,
  EdgeProduced, heap Keeps, actual edge residency, exact children, original child
  count, and Fits. Its second conjunct adds sourceEqualities Some, canonical
  project Some, valid tries, and all fresh-start own bounds for the same literal
  built edge and exact native endpoint. It uses ready_projectable and existing
  constructor field readback. It does not require a future projection or heap.
- `accepted_receipt_projectable` (line 105) takes the same current initial Good,
  edge inputs, allocated gate, and actual physical Receipt as accepted_receipt_fits.
  It retains that entire existing result once, including the actual raw ordered
  child walk, smaller child count, exact result constructor, complete native
  endpoint equality, original child count, and Fits. It adds the same successful
  projection/validity/fresh-bounds facts for the observed result. Thus it derives
  support from an actual completed body event without assuming a rich child walk
  as a separate premise. Final record coherence identifies the actual guard.

The private constructed_guard helper (line 91) copies the closed field argument
from the existing origin proof and returns only its guard equality. No new public
invariant type or alias-only law was added.

The actual SourceEqualityNativeDemand route checks the combined guard before
child work. The generic unchecked kernel constructor does not describe that gate.
The earlier frozen source-route audit was preserved. No Haskell defect or required
Haskell fix was established.

Open: initial generated guard support, support through every retained parent/query/
exposure history, all preceding scan rows and continuing hooks, adequate recursive
depth and common work, and full Haskell/runtime correspondence. These theorems
cover the actual accepted edge described by their gate/walk/receipt. They do not
claim that every resident edge has such history. Original-input/all-alternative
scope remains the objective. Existing same-sigma packet/resource results remain
separate and unchanged.

No existing source, root documentation, evidence, Haskell, Git state, or compiler
output was changed by this worker.


## type-substitution-note.md

# R228 raw type substitution witnesses

2026-11-12 06:03 CET. Owned source: `lean/MicroCFTA/SourceSynthesisTypeSubstitutionWitnesses.lean`, 199 lines / five public laws. Imports: `MicroCFTA.SourceSynthesisSourceTermsTyping` and `Lean.Elab.Tactic.Simp`. No compilation, Git, existing-source, root-document, evidence, Haskell, or subagent actions. Frozen for Root strict verification.

New definitions:

- `substTy`: simultaneous substitution on original raw type-variable names. Inserted images are not traversed again. Constructor tags and arities remain raw; rigidTerm and instantiate both interpret Fun/2 as an arrow.
- `AliasSafe`: an explicit sufficient condition on the ORIGINAL scheme. Each original constant leaf must fail source isVariableSymbol recognition; all children obey the same condition. This is a theorem hypothesis, not a new validation rule or public-domain change. It does not require rigid query types or every Fun constructor to lie in the universe.

Public laws in `MicroCFTA.SourceSynthesisTypeSubstitutionWitnesses`:

1. `instantiate_rigid_of_compatible scheme rho sigma safe coherent`: structural equality between source instantiate sigma scheme and rigidTerm (substTy rho scheme). Coherence is required only for the raw variables in typeVariables scheme. The proof handles ordinary constructors, raw arrows, and the explicit Fun/2 alias on both sides.
2. `component_instance_leaf catalog name scheme rho sigma safe coherent images`: derives existing LeafTyping at the conventional rigid substituted annotation. Its only universe premise is TypeIn for the demanded encoded variables scheme keys. It assumes no LeafTyping, TermsTyping, or semantic membership.
3. `component_instance_terms lib query asArgument entry binding rho sigma safe coherent images`: an actual libraryGroups entry supplies a size1 TermsTyping at either role flag. It retains the literal representative row and exact original scheme.
4. `argumentOnly_instance_terms lib query entry binding rho sigma safe coherent images`: an actual libraryArgumentOnly entry supplies size1 TermsTyping true.
5. `query_argument_terms lib query asArgument entry binding`: an actual rigid queryArguments entry supplies size1 TermsTyping at either role flag. It requires no substitution, alias-safety predicate, or TypeIn premise.

All raw and encoded substitutions are local theorem arguments for one occurrence. No global monomorphic sigma is introduced. Actual row memberships come from current finite input lists and preserve duplicate literal-row origins. No assumed future table membership, semantic model, or successful execution result occurs.

Limits: encoded sigma is still explicit. The module does not derive its finite lifting/injectivity law from arbitrary raw rho. It adds no independent full Program typing relation and does not prove whole-program/source-policy admissibility. Query terms membership is in the unrestricted terms cell; it does not identify an earlier duplicate query binding with a relevant-table last winner. Existing positional universe, reserved var_e, catalog, and role conditions remain separate. The frozen read-only audit and its source-only examples are unchanged and are not production Haskell defect claims.

Focused first-check repairs: use smart unfolding for the existing public typeVariables wrapper and its private recursive occurrence worker; unfold AliasSafe before conjunction projections; rewrite the public recursive encoding/substitution equations before comparing arrow terms; rename the already introduced Ty.rec list-motive binders. Public headers and hypotheses are unchanged. No lint, limits, or scope changes. Source frozen for Root recheck.

Second-check repair: simp! does not unfold the private well-founded occurrence worker. The local unfoldVariableWorker tactic instead obtains that worker from the existing public typeVariables definition body and loads its registered constructor equation theorems into a local simp set. It spells no generated private constant name. It adds no axiom or theorem hypothesis. This keeps the original source untouched. The nil-constructor branch now uses simp to remove the reported unnecessarySimpa lint. Public signatures and all limits remain unchanged.

Frozen source SHA256: `b6279a7699dccc3ac0ffb4a7ffa9d25d1b5d5af8681c58936760ed78c6c387e0`.


## policy-restart-source-note.md

# One policy head and its actual false callback restart

2026-11-12 05:46 CET. Source task on verified R227 publication `1f62420379f88154e3c98f431a064b1b3180aecd`. Only the assigned new `lean/MicroCFTA/SourcePruningEnumerationSharedPolicyPreparedRestart.lean` was added. No compilation, Git operation, existing source change, Haskell change, root documentation change, evidence change or subdelegation was performed. Root must run strict verification.

Public name: `MicroCFTA.SourcePruningEnumerationSharedPolicyPreparedRestart.complete_models_resources_work_restart`, line 143. The file has 661 lines and 50,817 bytes. SHA256: `ce1212a5f3c9f85d7f83612813f18b3ab46aab7c7c72eb0e15e1bb277cd414d6`.

## Current header and retained outputs

The public header is the complete R226 policy/prepared-work header plus only current `OriginPolicies templates whole` and refutation of every original `metadata.pending` group by the original assignment. The local `Refutes` notation fixes the concrete source symbol equality instance used by the existing callback/refutation laws. It introduces no new predicate.

The public output retains the entire R226 prefix validity/resource/work packet, parked packet, admission, common preparation packet and its model/origins/acceptance. Both the ordinary and opaque functions retain every existing head field. In particular, the ordinary result retains its exact accepting row and complete resource/model/properness packet. The opaque result retains its complete resources, global memos, canonical installed assignment, FinalizationAt, model and work/properness results.

Each derived complete head additionally returns one callback result:

```lean
∃ callbackFuel recorded callbackCore,
  callbackPacket ∧ originalPendingProgress ∧ originalWorkProgress
```

Here `callbackPacket` is the complete R227 callback return proposition, followed by the actual false verdict, updated pending refutation under the SAME internally derived head assignment, and the literal false-restart equation. Its full fields are written out in the public statement; there is no new public packet datatype.

The complete R227 proposition retains the full callback Packet/global witness, Frame/RenderStable, updated types, unchanged openHoles/typing, Fits/Heap, actual Success/ExceptT.run equations at all larger callback fuels, the either-verdict continueWith equation, model/origins/properness/non-stuck restart, the original empty-template and conditional false/refutation clauses, pending equality, and work equality for every coefficient.

The extra false-restart equation is stated for arbitrary recur, stop, order and callback extra fuel. It uses the ACTUAL head receipt's saved queries. Its returned cache is exactly `EnumerationExpandableIndex.frame callbackCore headCache`. The full callback Packet retains the SAME final global memos; the retained head query equality connects those global memos to the saved query argument.

At an ordinary head, the extra original-input results are:

```lean
pendingSize callbackCore extended + 1 ≤ pendingSize before.core assignment
work B (frame callbackCore headCache) extended < work B before assignment
```

At an opaque head, they are:

```lean
pendingSize callbackCore extended = pendingSize before.core assignment
work B (frame callbackCore headCache) extended + 1 = work B before assignment
```

Here `before` and `assignment` are the ORIGINAL inputs before the policy prefix. B is the original fixed coefficient. The returned R227 Packet/model/properness and updated refutation apply at this same actual restart. The original R226 head results remain present alongside them.

## One policy producer and one callback per completed head

The main proof calls R226 `SharedPolicyPreparedWork.complete_models_resources_work_proper_progress` ONCE, at line 513. It observes that SAME returned prefix and extends its returned branch functions. It does not rerun prefix, admission, preparation or a head producer.

The private shared `callback_from_original` adapter begins at line 58. A scoped `omit [DecidableEq Symbol] [DecidableEq Node] in` at line 57 removes only its two unused section instances. It accepts the current head Packet/model/properness/fragment/resource inputs and the ORIGINAL pending bound, old assignment and old-variable agreement. These private inputs are supplied from the actual head witnesses constructed by R226; there is no future head assignment or refutation supplier on the public header.

The adapter uses `pending_refutes_extension` with the ORIGINAL counter as its agreement limit. Original Packet.bounded supplies the old raw ID bound. It calls R227 `callback_complete_resources_models_work` ONCE and retains that entire callback result. It applies the retained current-policy clause with the actual inside/fill facts and transferred refutation. It derives false and updated refutation, then rewrites the actual continueWith equation.

For ordinary heads, the main proof constructs the current full Packet with actual `SharedPreparedRecursive.receipt_packet`. It derives Admitted/FragmentHistory/Pending from the SAME returned resource tuple and literal completion, uses the actual head Post.context, and transports IncomingAvoid through the SAME common preparation RenderStable. For opaque heads, the existing Admitted/Pending/FragmentHistory and actual completion supply that same certificate directly. Both branches retain their complete original resources and globals.

The common admission and preparation counter equalities restrict returned head agreement to the original allocated IDs. No agreement at fresh IDs is assumed. The actual Ready.inside and returned counter growth supply target range. The actual head fill/model/origins/properness discharge the callback inputs. Callback pending/work equalities transfer the original-input head progress to the returned restart.

## Limits and verification state

The source imports only R226 SharedPolicyPreparedWork, R227 SharedRecordedModelWork and actual SharedPreparedHookCertificates, with their existing pure dependencies. It contains no `sorry`, `axiom`, ResumeComplete, future-model supplier or recursive-depth premise. No old executor is cast into the shared executor.

Root reported that the entire original source compiled on its first check. Strict verification rejected only the two automatically included unused section instances on the private adapter. The log is `/tmp/mcfta-policy-restart-20261112-0535/shared-policy-prepared-restart-054823-failure.txt`. At 2026-11-12 05:49 CET, the scoped omit was added for exactly those instances. The public statement, complete packets and proof body are unchanged. Root's focused strict rerun is pending. No compilation was performed by this source worker. Only focused diagnostics from Root will change the frozen source.

This is one CURRENT prefix/head/callback/restart result. It does not execute recursion, derive adequate source depth or one common native work fuel, traverse prior siblings or all failed/dead alternatives, establish backward opaque-bucket soundness, derive original OriginPolicies from the public accepted-program predicate, derive next-hole typing-policy compatibility, prove public Program size/typing, or establish default eager Haskell ordered correspondence. No Haskell defect was established by this source task.


## prefix-stable-work-note.md

# Fixed prefix endpoints with work and resources

SourcePruningEnumerationSharedPrefixStableWork has 133 lines and one public law.
The source SHA256 is b4bb3b5761586ecd0ebdae9d96fde254495f28a410d6d8dc0ba2cb1242ccc361.
checkpoint_resources_work_stable passes the project Nix/Lake checker and strict own-source report.

Its header is the current Packet, original chosen decision, native resource profile/Fits,
and current annotation Heap from checkpoint_resources. No new public input was added.
It calls the existing prefix_checkpoint_complete once. The three alternatives capture
parked cache, empty narrowed heap, or nonempty narrowed heap/value/cache outside all larger fuels.
The explicit advance expression also fixes the entire reached Caller. Original saved query,
Right callback metadata, and resulting core are fixed. The actual stored action may vary.

At each SAME observation the theorem retains full PrefixValid and actual native Resources.
It also retains exact target debit for every B and every assignment. Parked P is unchanged,
A and W_B decrease by one. Narrowed counter and other flags are unchanged; P is unchanged;
A and W_B debit exactly 0 or 1 according to the new selected flag. No satisfying-assignment
or finite-model premise is needed for these scalar equalities.

The proof extracts validity from the SAME primitive checkpoint. Existing prefix_resources
and retained_work_target_debit observe that exact run. It does not call another checkpoint
or complete producer. The first draft lacked the EnumerationStorageProgress namespace for
pendingSize; adding that open statement resolved the elaboration errors. No limits changed.

This theorem does not choose one common later head/callback workFuel. It does not establish
ordinary row reach after earlier siblings, recursive adequate depth, public compatibility,
or Haskell correspondence. A full global memo bundle is still chosen within current endpoint
proofs. Its uniqueness must not be assumed. The new fixed endpoints permit a later proof to
select and reuse one such bundle. No Haskell source file changed.


## original-guards-projectable-note.md

# R228 original guard projectability

Status: source frozen for ROOT's strict compiler. This worker did not compile.
Owned new source only:
`lean/MicroCFTA/SourceSynthesisOriginalGuardsProjectable.lean` (105 lines).
SHA256: `99ac5708e0dbaabaaf14b5707529ec8b0a9cdaa6cc8fa082cfb1e1ac4b5a984f`.

Public namespace: `MicroCFTA.SourceSynthesisOriginalGuardsProjectable`.

- `generalized_projectable` (38): every actual Ty's generalized eqGuard has
  sourceEqualities Some. The private helper uses generated_equalities with a
  constant finite substitution, normalize_sat, and Sat None = False. It then
  uses the actual eqGuard_eq_source readback. No typing or universe supplier.
- `application_projectable` (47) and `filter_projectable` (57): finite raw-class
  witnesses establish the same fact for the two fixed original source guards.
- `alphabet_projectable` (65): covers Top, the two fixed guards, and every
  generalized library/argument-only Type in the actual OriginalGuardAlphabet.
- `initial_heap` (76): the actual observed original mapped build supplies
  SourceEqualityAnnotationHeap.Heap instantiated with
  `fun guard => exists classes, sourceEqualities guard = some classes`.
  It reuses NativeGuardOrigins.initial_heap and maps the literal alphabet
  membership to its actual payload witness for every physical edgeRecords key.
  The existing build proof handles canonical hits and complete stored bodies.
- `complete` (89): for actual Library, Query, and nonnegative signed size,
  firstOrderRaw_total supplies the original expression. The existing closed
  construction law supplies its actual root/heap. The theorem returns the
  actual firstOrderRaw equation, build equation, and the whole initial support
  Heap. No expression, future heap, or supported-row supplier is assumed.

Correction to the frozen history audit's illustrative filter witness: its paths
are [0] and [1,0]. The source uses root children [s, node [s]], which satisfies
both paths. The earlier [s,s] example was incorrect. The frozen audit was kept
unchanged as requested. The application witness is unchanged.

No new public invariant type was introduced. Projectability uses the existing
Heap predicate. The actual allocated checked-route correction remains in force:
NativeDemand .edge enters its guard gate, while arbitrary Code .work can bypass
that gate. This module makes no arbitrary-Code preservation claim.

Open: generated native prefix preservation, complete retained parent/query/
exposure history, every earlier scan hook continuing, recursive-depth/common-work
adequacy, and full Haskell/runtime correspondence. The theorem covers the original
initial construction and all of its physical records. It does not assert that
later arbitrary native work preserves those records' guard predicate. No Haskell
fix or defect was established.

No existing source, root documentation, evidence, Haskell, Git state, or compiler
output was changed by this worker. Earlier source and audit files remain frozen.


## next-common-work.md

# R228 audit: one common native work bound

Read-only source audit, 2026-11-12 06:03 CET. This note proposes a next proof. It does not report a new verified theorem. No source, compiler, Git, Haskell, or existing note was changed.

Frozen source inputs:

- `SourcePruningEnumerationSharedPolicyPreparedRestart.lean`: public `SourcePruningEnumerationSharedPolicyPreparedRestart.complete_models_resources_work_restart`, line 143; SHA256 `ce1212a5f3c9f85d7f83612813f18b3ab46aab7c7c72eb0e15e1bb277cd414d6`.
- `SourcePruningEnumerationSharedPrefixStableWork.lean`: public `SourcePruningEnumerationSharedPrefixWork.checkpoint_resources_work_stable`, line 32; SHA256 `b4bb3b5761586ecd0ebdae9d96fde254495f28a410d6d8dc0ba2cb1242ccc361`.

## The current quantifier gap

R228 returns `exists prefixFuel, forall prefixExtra, ...`. Its live branch then returns ONE full `prefixMemos`, one preparation carrier, one selected ordinary head or opaque head, one extended assignment, and one actual Left callback. Their bounds and witnesses remain inside `forall prefixExtra`. Taking the maximum of those witnesses does not produce a common bound for the family: another prefix fuel may select another witness.

The new prefix checkpoint fixes the physical prefix endpoints outside all larger fuels. Its live case, lines 60–66, fixes `checked`, nonempty `value`, `heap`, and the entire returned `after : Cached`. The reached caller is the explicit expression

```
SourceCurrentAllocatedPartialState.advance caller
  (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked
    <heap, caller.checked.operations>) caller.fourth caller.merge
```

Thus it fixes the ENTIRE caller, including the retained fourth and merge components. It also fixes the saved query memo to `memos.query`, the actual action raw result to `[ok ((), after.core)]`, and the Right callback result to `[ok ((false, metadata), after.core)]`. The prepared action FUNCTION can vary with the larger fuel.

The checkpoint does not put a full `EndpointMemoGateTrace.Memos` witness outside its fuel family. Do not infer equality of separately produced full memo bundles or semantic assignments. Instead, retain ONE R228 bundle at ONE common physical observation. `Post` and `Packet` are endpoint predicates; their fixed caller/cache/metadata arguments do not mention native fuel or the prepared action function. Downstream operational preparation consumes only that fixed caller, cache, and query projection.

## Construct the shared observation once

1. Obtain prefix bound `p` from ONE call to R228. Obtain bound `q` and fixed physical shape from the new checkpoint observer. The observer supplies no second semantic model or full global bundle.
2. Let `W0 = p + q`. Inspect R228 at extra `q` and the checkpoint at extra `p`. These are the SAME literal `runPrefix` observation, by addition commutativity.
3. Retain the ONE R228 live bundle at `W0`: its `prefixMemos`, admission packet, properness, original assignment and origins, preparation carrier, ordinary function, opaque function, and original-input progress statements. Constructor injectivity identifies its reached caller, narrowed cache, and saved query with the checkpoint's fixed fields. A second call to a semantic producer is unnecessary.
4. For later native fuels, use the checkpoint's physical observation and validity/resources. Reuse the retained endpoint predicates and full global witness. Do not select a fresh full memo witness from each later `CurrentPrefixFacts` proof. The empty checkpoint case is incompatible with the accepting R228 packet at `W0`; it is not a new public nonempty premise. The parked case already has a fixed observation and fixed R228 packet.
5. Retain the ONE preparation carrier from that bundle. It already fixes the decoded value, prepared value, preparation heap, entered core/cache, and raw result at all additive larger preparation bounds. Keep the entire carrier, not just the prepared node or heap.

One explicit alignment is needed at the operational preparation join. `SharedPreparedContinuations.run` rebuilds its entered cache as `EnumerationExpandableIndex.frame enteredCore narrowedCache`. R228 returns the equal entered core and preserves the narrowed cache's expandable/waiting fields. These equalities identify the rebuilt cache with the SAME returned `entered : Cached`. The prepared caller is likewise the literal `SelectedValueCaller.advance reached preparationHeap` from the retained carrier.

## Suggested smallest public source cut

Suggested additive module/name:

```
SourcePruningEnumerationSharedPolicyPreparedCommonWork
  .complete_models_resources_work_restart_common
```

Use EXACTLY the R228 public input header at lines 143–185, including only CURRENT original `OriginPolicies` and pending refutation. Add no future head assignment, metadata/refutation supplier, fixed future memo, uniform fuel supplier, or recursive-depth premise.

The following is a quantifier specification, not a proposed packet datatype. Preserve all fields of the R228 result. In the live branch move its retained physical endpoints, full `prefixMemos`, preparation witnesses, and ordinary/opaque functions outside the new larger-fuel quantifier. Return:

```
exists fixed prefix endpoints, prefixMemos, fixed preparation witnesses,
  [entire R228 prefix/common/preparation/ordinary/opaque packets]
  and exists C,
    (forall extra, exists actionAtThisFuel,
       exact fixed-prefix observation at C+extra
       and PrefixValid/resources/exact original-prefix debit
       and exact SAME preparation observation at C+extra)
    and (recursiveBoundary prepared = true ->
      exists F, fixed opaque receipt/endpoints/global bundle/assignment,
                callback metadata/core,
        [entire SAME R228 opaque and callback packets]
        and forall extra,
          let w := F+extra
          exact fixed-prefix observation at w, with some actionAtThisFuel
          and exact SAME preparation observation at w,w
          and exact SAME opaque-head observation at w,w,w,w,w
          and exact SAME Left recordTypes singleton at w
          and exact false-callback restart equation at w
          and exact actual prepared-continuation equation at w).
```

The opaque branch is an internally derived result condition, not an extra future input. Its `F` is outside `forall extra`. Retain the complete original ordinary function in this cut; do not claim that its selected edge is the complete actual ordinary scan. A first source cut can stop after the stable prefix/preparation carrier if the operational wrapper makes the public theorem too large. Both cuts use one R228 semantic producer.

A concrete sufficient opaque bound is

```
C = W0 + preparationBound
F = W0 + preparationBound + opaqueHeadBound + callbackFuel
```

For every `w = F+extra`, each required bound is at most `w`. Reindex each existing additive stable equation using `w - bound` and `Nat.add_sub_of_le`. The fixed scalar coefficient `B` from R228 is not this native work bound; retain its original meaning and all original `P`/`W` statements. In particular the fixed opaque callback state keeps `P_restart = P_original` and `W_restart + 1 = W_original` under the SAME internally derived assignment.

The selected ordinary edge also admits an isolated common native bound: include its `r,n,p,h,k` and callback bound in the sum; instantiate its stable equation with `er=w-r`, `en=w-n`, `P=w`, `H=w`, and `ek=w-k`. R228 supplies ONE witnessed edge, lines 283–299. It does not provide all rows or an execution from the actual caller reached after earlier rows.

## Actual opaque continuation and restart

`SharedPreparedContinuations.run`, lines 65–86, uses the same opaque receipt continuation in the terminal-bucket arm and in the non-node arm. Thus the internally established opaque boundary reaches the actual single-head arm. Substitute the fixed preparation and opaque receipt equations into this definition.

R228 supplies the callback singleton and the equation, for arbitrary `recur`, `stop'`, and `order'`:

```
continueWith recur graph templates stop' order' w metadata uv
  fragment headCaller savedQueries headCache
=
recur updated headCaller savedQueries (frame callbackCore headCache)
  (Restart.decision stop' order' updated (frame callbackCore headCache)).
```

Preserve `SharedReceiptContinuation.run` and the enclosing `SharedPreparedRecursive.finish` for the returned `recur` outcome. A stopped recursive outcome can acquire the actual alternatives failure wrapper. An unconditional equation that simply discards these wrappers and equates the entire worker to `recur` would be false.

`SharedPreparedRecursive.resume_prepared`, lines 194–218, joins the fixed-prefix equation to the actual prepared continuation at ONE native `w`. Its `narrowed` argument can contain the varying `actionAtThisFuel`; no action-function equality is required. Instantiate its callback with `resume ... w depth` if desired. This supplies an exact equation through the next recursive CALL for any `depth`. It does not establish that the recursive call completes or derive adequate recursive depth.

## Existing helper scope

- `PreparedFuel.native_moreFuel:19`: raises only native fuel while representative fuel stays fixed. It does not justify equality of prepared action functions when both grow.
- `PreparedFuel.nonempty_moreFuel:39`: raises both fuels and returns an action with the SAME actual singleton execution on the SAME checked core. This is the correct invariant already used by `SelectedStep.prefix_checkpoint_complete` / `PrefixCheckpoint.lean`, notably lines 210–228.
- `SelectedPreparationCarrier.complete_resources_carrier:28`: supplies the fixed preparation run family and full carrier. R228 already retains this information. Do not call another preparation producer to obtain unrelated globals.
- `SelectedPreparationIdentification.identify_complete:27`: compares actual stable preparation observations at an additive common bound, then identifies decoded value, raw core, value, and heap. It is a useful equality method if needed; its input stable run family must be derived internally here. It does not prove uniqueness of arbitrary full global memo witnesses.
- `SharedDispatchUnique.ok_unique:29`: for the SAME dispatcher caller/core/source/target/query input and two successful native bounds, identifies that dispatcher's action option, returned caller, and saved query. Its dispatcher is not the outer `Action.prepare` family with changing representative fuel. Its conclusion also does not identify full `EndpointMemoGateTrace.Memos` or semantic assignments.
- `SharedPrefixResources.CurrentPrefixFacts.right_packet:292`: derives the full Right packet and unchanged metadata for ONE actual observation. Select it once if needed; its full memo existential must not be joined with independent bundles.
- `SharedReceiptContinuation.completed:48`: identifies the exact complete-hook fold, retaining its receipt. For arbitrary recursive outcomes, use the literal `run` definition or its stopped-hook law as appropriate.

## Honest remaining boundary

The audited next cut would give a common native work bound for one current accepted prefix, its SAME preparation, and its opaque head plus actual false callback/restart. It retains one assignment and one full global bundle. The stable prefix law and the R228 component packets are currently verified; this composed common-work theorem has not been implemented or checked.

The actual ordinary list still requires current endpoint/model/resource transport through earlier rejected, dead, and accepted alternatives and their hooks. The witnessed accepted row's membership does not place it at the actual reached caller/query. A complete all-alternative scan and a source-derived common native budget over all reached recursive states remain open. Adequate recursive depth, whole enumeration termination/productivity, order and multiplicity, signed API/rank laws, machine limits, warm-cache coverage, and correspondence to the default eager-order Haskell implementation remain separate obligations. This audit establishes no Haskell defect.


## next-projectable-history.md

# R228 next checked-row history — read-only, unproved plan

The accepted projection source and previous audit remain frozen. No source,
compiler, Git, Haskell, or evidence changes were made for this audit.

## Smallest existing heap predicate

Use `SourceEqualityAnnotationHeap.Heap` (line 15), instantiated with
`fun c => exists classes, SourceCompactGuards.sourceEqualities c = some classes`.
It checks every actual physical edgeRecords key. No new invariant type is needed.
`Heap.edge:40` gives the predicate for a resident edge and annotations for all its
children from the same current heap and Facts. `Heap.available:24` reaches complete
stored binder bodies. This is stronger than support of the one accepting row and
is sufficient to cover every retained original row once residency is known.
It is weaker than requiring a shared accepting term for every guard.

`SourceEqualityAnnotationHeap.edgeStep:46` handles both cache cases explicitly:
old keys use the current heap invariant; an installed key uses its supplied guard
predicate. `run:67` and makeEdge:84 combine with SafeWork:61. makeNode/makeUnion
and withoutSelfReference introduce no edge constraints. Stored substitution and
optional binding already preserve any predicate through
`SourceEqualityAnnotationStoredSyntax.encode_allowed:41` and optionalBinder:65,
including the pending endpoint. All of these results are already proved.

## Restrict preservation to actual generated requests

Arbitrary NativeDemand Code permits unchecked makeEdge. NativeDemand.step:101–102
passes non-edge Code to RecursiveIntersectionNative.step; its .work branch:41–43
runs any supplied Work directly. Only .edge requests enter the checked body.
Therefore an unrestricted theorem for every Code and current support heap needs
an emitted-work condition such as existing SafeWork; Good/physical readiness alone
must not be presented as source projectability. This observation describes the
operational definitions, not a Haskell defect or an executed counterexample.

Use a generated-request theorem with this header shape (not yet implemented):

    node_query_prefix_projectable
      (request : NodeRequest Symbol Guard) (before after : Checked width)
      (remaining : Control Node) (fuel : Nat)
      (initial : Good before)
      (current : Heap (fun c => exists cs, sourceEqualities c = some cs)
        before.native.machine.heap)
      (trace : Trace fuel (.code (requestNode request.domain request.left request.right))
        before remaining after) :
      Heap (fun c => exists cs, sourceEqualities c = some cs) after.native.machine.heap

Add the matching requestEdge theorem. The only support premise concerns the literal
CURRENT entry state. It is not supplied for a future reached heap. Derive the pair
by strong induction on actual yielded trace length, following the closed
`SourcePruningEnumerationNativeQueryPrefixArity.query_prefix_heaps:24`, public
node_query_prefix_heap:54, and edge_query_prefix_heap:62. Smaller-call suppliers
stay private to that induction; do not add them as new public completion premises.

The existing decomposition already accounts for the required operational cases:

- `NativeRequestPrefixArity.node_request_prefix_heap:55` and
  edge_request_prefix_heap:102 separate cold evaluation from warm ready hits.
  A ready hit changes no edgeRecords. Good supplies residency of returned memo
  values. Its stored winner need not equal the newly requested operands.
- `NativeNodePrefixArity.compileNode_prefix_heap:275` uses generated local work,
  recursive requests, and optional binding. Replace its specialized arity work
  checks with existing generic AnnotationHeap SafeWork checks. Its generated
  makeNode/union work introduces no fresh guard; stored binder work copies known
  guards. Do not apply this argument to arbitrary Code continuations.
- `NativeBodyPrefixArity.body_prefix_heap:57` obtains the literal checked branch
  through NativeBodyOriginArity.body_choice_checked:26. Mismatch/rejection
  emits Top/[empty], which projects by reduction. A ready branch uses R227
  NativeCheckedProjectable.ready_projectable:21 to justify its actual guard.
  The actual ordered child prefix precedes the final makeEdge work. This yields
  support even before a body has completed; R228 accepted_body_projectable and
  accepted_receipt_projectable are already closed completed-event instances.
- Trace includes yielded prefixes, so it covers partial stopping caches without
  requiring future completion. Error/blocked outcomes require only the final
  single-step extension: gate faults change operations but not the native heap;
  busy/absent publication changes memo state but not edgeRecords. Optional-binder
  stopping is already covered above. Keep this extension separate unless a caller
  needs it; do not silently call every failure a completed Receipt.

## From query allocation to all retained parent rows

The current native predicate covers old keys, all new checked query allocations,
and reused keys. To transport it through the full outer parent producer, follow
`SourceCurrentAllocatedSharedParentWorker.edge:110–121`: raw contradiction calls
checked reject; the live branch reduces children and then calls checked build.
Use Top for reject; use the new native query-prefix result for child intersections;
use R227 observed_build_projectable plus AnnotationHeap.edgeStep/run for the
returned checked build. Gate failures before interning retain the current heap.
Then lift through the actual local scan/pass/classes and outer rows/descendant
recursion, whose returned states compose. Existing node rebuilds retain edges.
Memo hits need current coherence/residency, not a new future support supplier.
Selected exposure/unfolding already has predicate-parametric
`SourcePruningEnumerationSelectedValueInvariants.run_heaps:23`; narrowing retains
existing filtered rows via NativeView.narrowAt_complete:60. At actual scan entry,
Heap.edge and actual row residency then derive every earlier row's projection.
This full parent/query/exposure lifting remains unproved in this audit.

## Initial source support is now a small concrete cut

A missing published corollary does not require a new semantic assumption.
`SourceSynthesisGeneralizeFiniteInstances.generated_equalities:168` already proves
`Satisfies (instantiate substitution typ) (equalityClasses typ)` for ANY actual Ty
and uniform finite substitution. `SourceEqualityPCSGuard.normalize_sat:20` then
shows Sat of the completed normalization. `SourceEqualityGuardReadback.Sat:85`
reduces Sat None to False. Therefore normalization must be Some. Pick a constant
finite leaf substitution; no typing derivation, future term, or universe-membership
supplier is required for this guard-only fact.

`GeneralizeSyntax.eqGuard_eq_source:113` and eqGuard_residual:124 turn that witness
into sourceEqualities Some for each generalized library guard. Top is immediate.
For the fixed app/filter guards, prove finite raw-class satisfaction once and use
the same normalize_sat argument; do not assume a generic conjunction of supported
guards remains supported. A concrete app witness can use one common leaf s and
root children `[s, s, node [node [s,s,s]], node [s]]`. It satisfies all three raw
classes independently of symbols. The filter witness has children `[s,s]`.
These finite equations have not been compiled in this audit.

`SourceSynthesisOriginalGuardAlphabet.alphabet:30` lists only those cases.
Its mapped_guards:198 covers all actual mapped syntax. For an observed current
build, instantiate `SourceEqualityAnnotationConstruction.build:55` with the
predicate above, derive Allowed from OriginalGuardAlphabet membership, and start
with AnnotationHeap.empty_heap:19. The shorter proof can reuse
`SourceSynthesisNativeGuardOrigins.initial_heap:63` and map each recorded alphabet
membership pointwise to its sourceEqualities witness. No generic heap_mono helper
is required. For a theorem deriving its own actual initial heap, reuse
OriginalGuardAlphabet.complete:238 / InternedFreshOrdinaryClosedCompletion.closed_complete
and then apply the observed-build result. The only source input is actual
firstOrderRaw success, not a future supported-row or final-heap supplier.

## Proposed next NEW-file source task

`SourceSynthesisOriginalGuardsProjectable.lean`:

1. A private normalize-Some corollary from finite raw-class satisfaction.
2. Public `generalized_projectable typ` from generated_equalities.
3. Public `alphabet_projectable lib guard member`, including Top and the two
   fixed witnesses.
4. Public `initial_heap` for the actual current mapped build, using the existing
   generic Heap predicate and current observed build equality.
5. If desired, `complete` derives the actual mapped build and that Heap directly
   from firstOrderRaw success via the already-closed build completion theorem.

This is a bounded initial-source cut. It closes neither the generated native
prefix theorem above nor full parent history. Even with all earlier rows supported,
actual row reach still needs every earlier hook to continue and adequate source
recursive depth/common work. Existing same-sigma Post/Packet/reservation facts stay
closed and unchanged. Preserve original input, all alternatives, source role/size
conditions, and the full Haskell/runtime correspondence objective.


## next-source-admissibility.md

# Next conventional-typing admission bridge

Read-only audit, 2026-11-12 05:40 CET. R227 selection closure and all five FirstOrderTotality laws are strict PASS; Root owns the running full Audit. No source, docs, evidence, compiler, Git, Haskell, or subagent changes were made. This file is the only output of this audit.

## What exists now

The current synthesis judgments are algorithm-admissible derivations, not an independent conventional type system. Exact headers are in SourceSynthesisSourceTermsTyping.lean:67-80,116-117:

```lean
inductive LeafTyping (catalog : List (String × Nat)) :
    Row → Program → Term Symbol → Term Symbol → Prop
inductive TermsTyping (lib : Library) (query : Query) :
    Bool → Nat → Program → Term Symbol → Term Symbol → Prop
inductive RelevantTyping (lib : Library) (query : Query) :
    Bool → Nat → List String → Program → Term Symbol → Term Symbol → Prop
```

Their structural and semantic contracts are closed. SourceSynthesisSourceRelevantTyping.relevantRows_member:61-68 consumes the literal actual `.ok rows` equation. Root's new FirstOrderTotality removes that execution premise at the root. Its exact current header is SourceSynthesisFirstOrderTotality.lean:118-139:

```lean
theorem firstOrderRaw_member_total [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : SourceSynthesisTypeSyntax.Library} {query : SourceSynthesisTypeSyntax.Query}
    (size : Int) (nonnegative : 0 ≤ size)
    (selected : List (String × Row))
    (permutation : selected ∈ permutations (context lib query).argumentEdges)
    (program : SourceSynthesisProgramTermSize.Program)
    (body : Language.Term (SourceObservations.Label FullSyntax.Formula))
    (typed : SourceSynthesisSourceTermsTyping.RelevantTyping lib query true size.toNat
      (selected.map Prod.fst) program
      (SourceSynthesisFiniteTypeWitnesses.rigidTerm query.queryGoal) body) :
    ∃ expression, firstOrderRaw lib query size = .ok expression ∧
      InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
        (SourceSynthesisProgramBuildRolesGeneric.mapSyntax
          SourceSynthesisLabelProgramBuildRoles.literal expression)
        (.node (SourceSynthesisLabelProgramBuildRoles.literal "filter")
          [SourceSynthesisFiniteTypeWitnesses.rigidTerm query.queryGoal, body]) ∧
      SourceSynthesisProgramTermSize.Projection SourceSynthesisLabelProgramBuildRoles.literal Prod.fst
        (.node (SourceSynthesisLabelProgramBuildRoles.literal "filter")
          [SourceSynthesisFiniteTypeWitnesses.rigidTerm query.queryGoal, body]) program ∧
      program.components = size.toNat
```

Thus source construction totality is no longer the missing root premise. The remaining premise is the source-admissible derivation and its joint type annotation.

## Existing ordinary relations are for another API

SourceTypingRules.lean:82-105 defines an independent bounded typing relation:

```lean
Typed (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol)) :
  List Ty → Ty → Int → Term Symbol → Prop
```

Its constructors are ordinary constructor-rule selection and position-indexed variables in an innermost-first environment. FieldsTyped and FieldTyped retain fixed fields and positive nesting budgets. SourceTypingRulesLanguage.accepts_typed:282-287 already proves its equivalence to the typed-datatype row language, under LawfulFixed.

This models Data.CFTA.Gen.Typing, not Data.CFTA.Gen.Synthesis. The Haskell source confirms the split: Typing.hs:174-181 defines user constructor rules and fields; :225-234 defines typing environments, roots, and rules. A polymorphic rule requires one rule per type (Typing.hs:184-187). There is no current library-to-rules construction that supplies every polymorphic synthesis instance. Reusing an arbitrary rule list as a new hypothesis would not derive the synthesis contract.

No independent conventional typing relation over SourceSynthesisProgramTermSize.Program and SourceSynthesisTypeSyntax.Library/Query was found in the Lean sources. Other Typed predicates concern cache, reference, or domain well-formedness. OriginalType/ProgramRow in synthesis modules describe annotation origins and source row roles, not ordinary typing.

Synthesis.hs has finite raw Type, Library, Query, and Program records (:128-132,227-242,315-327), but no ordinary Program typechecker. Synthesis/Liquid.hs:1301-1311 has one-way expected/actual base-type unification for the separate refinement synthesizer. It is not the missing first-order Program typing judgment.

## Why unrestricted ordinary typing does not imply source admission

These are source-level counterexamples by constructor inspection. They were not compiled or executed in this read-only audit. They are not new reproduced Haskell defect reports.

1. **Unsupported rigid instance image.** Let libraryGroups contain only `("f", tVar "a", ["f"])`; no argument-only entries or avoid rules; FirstOrder encoding. Let the query have no arguments and rigid goal `tVar "e"`. Conventional universal instantiation types the one-component Program f at e. The source constructor catalog is empty. Its universe has var1..var4 and recursive arrows, not the leaf var_e. The component instance needs its demanded image to be TypeIn [] (rigidTerm e), which has no constructor. Source raw construction still succeeds; ordinary f:e does not supply the required source derivation. This is a positional boundary: with query argument x:e and goal e, the rigid singleton x is admitted without a universe premise. Do not ban rigid e globally.

2. **Intentional pruning.** Let f:A→A and c:A be two component groups. Let libraryAvoid contain `(["f"], none)`; no query arguments; goal A. The conventional Program f c has type A and size2. The source emits no restricted row for none, and its fallback removes f. No size2 source derivation for f c follows. With a required query argument x:A, the Program f x can remain admitted through nonempty relevant recursion, as the source explicitly documents at Synthesis.hs:233-238. A blanket global prohibition on an avoided head would misstate the actual algorithm.

3. **Query requirement multiplicity.** Let queryArguments be `[("x", A), ("x", A)]`, goal A, and the candidate Program be x at size1. Ordinary named lookup types x:A. It also uses every distinct query name. The source root key contains [x,x], its winner has length2, and size1 returns no rows. Admission needs occurrence allocation for the ordered argument LIST, including duplicate-name multiplicity; set coverage is insufficient. This does not claim that last-winner types equal supplied slice types. The source re-resolves names at every child.

4. **Encoded constant/variable alias.** A conventional scheme `a → TCons "var1" []` treats the latter as a rigid constructor. Source generalization recognizes the encoded leaf var1 as the same variable-shaped key as TVar a. Instantiating a to a distinct closed type therefore also replaces that supposedly rigid constant. Ordinary raw-Type substitution and source encoded substitution need not commute. A compatibility theorem must expose this domain issue. It cannot assume the desired whole-scheme correspondence as its premise.

A simpler relevance failure also exists without duplicates: an otherwise well-typed constant c:A does not use a required x:B. Ordinary typing alone has no use-every-argument condition.

## The smallest noncircular next cut

Recommend a small ordinary scheme-instance/leaf bridge before a full Program completeness theorem. It adds conventional simultaneous substitution on the existing raw Ty, proves its source encoding correspondence, and derives the existing LeafTyping/size1 TermsTyping constructors from actual library/query bindings. It does not add another Program AST.

The following names and statements are PROPOSED; they do not exist yet:

```lean
def substTy (rho : String → Ty) : Ty → Ty
  | .tVar name => rho name
  | .tFun argument result => .tFun (substTy rho argument) (substTy rho result)
  | .tCons name children => .tCons name (children.map (substTy rho))
```

This is ordinary simultaneous substitution on raw variable NAMES. It does not recursively substitute inside an inserted image. Each component occurrence will choose its own rho.

A sufficient syntactic compatibility predicate on an ORIGINAL scheme is:

```lean
AliasSafe (.tVar _) := True
AliasSafe (.tFun d c) := AliasSafe d ∧ AliasSafe c
AliasSafe (.tCons name children) :=
  (children = [] → isVariableSymbol name = false) ∧
  (∀ child ∈ children, AliasSafe child)
```

This rejects constant leaves that the source treats as encoded variables. It does not reject all var_e query types, every Fun constructor, or every rigid type outside the universe. It is an explicit sufficient domain condition for this bridge, not an existing validation rule or a silently adopted change to the public contract. A more permissive compatibility predicate could instead require the particular substitution to fix each such constant leaf; do not add that generality unless needed.

Prove this correspondence by structural induction, with finite pointwise variable-image agreement:

```lean
theorem instantiate_rigid_of_compatible
    (scheme : Ty) (rho : String → Ty) (sigma : String → Term Symbol)
    (safe : AliasSafe scheme)
    (coherent : ∀ name ∈ typeVariables scheme,
      sigma (variableSymbol name) = rigidTerm (rho name)) :
  SourceSynthesisGeneralizeFiniteInstances.instantiate sigma scheme =
    rigidTerm (substTy rho scheme)
```

No automaton membership premise occurs here. Fun at arity2 remains the source arrow alias on BOTH sides of the equality, so it needs its explicit existing two-child case. Fun at other arities remains a rigid constructor in this correspondence; its universe/catalog admission is a separate positional issue.

Then derive this public source-data result; the following signature is exact pseudocode with the existing abbreviated types:

```lean
theorem component_instance_terms
    (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Ty × List String) (binding : entry ∈ lib.libraryGroups)
    (rho : String → Ty) (sigma : String → Term Symbol)
    (safe : AliasSafe entry.2.1)
    (coherent : ∀ name ∈ typeVariables entry.2.1,
      sigma (variableSymbol name) = rigidTerm (rho name))
    (images : ∀ key ∈ variables entry.2.1,
      TypeIn (constructorCatalog lib query) (sigma key)) :
  TermsTyping lib query asArgument 1 (.var entry.1)
    (rigidTerm (substTy rho entry.2.1))
    (.node (literal entry.1) [rigidTerm (substTy rho entry.2.1)])
```

The proof gets the actual context component row from binding, inserts it in oneRows, uses LeafTyping.component with this occurrence's sigma, and rewrites the joint annotation with instantiate_rigid_of_compatible. It assumes neither LeafTyping nor TermsTyping, neither successful table membership nor a semantic model. Variable-image agreement is a primitive substitution encoding law, not an assumed whole-type result.

The argument-only analogue fixes asArgument=true and uses actual libraryArgumentOnly membership. The rigid query-argument analogue uses actual queryArguments membership and has NO TypeIn premise. These are direct source-data bridges and work with duplicate entries because they retain the selected literal row.

The sigma argument is currently explicit. Do not claim that every raw rho automatically has a supplied encoded sigma. A later finite lifting lemma can build it from typeVariables scheme and variableSymbol injectivity, with only the demanded image-admission hypotheses. No closed variableSymbol injectivity/lifting law was found. Keep sigma local to each occurrence; never introduce a library-wide monomorphic substitution.

This first cut gives conventional leaf instances. It is not full Program completeness and should be reported as such.

## Full Program bridge after the leaf cut

A new independent conventional typing judgment should use the EXISTING Program AST and raw Ty. Its rules should be ordinary component-scheme instantiation, rigid query lookup, argument-only scheme instantiation, and application. It must NOT contain TypeIn, source avoid cases, termsRows/relevantRows membership, source table success, or a SourceTermsTyping premise. Those are admission obligations to prove separately.

Specify ordinary query lookup explicitly. Usual last-binding named lookup is a reasonable candidate. Its correspondence to SourceSelections' last singleton key still needs a general source-order theorem; duplicate_singleton proves only the two-entry example. Do not infer full singleton order from a membership-only permutation theorem. Alternatively require distinct query names for an initial clearly limited theorem, while retaining duplicate-name behavior in the generic source model. That would be a restriction on the first bridge theorem, not proof of the unrestricted API.

Normalize the documented Fun/2 arrow alias in the ordinary typing judgment or state type equality modulo that alias. A raw syntactic tFun-only application rule would otherwise omit an advertised source type. Do not reuse source isVariableSymbol to redefine ordinary rigid constructor constants as type variables; expose that mismatch through compatibility conditions instead.

For an ordinary typing derivation, the precise remaining source-admission conditions are:

- Binding origin is the actual group representative, actual argument-only entry, or actual query argument selected by ordinary lookup. A theorem about expanded member names also needs the representative/expand adapter. The source context labels groups by representative, not by every group member.
- Source branch/encoding is FirstOrder for the public API claim. The direct firstOrderRaw function itself does not dispatch on libraryEncoding.
- Each generalized occurrence supplies a compatible simultaneous instance and structurally admitted images only for the demanded original encoded keys.
- Each application result annotation is TypeIn the actual constructor catalog. Do not require every rigid domain, goal, or query argument to be in that universe.
- The role flag is exact at each call. Current root relevant uses true; function recursion uses false and argument recursion uses true. Do not translate this into an unproved claim that argument-only entries are excluded from the root.
- Size2 pruning is checked only when the derivation delegates to a terms cell. Restricted and fallback pools match the exact current avoid entry, including none entries in fallback exclusion. Nonempty relevant recursion follows its own positive splits and offsets.
- Required query argument names are allocated in an actual root permutation, with duplicate multiplicity. At each relevant node use the actual last winner; split its take/drop NAMES and resolve children again. Existing winner-name identity does not imply row identity.

These facts can be represented by a finite static policy/occurrence certificate aligned with the chosen ordinary typing derivation. Such a certificate must contain only source-input eligibility and allocation choices, never future semantic membership or the target SourceTermsTyping itself. A theorem from ordinary typing plus that independently stated policy to source admissibility would be useful. It still would not prove that every advertised ordinarily well-typed input satisfies the policy. That final domain/API theorem must either derive the conditions or report the remaining discrepancies. Defining a predicate as 'there exists the target SourceTermsTyping derivation' would be circular and must not count as this bridge.

## Limits retained

All counterexamples and proposed definitions above are uncompiled source analysis. This audit makes no production Haskell defect/fix claim and changes no public contract. It retains independent per-use substitutions, actual last winners and duplicate occurrences, rigid var_e positional behavior, reserved aliases, Fun/catalog exceptions, and the full original formalization objective. Source totality, source inhabitance, ordinary typing completeness/soundness, native execution, Haskell correspondence, and enumeration/rank properties remain distinct claims.
