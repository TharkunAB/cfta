# Next same-observation driver and source witness cuts

These audits describe remaining proofs. They are not verified whole-driver
or original-program witness results. The checkpoint header records checks.

# Exact work through the common selected prefix

2026-11-11 23:01 CET. Read-only audit. No source edits, builds or Git. Four focal files: SourcePruningEnumerationNativeWork, ParkedActiveCount, ParkedProgress and PrefixMass. Other references are their literal primitive/pure dependencies.

## The measures

NativeWork.work:21 is W_B(cache,sigma)=(B+1)*P(cache,sigma)+A(cache). P=EnumerationStorageProgress.pendingSize counts NumberedTerms.size(sigma slot) at EVERY .unenumerated(some handle) slot. It ignores that slot's handle and bucket. A=IndexSelection.candidates.length uses (range counter).filter expandable. It DOES NOT remove waiting/blocked entries. Keep B and sigma fixed across the prefix.

This distinction matters: parking can unblock other offered slots when it removes waiting counts. Their active flags were already counted in A, so this does not increase A. Do not use the length of the unblocked offered list as A.

## Parked: P stays equal; A loses exactly one

Recursion.checkRepeated:17 clears a bucket ONLY after an actual native recursive boundary and repeated recursionKey. It writes .unenumerated(some SAMEhandle)[] at the current representative. Current chosen selection and Ready.root identify that representative with uv. It does NOT complete, eliminate, or replace the slot with none. Therefore P_after=P_before for ANY fixed sigma, including the positive assigned weight still attached to this marker.

ParkedRestart.adapt:95 performs the literal NativeIndex.write, then frames the SAME checked core. NativeIndex.candidate:17 classifies a recursive boundary with [] as false; write:41 changes only target's expandable flag. Counter is fixed. Selection.offered:11 gives before.expandable uv=true and uv<counter from the ACTUAL chosen decision. Thus after.expandable other = if other=uv then false else before.expandable other, and A_after+1=A_before. Consequently W_B(after,sigma)+1=W_B(before,sigma), for any B. No model or current P<=B is needed for this local equality.

EXISTING public ParkedActiveCount.selected_complete_with_order_progress:44 proves that exact A+1 equation, full flag shape and original parked receipts. selected_complete_with_restart_progress:132 adds the configured restart observation. ParkedProgress.selected_complete_with_parking_progress:22 gives the weaker strict inequality. These producers choose their own sufficient read/check observations: do NOT silently identify their existential cache with a separately observed R223 parked cache.

The missing bounded bridge is an observer of the literal runPrefix receipt already returned by R223. Decompose its PrefixValid parked fields into the actual read/check plus after.core=checked, and invert its ACTUAL runPrefix equation to get ParkedRestart.adapt at the observed index fuel. Derive the flag equation from that literal write, rather than introduce a second parked existential. The private candidates_clear_count proof in ParkedActiveCount is the small pure counting pattern to reuse.

For P use StorageProgress.values_set_pendingSize:109: old and new are both Some slots, so their sigma-weight cancels. Representative/getValue frames preserve values; StorageCallbackProgress.frame_pendingSize:16 handles those frames. PrefixMass.parked_mass:96 is about suspended bucket LENGTH, not P; it cannot supply the required equality by itself.

## Narrowed: tag-neutral, generally NOT a values Frame

A successful live narrowing may write .unenumerated(some newHandle) SAMEscs in place of .unenumerated(some oldHandle) SAMEscs. The values array can change. Do not claim full Frame before.core after.core or exact values equality for this prefix.

The false check is framed by RecursionOrder.checkRepeated_false_frame:11. Action.prepare:17 is either pure() for the same handle or representative followed by that literal Some-to-Some setValue. Thus P_after=P_before, again for any fixed sigma. NarrowAdapter.adapt:10 either keeps all flags or makes the one NativeIndex.write at uv; other flags and counter are unchanged. The selected old flag was true, so its new Boolean flag cannot increase A. Hence A_after<=A_before and W_B(after,sigma)<=W_B(before,sigma). This sufficient nonincrease statement does not need a stronger classification of every possible new native value.

NarrowCache.complete_after_frame:17 retains the exact same-handle/frame versus changed-handle/write split. PrefixMass.narrowed_mass:112 and retained_le:242 already demonstrate extraction of the actual action endpoint from runPrefix; substitute pendingSize's Some-to-Some equality for their suspended-mass argument. Preserve the literal actual equation when matching receipt fields. Right recordTypes(.inr handle) is pure(false,metadata); PrefixRightIdentity.narrowed_right_identity:25 pins its core. NativeWork.recordTypes_work:26 also preserves W at every successful callback, but physical cost preservation alone proves no Left callback model compatibility.

## Common preparation is exactly work-neutral

The SAME R222 carrier packet gives entered.values=before.values, entered.counter=before.counter and entered.expandable=before.expandable. Therefore P, A and W are equal at that actual endpoint for fixed sigma/B. It changes the native heap and can change other enumeration fields; no alternate preparation producer is needed. RenderStable (EnumerationDriver:664) also retains class equivalence, not just values.

Chosen selection supplies IncomingAvoid through Restart.selected/Selection.unblocked_incoming. Recursion.complete and NarrowCache.complete_after_frame preserve actual incoming-reference facts through the clear/replacement. For common preparation use its SAME RenderStable.values/classes to transport references, or the corresponding pure frame helper where an actual Frame is available. Values equality alone is insufficient to transport representative-class avoidance. Ready alone implies neither chosen nor waiting=None nor IncomingAvoid.

## Small next producer

Suggested component retained_work uses EXACT PrefixMass.retained_le-style inputs: original policies/metadata/caller/memos/cache, CURRENT Packet, ACTUAL chosen decision, the SAME PrefixValid and literal runPrefix equation, plus arbitrary sigma and B. Its returned match is:

* parked(some after): same counter, P equality, exact cleared-flag equation, A_after+1=A_before, W_after+1=W_before;
* narrowed(some after): same counter, P equality, A_after<=A_before and W_after<=W_before;
* no retained cache: True, with no failure-state decrease claim.

PrefixValid is an internal receipt from R223, not a new top-level future supplier. A current-only wrapper can derive it with the unchanged prefix_complete producer and return these facts for all sufficiently large common prefix fuels. Prefer applying the observer to R223's EXISTING bound/receipt, so its SAME heap/cache/global model packet is retained. Both shared drivers call this identical SelectedStep.runPrefix; no old ordinary/recursive executor cast is involved.

R223 transports the SAME sigma and origins through the prefix, so an original P<=B remains valid after it and common preparation. The existing SharedCapturedWork.complete_models_resources_work_prepared then supplies the strict captured branch using its actually derived extended assignment. Do not reset the coefficient B at later states. Parked native boundary slots may retain positive P when the scheduler is done; no scalar-zero or all-markers-ordinary conclusion follows. Opaque routes, policy/callback completeness, recursive induction and uniform work-fuel bounds remain separate.


# Generic annotated app/filter witnesses

The next small module can prove generic application/filter membership and Program projection from current child witnesses. It needs no whole-build membership premise. After that, mutual source-selection typing remains necessary to connect the annotated tree to actual termsRows/relevantRows/firstOrderRaw.

Four focal Lean files: SourceSynthesisFirstOrderConstruction, SourceSynthesisFiniteApplicationWitness, SourceSynthesisProgramTermSize and SourceSynthesisFiniteTypeWitnesses. Pure dependencies below supply path composition, PCS normalization, source counts, traversal equations and closed construction. The Haskell layout was also checked at cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:592-611. Its API names, like Lean's, are application and ofType; no separate appType declaration was found. This is a read-only plan; no source/build/Git change or new Haskell defect claim.

## Exact current application law

FirstOrderConstruction.application:47 is ONE app row with children [types,arrowMarker top,function,argument], and the three classes [[[1],[2,0,0]],[[3,0],[2,0,1]],[[0],[2,0,2]]]. Let marker=(->)[], arrow(domain,codomain)=-> [marker,domain,codomain], and joint=app[codomain,marker,f,a], with all symbols mapped by the actual literal label.

A proposed application_member header takes formulas/solver, catalog, current function/argument expressions F/A, current terms f/a and encoded domain/codomain. Its only semantic child premises are evaluate PCS [] (mapSyntax literal F) f and evaluate PCS [] (mapSyntax literal A) a. It also takes CURRENT equations f.atPath [0]=some(arrow domain codomain) and a.atPath [0]=some domain, plus TypeIn catalog codomain. It concludes actual evaluate PCS [] (mapSyntax literal (application (allTypes top catalog) F A)) joint and joint.atPath [0]=some codomain. These local child semantic premises are the induction hypotheses of the future source derivation, not a future whole-build witness.

The exact common subterms for the three classes are:

| Class | Witness |
| --- | --- |
| [1] = [2,0,0] | marker |
| [3,0] = [2,0,1] | domain |
| [0] = [2,0,2] | codomain |

Language.Term.atPath_append:445 composes the two current annotation equations with arrow paths. EqualityNormalize.Satisfies/ClassSat:34/30 and PathsEqual:458 then produce all three classes internally. Do not ask for the generated guard or for each equality as another input. GeneralizeSyntax.eqGuard_eq_source:113, PCSGuard.normalize_sat:20/holds_exact:45 and PCSConstructors.top_true yield the actual guard test. FiniteApplicationWitness private eqGuard_true:138 shows this exact conversion. Its node_member:104 and application_equalities:126 show the assembly, but cannot serve as public generic laws.

TypeIn.member:35 supplies codomain's actual universe membership. The marker accepts its single Top leaf. The two child memberships complete the four-child forest, so the singleton app row accepts joint. No TypeIn domain premise is needed: a rigid query function may have a domain outside the recursive universe, while its current result slot still has admission. Do not require that every operand annotation lies in allTypes.

## Exact filter and leaf laws

FirstOrderConstruction.ofType:52 is filter with children [goal,candidates] and class [[[0],[1,0]]]. Proposed ofType_member takes current goal/candidate terms g/p, their respective expression memberships and the current equation p.atPath [0]=some g. It derives the class with witness g and concludes membership of filter[g,p]. Specialize goal to typeNode top queryGoal and g to rigidTerm queryGoal using FiniteTypeWitnesses.typeNode_member:97. No TypeIn g requirement is valid in general; rigid var_e and nonarrow Fun arities remain legal at this slot.

A generic component_member can take a current component name/scheme, a substitution local to THIS occurrence and TypeIn images for variables scheme. generalize_member_of_TypeIn:140 gives its type-child membership, and a Top singleton row gives name[instantiate sigma scheme]. A rigid argument_member uses typeNode_member and gives name[rigidTerm typ]. Which source row is permitted remains a separate current selection fact. Repeated component occurrences can use independent substitutions; aliases within one occurrence share actual encoded keys.

## Program projection and source count

Use existing ProgramTermSize.Program and Projection, not a second AST. Given Projection literal Prod.fst f pf and Projection literal Prod.fst a pa, Projection.application codomain marker supplies Projection joint (Program.app pf pa). Projection.filter g preserves the candidate Program; Projection.component supplies each leaf. Program.components:30 immediately adds function/argument occurrence counts; a filter adds zero and a component contributes one. Projection.toProgram_eq:61 identifies the actual decoder. No native worker execution or output-model supplier is involved.

These projections alone do NOT establish source-table selection. The later derivation must also obey FirstOrderConstruction.termsRows:84 (asArgument, size2 avoid rows/fallback, positive size splits), relevantRows:112 (actual last-name winner, offset take/drop, re-resolution) and root permutations. SourceSize.termsRows_size:234/relevantRows_size:240/firstOrderRaw_size:247 and ProgramTermSize.accepted_projection:155 validate counts of an ALREADY accepted actual expression, including its selected Program. They do not prove inhabitation or identify an arbitrary recursively assembled tree as an actual source alternative.

## Exact table-to-closed-language bridge

First prove the future TermsTyping semantic induction against the actual termsRows equation, retaining some expression IN that current row list and its accepted annotated body. For RelevantTyping, invert the SAME literal relevantRows=.ok rows equation and prove that body's membership in union rows. At each successful mapM use SymbolicDriver.mapM_success_all₂ (declared SymbolicNormalization:283) to retain its actual input/output pairing; extract the chosen split/offset/permutation's result from that All2 relation. List.mem_flatten then includes the selected current row in the actual flattened table result. Generic union_member follows mapSyntax/evaluate, mapChildren_eq_map and List.mem_map as in the fixture's private union_member:117. Existing role/size theorems are useful cross-checks, not this semantic table theorem.

Finally invert the given nonnegative firstOrderRaw=.ok expression equation. It is ofType (union chunks.flatten) (typeNode top queryGoal), where chunks is the SAME successful traversal of root permutations. The preceding table derivation supplies the candidate member, and ofType_member supplies its joint filtered term. No direct identification of a simple application AST with firstOrderRaw is justified before these selection equations.

At the SAME actual native build equation, LabelProgramBuildRoles.mapSyntax_ordinarySymbols:26 rewrites ordinarySymbols expression to mapSyntax literal expression. InternedGuardedExecution.closed_language:201 gives meaning PCS ambient builtValue = evaluate PCS [] mappedExpression. This is the exact language bridge; firstOrderRaw_build_roles describes roles, not an accepted term. FiniteApplicationWitness.build_member:214/native_witness:230 exhibit the same bridge for the fixed fixture.

A separate source-totality theorem must construct the .ok equation if it is not already supplied. A chosen inhabited branch is insufficient because mapM evaluates ALL alternatives. Ordered-selection take/drop lookup closure and relevantRows totality are finite syntactic obligations; unused branches need no models. The generic assembly module should not attempt these or hide them behind future lookup callbacks. Full original source typing, Curried construction, later branch/pruning coverage, opaque retention, adequate driver depth and native capacity remain open at their separate cuts.


# One opaque head packet with its installed model and work decrease

Read-only audit, 2026-11-11 23:09 CET. Source prefix below is
lean/MicroCFTA/SourcePruningEnumeration. No source or compiler changes.

Focal files: SharedSelectedOpaqueResources:47-103,
SharedPreparedFiniteOpaqueResources:63-129,
SharedNonterminalChildModels:28-83, and FinalizeLanguage:19-44/47-90.
Pure dependencies are Nodes.available_readback:35, Origins.install_origins:72,
EnumerationCompleteness.stored_satisfies:26, EnumerationFrame.neutralize_satisfies,
StorageProgress.opaque_transfer_pendingSize:244, and the closed R223 observer.

## Smallest honest public producer

Add an opaque-specific wrapper of
SharedSelectedOpaqueDispatch.opaque_complete_resources. Keep its exact current
resource inputs/entire packet and add:
- recursiveBoundary value=true and current scs.any isTerminal=false;
- before.expandable target=true;
- ambient, assignment sigma, whole, current Satisfies at caller.heap,
  AssignmentOrigins whole before.counter sigma;
- CURRENT prepared acceptance: meaning holds ambient value (sigma target).

This is a current accepted opaque value, not an assumed successful observation,
post-state model, future equality, work decrease, or callback verdict. The two
opaque gates derive dispatch=false. ProperState of the currently stored bucket
can discharge nonterminal; actual chosen plus valid flags discharges active.
Ready alone does not discharge active. The original stored handle stays the
resource theorem's handle. It need not equal the prepared handle.

Desired sole new law, e.g. opaque_complete_models_resources_work, returns all
existing witnesses bound/receipt/reached/saved/final/next and their ENTIRE
resource packet, followed by the SAME receipt's complete fragment/cache and
one canonical extended assignment:
  sigma' = install sigma before.counter [sigma target],
  agreement below before.counter,
  Satisfies sigma' before.core and after.core at their actual heaps,
  fill sigma' fragment = sigma target = sigma' target,
  AssignmentOrigins whole after.counter sigma',
  all supplied scs still Hold sigma' (sigma target),
  pendingSize after.core sigma' = pendingSize before.core sigma,
  work B after sigma' + 1 = work B before sigma, for every B.

The last equality gives strict scalar decrease without an extra P<=B premise.
The new assignment is the existing child's installed witness, not a second
model chosen to satisfy a separately produced finalizer result.

## Concrete proof and endpoint coupling

1. Call opaque_complete_resources ONCE. Keep its global bundle, Post, Fits,
   carrier, Admitted/Pending/FragmentHistory and completed Packet unchanged.
   Do not reconstruct globals from a second resource producer.

2. Extract current paths/counts/storage/realized/flags from packet.valid and
   coherent from packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent.
   stored_satisfies supplies ALL inherited Holds for the chosen sigma target;
   Ready bounds their referenced IDs. Its inside proof gives the chosen origin
   from the current AssignmentOrigins. Nodes.available_readback derives the
   prepared encoded/decoded handle from current coherent/available/closed.

3. Invoke ChildDispatch.nonterminal_models_origins:28 once with that chosen term.
   It gives explicit install equality:70, old agreement, BOTH child-entry/child
   models, full-bucket Holds, fresh fill and origins. This child operation is
   forward existence even when opaque storage drops its bucket. No old executed
   child result or backward bucket restoration is used.

4. SharedOpaqueBucketBoundary.run_exact identifies this modeled child's FULL
   observation/cache with the resource child's observation at any shared bounds.
   Use it both for the child's modeled bound and the resource bound; arbitrary
   first-four fuel reindexing is unnecessary. The resource theorem's alternatives
   are complete/stopped/rejected, with no finalizeStopped at adequate bounds.
   The opaque nonempty value and actual singleton child rule out stopped/rejected
   directly by the literal opaque run/finalizer cases. This derives a complete
   head; do not add completion as a public premise.

5. The returned FinalizationAt:47-62 already pins the SAME resource middle cache,
   the actual finalizer at bound+extra, and its all-assignment final equation.
   Align the modeled child cache with that middle via the exact observation.
   Apply neutralize_satisfies to the child model, then FinalizationAt's reverse
   implication with fresh fill and old-target agreement. This derives the final
   Satisfies at the SAME physical heap/cache. Finalizer counter preservation
   transfers the child AssignmentOrigins. The returned child caller/query are
   entry identities, as also proved by R223 complete_candidates.

6. Derive CachedChild.allocate heap (some preparedHandle) before =
   some(before.counter, SharedOpaqueBucketBoundary.after preparedHandle before)
   internally from candidate(...,[]) = some false (decoded+boundary) and its
   literal definition. Together with the resource's actual finalizer, canonical
   fresh value and agreement, StorageProgress.opaque_transfer_pendingSize gives
   P equality. Its ORIGINAL stored handle and fresh prepared handle are separate
   parameters. No future middleStored or Protected input is required.

7. Apply CLOSED SharedOpaqueWork.complete_candidates at one actual returned bound
   using stored/active/aligned/flags and encoded/decoded/boundary/nonterminal.
   Keep its candidate-drop proof; do not reprove it. Unfold NativeWork.work and
   combine it with P equality. No candidate upper bound or initial budget is
   needed for this opaque equality-and-one-unit-drop calculation.

## Genuine source ingress and finite-hook boundary

The necessary prepared acceptance already has a source producer:
SharedPreparedBranchModels:171-184 consumes ONE actual
SelectedPreparation.complete_resources_carrier result, then its satisfaction
relation derives enteredModel, enteredOrigins and accepted prepared value.
These facts precede its ordinary-only continuation. Reuse that same setup for
an opaque branch. Do not replace the stored native handle by the prepared one,
or claim acceptance of an unrelated current value. Its exact entry flag/counter
frames can retain the original chosen flag at the entered cache.

SharedPreparedFiniteOpaqueResources calls the head resource producer at137-140,
then already executes the callback/smaller-depth recursion at168-173. Its local
complete-head Packet is available at102-105, and FinalizationAt remains129.
A later adapter can append the model/work facts AT THAT head receipt while
retaining its finite resource bundle. It cannot assert that every final output
still uses the single freshly installed sigma': later recursion allocates again.
Prefer proving the head wrapper first, then feeding its same Packet/Post into
the existing hook induction. Do not run head and finite resource producers and
identify their globals merely from physical endpoint uniqueness.

No public forward semantic opaque-finalization producer currently supplies this
whole package. SharedPreparedOpaqueLanguage's retained-bucket backward theorem
has a separate side condition and cannot supply the forward install witness.
No whole-driver model, arbitrary callback acceptance, bucket backward soundness,
source capacity/depth, or default Haskell API correspondence follows here.
