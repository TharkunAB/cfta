# One native narrowing argument in the existing shared eager backend

Status: READ-ONLY HEADER/PLAN. No source body, factoring or theorem is checked here.
Authority: committed default-entry plan96, copied with its exact SHA below.

1. Three operation files are sufficient for the narrowing argument.
   SourcePruningEnumerationAction.prepare:17 currently calls OuterNarrow.narrow:11.
   Move its SAME match/action body to prepareWithNarrow. Its argument has exactly the
   old native operation type: Metadata → nativeFuel → uv → value → heap → Result value.
   Keep old prepare as the configured specialization. No hooks record is needed.
   SourcePruningEnumerationSelectedStep.runPrefix:43 calls that action at:64. Move its
   SAME body to runPrefixWithNarrow and pass the operation to prepareWithNarrow there.
   Keep old runPrefix as the configured specialization. Its Result datatype is unchanged.
   RecursiveChildPolicy.resumeWithChild:39 calls runPrefix:53. Move that SAME recursion
   to resumeWithNarrow and carry the ONE argument through parked and callback recursion.
   runWithNarrow mirrors runWithChild:76. runEagerWithNarrow mirrors runEager:88 and
   installs the SAME eagerChild with the SAME five work fuels and edgesOf function.
   Old resumeWithChild/runWithChild/runEager become exact configured wrappers.

2. Keep the existing child/native preparation/callback backend.
   SharedPreparedRecursive.continueWith:74 already accepts its recursive continuation.
   Pass resumeWithNarrow child narrow there; continueWith needs NO operation change.
   SharedPreparedChildPolicy.runWithChild:39 and SharedEagerChildren.eagerChild:134
   inspect no Metadata and run no OuterNarrow. They retain their exact implementation.
   Preserve actual prefix, preparation, own-class, ordered tuple, terminal, finalizer,
   native Caller and COMPLETE Memos. ParkedRestart/Restart and recordTypes stay exact.
   Legacy SharedPreparedRecursive.resume and SelectedStep.run can remain unchanged;
   they call their old configured wrappers. No second child backend or evaluator.

3. Preserve every old mode and result before adding literal defaults.
   operation-headers and wrapper-equations freeze the proposed interfaces.
   Every old wrapper equation is intended to be rfl, at ALL inputs/fuels/templates/
   stop/order/checkEmpty/metadata, including faults and unsupported raw observations.
   Old theorem statements, public inputs and results remain exact. Existing scripts
   that rw[resumeWithChild] may need one explicit new backend-equation unfold. This
   is not a promise that all old tactic bodies remain byte-identical. Strictly check
   the original affected modules, full Audit and portable packets before publication.
   The operation body is moved once, not retained as an independently maintained copy.
   Existing resource theorems remain about their configured wrapper specialization.
   Identity-specialized resource/role receipts need a separate concrete derivation;
   the old theorem cannot simply be instantiated with an extra operation argument.

4. Literal default specialization and callback treatment.
   Set narrow := fun _ _ _ value heap => .done value heap.
   Set templates:=[], stop:=none, order:=fun _ _=>none. Retain actual checkEmpty and
   edgesOf; default Haskell must derive these from the processed/refolded root later.
   Old holeKey/fits/admits do not enter this specialization. No alltrue-filter trick.
   recordTypes_empty:76 then returns false and the exact SAME Core at EVERY fuel.
   pending, typing and openHoles stay exact; types may update on Left fragments.
   Right metadata is already exact by recordTypes_inr:83. Restart.decision:13 now
   ignores ALL metadata. The new identity operation does so too. No other selected
   or eager child control operation reads the type set. Therefore no callback hook
   is needed for an explicit erased observation. Initial pending=[] is supplied by
   the original startup; it is not a new neutrality provider or local erasure gate.
   Keep typesLast and atTypes OUTSIDE this specialization: they read updated types.

5. Full success/error observation and proof stages.
   observation.md specifies maps into EXISTING Unit-indexed receipt datatypes.
   Erase metadata in outputs, exhausted, parked/Right raw observations, callback raw
   and nested alternatives/continuation failures. Preserve EVERY other field, errors,
   raw list order/multiplicity, complete/stopped distinction and SAME native endpoint.
   Erasing exhausted alone is not a total relation on the existing failure datatype.
   Keep the entire original execution receipt alongside the observation equation.
   First derive selected-prefix map agreement by concrete read/check/lookup/action
   cases; identity narrowing uses SAME heap/value and imposes no normal-form gate.
   Then prove private map congruence for the ACTUAL eagerChild height/tuple/row code.
   Existing visitors are polymorphic in Output/Reason and inspect only constructor
   shape, so map over returned outputs/failures commutes with actual continuation
   placement. No existing public map/congr law was found in the six relevant files.
   This is a bounded algebraic lemma, not a second producer/resource proof stack.
   Finish by actual outer recursiveFuel induction, retaining stopped prefixes/zero
   depth/empty rows/faults. Use the concrete lower IH at each callback and parked
   recursion. No arbitrary visitor or metadata-neutral callback supplier is exposed.
   erasure-header gives the precise unconditional initial-metadata equality target.
   Derived concrete callback quotient equation uses SAME output cache/Caller/Queries.
   Its unit false/unchanged equation is the literal oracle's behavior at this layer.
   This quotient control fact is not the complete Haskell correspondence theorem.

6. Remaining primary default entry obligations stay unchanged.
   The authority96 requires actual <=30 reduction rounds, redundancy/refold language
   and physical Program-role transport, then derived flag/order/startup at THAT root.
   It also requires capacity for that whole pipeline, selected finite depths versus
   depth-free Haskell execution, native identities/global interning/laziness, and
   nub-before-projection output order/multiplicity. This plan replaces none of them.
   It supplies no model existence, ordinary typing, partial-Type assignment pullback
   or complete enumeration claim. It establishes no Haskell defect or runtime result.
