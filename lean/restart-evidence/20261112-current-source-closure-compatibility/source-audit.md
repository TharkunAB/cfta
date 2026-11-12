# Current source closure, native guards and eager children

Base: c7e63738b1441c4f17742933f82ddcc64eaebfb0. Integrated main:
e53852064d3ef5a2eafec47d754c27504b11de5f, including PR210/211.
The full formalization goal remains ACTIVE. No production Haskell changes.

## Checked modules

- SourceSynthesisCurrentGuardPreparation: 71 lines; 2 laws; SHA256 39bb9d0408fb4c2c49839a3b66c7489654d00a0f4d41c376bcbe5dabeb0fa012.
  - MicroCFTA.SourceSynthesisCurrentGuardPreparation.mapped_guards_cached
  - MicroCFTA.SourceSynthesisCurrentGuardPreparation.prepared_fields_of_build
- SourceSynthesisCurrentNativeGuardOrigins: 60 lines; 2 laws; SHA256 006e4387eabf71dbb0ad54e1cd351dece004edb9dfae6806612a9be6ef094880.
  - MicroCFTA.SourceSynthesisCurrentNativeGuardOrigins.constructed
  - MicroCFTA.SourceSynthesisCurrentNativeGuardOrigins.complete
- SourceSynthesisCurrentProgramStructure: 258 lines; 1 laws; SHA256 a4b2a7e5ce4b495f414f4bbaafdc2ee54005f1ec5505ba382a5b4ddbbddfae4e.
  - MicroCFTA.SourceSynthesisCurrentProgramStructure.current_root_structure
- SourceSynthesisCurrentSourceGuards: 383 lines; 2 laws; SHA256 2898412f94f94e11e87b7dd2967884f49611d797e6562359d1a0358f836f0f55.
  - MicroCFTA.SourceSynthesisCurrentSourceGuards.firstOrderRaw_guards_plainMu
  - MicroCFTA.SourceSynthesisCurrentSourceGuards.mapped_guards
- SourceSynthesisCurrentTypeFieldCalls: 205 lines; 6 laws; SHA256 fe28ec68e74bdb1bebd5dc8b712c96f7d15c3c0f3ea141038410ed758eb60dec.
  - MicroCFTA.SourceSynthesisCurrentTypeFieldCalls.mapSyntax_allowed
  - MicroCFTA.SourceSynthesisCurrentTypeFieldCalls.allTypes_allowed
  - MicroCFTA.SourceSynthesisCurrentTypeFieldCalls.generalize_allTypes_allowed
  - MicroCFTA.SourceSynthesisCurrentTypeFieldCalls.current_generalized_allowed
  - MicroCFTA.SourceSynthesisCurrentTypeFieldCalls.prefix_muStored
  - MicroCFTA.SourceSynthesisCurrentTypeFieldCalls.component_call
- SourceSynthesisCurrentTypeOperands: 314 lines; 1 laws; SHA256 71216cfd9f56907bf5fd39a7ea128d303550e30f8d78a82bedb3366f4dc62d6c.
  - MicroCFTA.SourceSynthesisCurrentTypeOperands.current_root_type_operands
- SourcePruningEnumerationSharedEagerChildren: 207 lines; 7 laws; SHA256 029464163b7288a5ddbaae95996307fab7acec77e7f70e5a661db948757423eb.
  - MicroCFTA.SourcePruningEnumerationSharedEagerChildren.prepared_child_lt
  - MicroCFTA.SourcePruningEnumerationSharedEagerChildren.consume_complete
  - MicroCFTA.SourcePruningEnumerationSharedEagerChildren.consume_rejected
  - MicroCFTA.SourcePruningEnumerationSharedEagerChildren.ordinary_dispatch_checkEmpty
  - MicroCFTA.SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback
  - MicroCFTA.SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary
  - MicroCFTA.SourcePruningEnumerationSharedEagerChildren.prepared_child_eager

## Exact current source and native contracts

CurrentProgramStructure derives existing ProgramSyntax and ProgramSize from
an actual current root return. All avoid rules and actual table alternatives
are covered. CurrentSourceGuards derives complete guard inclusion in the
once-encoded library alphabet and PlainMu for that same actual expression.
Its encodedLibrary changes only scheme fields, preserving original names,
duplicates, avoid lists and the encoding field. No old/current context equality
or ordinary input-admission assumption is used.

CurrentGuardPreparation derives Cached for every current mapped guard. Its
actual-build observer returns the complete equality preparation Receipt,
actual cache and conjunction Fields on the SAME supplied native heap. It
calls the existing allocator and history observer. No future normalization,
Fields or native initializer is assumed.

CurrentNativeGuardOrigins observes every physical edge guard of that same
build under Derived(encoded alphabet). Its complete law derives one current
source expression and ONE actual native build for each nonnegative request.
It supplies the full physical guard-origin invariant on that build. This
Derived invariant alone does not imply physical projectability. No model,
Type-field classification, worker completion or inhabitance is supplied.

CurrentTypeFieldCalls supplies generic map/Allowed, arbitrary-catalog universe
and generalized-scheme laws. The current specialized scheme law derives its
origin from actual raw group/argument-only membership through encodedLibrary.
The prefix Mu store comes from the SAME current root/build and actual growth.
The component/argument-only RowCall observer retains the SAME physical slot
zero value, availability, closedness and annotation. It calls the generic
hereditary constructor at the actual operand context. No second build or
future annotation/store supplier is introduced.

CurrentTypeOperands adds only two ordered syntax-list observers, paired with
existing ProgramSyntax. They collect singleton annotation, application slots
zero/one then recurse on program slots two/three, filter goal then program,
and union members in order. Duplicates remain. From actual current root
success, current_root_type_operands derives roles and Allowed Origin(encoded
library) for EVERY collected Type instruction. It applies to all avoid rules.
No new ordinary/Program/Relevant typing hierarchy or evaluator is introduced.
The next generic native consumer must transfer those current static operands
through the SAME actual build to existing whole ValueFields.

SharedEagerChildren defines the ordinary nonterminal predicate, complete
selected-receipt consumer and eagerChild operation on checked visitSelected
and scan. It recurses by existing ordinary height. The generic child callback
checks strict decrease; its shallow fallback is unreachable on actual staged
payload children under CURRENT selector membership. The preparation lemma
derives actual projection/readback and strict decrease from the SAME prepare.
The ordinary dispatcher checkEmpty law is FULL raw-result equality. Terminal,
opaque and other fallback cases keep their exact old worker and Boolean.
Callbacks execute complete child-product tails before the next alternative.
The exact row receipt prefixes both successful and stopped continuation
receipts; final Caller/full Memos, outputs and stops remain. Only pure tests
can repeat in fallback. No public depth, cutoff/outcome hierarchy or invented
source error is added.

This is an actual eager child operation and local equations, not the whole
default worker theorem. Canonical root-map/native-row membership correspondence,
all native adequacy/resource receipts, and lazy Haskell demand remain open.
The common driver reaches SharedPreparedContinuations directly; merely changing
the older NativeOrdinaryContinuations wrapper would miss it. The next factor
must preserve SelectedPreparation and the entire Preparation/optional-fold
observation. Existing driver finish drops processed receipts on completed
outcomes; do not attribute pair-level receipt retention to its HookResult.

## Compatibility and reproduction

All seven strict checks pass for twenty-one public laws. Full Audit passes:
5814 live modules, eight affected modules, 4811 Audit imports, 93928 axiom
reports. All 260650 old Audit bytes remain after seven imports. Every prior
source definition and public theorem remains. All eight portable checkers
pass from /tmp. Exact public names/namespaces, source hashes and standard
axioms are checked. Effective limits: memory.max=memory.high=4294967296,
memory.swap.max=0, one Lean thread. Project Nix and the existing repository
Lake cache are used. No binary archive is copied. The six-module intermediate
full/seven-portable receipts remain in the runtime; a new checked source
module caused the final frontier rerun.

Prior Haskell validation/source hashes remain in the preceding compatibility
source audits. Merged main passed Fourmolu and 16 focused SynthesisSpec cases,
zero failures. No Haskell/Cabal file, full-suite or benchmark result changes.

## Haskell findings and full scope

No new Haskell repair or runtime defect is established. FINDINGS retains the
merged namespace, Fun-arity and duplicate-query fixes with exact source pins
and validation. Historical negative packets keep their old hashes and bad
outputs; their checkers must reject the repaired current checkout. Curried
markers and generated-variable admission remain separate. Rigid query/goal
types do not blanket-require universe membership. Liquid synthesis duplicate
reader policies remain under external review. Matching Liquid Haskell pure
contracts can help source correspondence; external proofs do not enter Lean
automatically or certify the compiler/runtime.

The preceding checkpoint retains constructive current whole-root admission
on its raw per-use certificate, empty avoid rules and ORIGINAL query-token
coverage. That proof retains ordinary Typed, actual success/membership, SAME
annotation/projection/count and fixed-original-query permutation mapping.
This checkpoint adds structural source and native construction facts; it
does not establish reverse source soundness or unrestricted completeness.

The remaining hereditary gap is whole native ValueFields from current static
Type operands. The remaining operational gap is common eager driver wiring
and complete resource/model/work receipts. Cold raw initialization can use
these current build/cache facts before a worker; it must remain labeled cold
startup. Its generic Packet/model/work observer does not require Room or
whole TypeFields. Later raw pruning needs the exact computed Room condition;
checked hereditary traversal still needs source-derived whole ValueFields.
No fixed-word Room discharge or full-work bound is inferred from Program
count, startup work or syntax totality.

Continue all earlier hooks/alternatives; original-input work/depth; reduction,
refold/weights; source order/multiplicity; both inverse contracts; full guards,
signed/Word/Int/errors/lazy demand; refinement/training. Annotation size is not
Program count. Default synthesis does not call boundDepth. The goal is incomplete.

Runtime: /tmp/mcfta-current-source-closure-20261112-1523/. R243 root-progress
points here. R243 c7e63738b is published; its board request
8d5bb6ac-eaed-494c-8d8b-7eb3c682f6c3 has canonical sequence1178/total391.
All failed drafts/logs remain, including sourceGuards379->383, nativeOrigins
a352->006e, eager3133->0294, and TypeOperands0e98->7121. Public headers remained
unchanged through repairs. At 15:53 CET, primary usage was 20% and free space
183.9 GiB. Check usage by 16:08. Above 80%, save handoff, pause goal and notify
Matti. Last readable /tmp total was about 35 GiB, excluding six private dirs.
Runtime records remain small text files; no binaries are archived.

Next runtime-only sources are UNVERIFIED: CurrentCallerInitialization (Beta)
and ProgramTypeFieldConstruction (Gamma). Alpha is auditing the exact common
eager driver factor. ROOT alone compiles, runs Git and publishes. Do not pause
the active full goal after publishing this checkpoint.


## Frozen audit: Current Type-field cut

Earlier planning labels are superseded by the checked results above.

# Current Type-field bridge

2026-11-12 15:31 CET. Read-only audit. No source, compiler, repository, Git, Haskell, root-doc, or evidence changes.

## Result

Two small Allowed laws close the pure Type-instruction gap. A new native constructor or annotation engine is not required. The current whole-source PlainMu result already supplies the SAME build's conditional Mu store through public generic laws. The remaining source-composition gap is positional: the current source's Type operands must carry these Allowed facts at their actual ordered row calls. The historical Program/ProgramRow certificate fixes the historical universe and cannot be asserted for the current source.

The references below use `lean/MicroCFTA/` unless a runtime path is given. `E lib` means CurrentSourceGuards.encodedLibrary lib, `Origin` means SourceSynthesisNativeTypeTrace.Origin, `mapSyntax` means ProgramBuildRolesGeneric.mapSyntax, and `ordinarySymbols` is the existing Label caller adapter. CurrentSourceGuards is the frozen 383-line candidate in this directory. ROOT owns its strict result.

## Smallest pure API

The useful generic laws have an arbitrary constructor catalog and guard predicate. Their only guard inputs concern literal CURRENT instructions:

```lean
theorem allTypes_allowed {S : Type} (literal : String → S)
    (valid : Guard → Prop) (validTop : valid top)
    (catalog : List (String × Nat)) :
    Allowed valid (mapSyntax literal (allTypes top catalog))

theorem generalize_allTypes_allowed {S : Type} (literal : String → S)
    (valid : Guard → Prop) (validTop : valid top)
    (catalog : List (String × Nat)) (scheme : Ty)
    (own : valid (eqGuard (equalityClasses scheme))) :
    Allowed valid
      (mapSyntax literal (generalize (allTypes top catalog) scheme))
```

Proof dependencies are already public: EqualityConstraintOrigins.allowed at 45; TypeSyntax.allTypes_guards at 270; GeneralizeSyntax.generalize_guards at 326. The last law says each guard is the generalized outer guard, Top, or a universe guard. No universe-membership, AliasSafe, name-freshness, query restriction, or finite language premise is needed.

One symbol-map helper is private today: OriginalTypeAnnotations.map_allowed at 39, with its two mutual list helpers at 55 and 65. Its exact generic contract is:

```lean
theorem mapSyntax_allowed {S : Type} (literal : String → S)
    (valid : Guard → Prop) (expression : Expression)
    (allowed : Allowed valid expression) :
    Allowed valid (mapSyntax literal expression)
```

Expose or reuse that proof once if an additive generic module is preferred. Do not reference mangled private declarations. Alternatively expose the already duplicated private generic `mapped_inventory` guard equality from OriginalGuardAlphabet at 165; then EqualityConstraintOrigins.allowed gives the mapped result directly. Only ONE of these mapping APIs is necessary.

The source-specialized generalized contract is exact:

```lean
theorem current_generalized_allowed {S : Type} (literal : String → S)
    (lib : Library) (catalog : List (String × Nat)) (scheme : Ty)
    (original : OriginalTypeAnnotations.OriginalType lib scheme) :
    Allowed (Origin (E lib))
      (mapSyntax literal (generalize (allTypes top catalog) (encodeTy scheme)))
```

`original` is actual raw group/argument-only membership, not an output supplier. Map that membership through E's two existing scheme maps (CurrentSourceGuards:25-30). It gives OriginalType (E lib) (encodeTy scheme). Derived.literal then proves the one outer guard belongs to Origin (E lib), exactly as OriginalTypeAnnotations.generalized_origin at 29. Origin's literal pool is NativeTypeTrace.pool at 30, and origin_top is public at 39. Instantiate the generic catalog with CurrentContext.constructorCatalog lib query. Do not equate that catalog or universe with historical typesOf, including typesOf (E lib) of an encoded query.

Rigid fields and markers are ALREADY covered: OriginalTypeAnnotations.rigid_allowed at 93 works with library E lib and raw type encodeTy typ; marker_allowed at 111 works with E lib. CurrentContext.typeNode unfolds to that exact rigid instruction. These laws need no new aliases.

## SAME build and SAME prefix

The missing historical wrapper does not require a missing native primitive. Start with one actual current source return and one actual Label build:

```lean
(accepted : CurrentConstruction.firstOrderRaw lib query signed = .ok whole)
(built : build (ordinarySymbols whole) [] empty = .done rootValue finalHeap)
```

Use CurrentSourceGuards.firstOrderRaw_guards_plainMu at 320, its second projection; NativeTypeSites.mapped_plainMu at 195; LabelProgramBuildRoles.mapSyntax_ordinarySymbols at 26; then NativeTypeSites.build_mu_bodies at 71. The last theorem is generic over syntax and SAME observed build, not historical firstOrderRaw. Its completed Mu bodies are Annotated (fun guard => guard = top). SourceCurrentHereditaryUnconstrained.annotated_mono at 18 (the same call used by NativeTypeSites:225) lifts that to any valid containing Top, in particular Origin (E lib). OriginalPrefixMuStore.muStored_of_grows at 21 transports that SAME final store to each actual earlier heap.

Consequently a current prefix helper needs only the same actual field build, its ordinary Context, and growth into the SAME final heap. It calls HereditaryConstruction.build at 205 once with the source-derived Allowed field. It does not assume a future annotation, store, or model. For a captured call, preserve the actual ActiveOrigins.Path rooted at ordinarySymbols whole and original inputs []; Path.inputs makes every captured environment item a reference. That is already the proof at OriginalTypeAnnotations.captured_build_typed:165-180. A Context plus Grows alone does not establish that a call was an operand of the root; use the actual ordered call receipt for attachment.

The smallest concrete next attached producer is the current component/argument-only Type slot. Its full current source/root/build parameters are above; its new source-site inputs and output are:

```lean
(scheme : Ty) (original : OriginalTypeAnnotations.OriginalType lib scheme)
(call : SourceCurrentStoredMuRetainedAlignment.RowCall
  expressions [] before outputs after finalHeap rowIndex symbol top
  [ordinarySymbols (generalize
    (allTypes top (CurrentContext.constructorCatalog lib query)) (encodeTy scheme))]) :
∃ value, call.output.children[0]? = some value ∧ Available finalHeap value ∧
  value.free = [] ∧ Annotated (Origin (E lib)) value
```

All omitted variables above are the existing RowCall indices and carriers, not extra proof premises. This is the exact shape of OriginalTypeFieldCalls.component_call at 118, with the actual current universe and encoded scheme. For its selected operand use OriginalProgramTypeFields.many_call at 37; it already returns the SAME output index, actual start/finish, current Context, and both growth facts from the actual ordered children receipt. Then use the source-specialized Allowed law and the generic prefix composition. RowCall.children_eq attaches the result to the exact physical row. OriginalTypeFieldCalls.typed_slot at 82-115 already gives the availability/closedness proof pattern through residency and build_free_origins. No second root build is needed.

The universe/marker and rigid-query/goal companions differ only in the fixed current instruction and slot. They reuse the two generic Allowed laws or the existing rigid/marker laws. Argument-only remains a source role; no new name-priority rule is needed.

## Remaining whole-root seam

InitialTypeFields.ProgramRow at 25-38 hardwires typesOf lib query in component and application constructors, original query membership in the rigid argument constructor, and the original goal in the filter. Its ContextFields.types at 43 therefore does NOT hold for current Context. OriginalProgramTypeFields.at_prefix at 236 and OriginalHereditaryProgramFields.at_prefix at 193 consume that exact historical certificate and historical accepted build. Their firstOrderRaw_fields wrappers at 307 and 319 cannot be applied by changing labels or by supplying current ProgramSyntax alone.

Current ProgramSyntax and ProgramSize are now derived for the whole current source. ProgramSyntax.annotated intentionally allows an arbitrary annotation, so roles alone do not imply Type Allowed. Whole-source guard alphabet membership also does not suffice: it includes the application and filter guards, whereas the Type pool contains only Top and actual generalized library guards. A CURRENT positional source closure must attach Allowed to each actual Type operand and recurse on the existing Program positions. Reuse the existing ProgramSyntax/ProgramRowSyntax constructors and physical ValueFields/EdgeFields constructors; do not add another Ordinary Typed, Eligible, Program/Relevant evaluator, or native engine.

The generic physical parts already exist: OriginalProgramTypeFields.many_call:37; AnnotationFieldConstructors.makeNode_fields:21 and makeUnion_fields:62; HereditaryProgramFields.makeEdge_fields:115, makeNode_fields:123, makeUnion_fields:159 and EdgeFields.congr:98. The two historical native induction bodies are largely source-independent after replacing historical row-head classification with the current source-derived Type operands. Exposing a narrow generic constructor/observer interface is preferable to duplicating both native inductions. The direct current component-slot producer above can be checked first while that whole-source positional closure is kept explicit.

No native progress, Room discharge, source-language finiteness, runtime extraction, or whole default enumeration claim follows from these Type-field cuts.


## Frozen audit: Whole Type-operand cut

Earlier planning labels are superseded by the checked results above.

# All current Type operands

2026-11-12 15:42 CET. Read-only design audit. No compiler, source, repository, Git, Haskell, root-doc, or evidence changes.

## Smallest cut

Use a pure ordered Type-operand list observer, paired with the EXISTING ProgramSyntax certificate. Do not add an inductive Program/Relevant typing hierarchy. The current source theorem derives Allowed for every member of that list. A generic actual-build consumer then threads the CURRENT MuStored invariant and returns the EXISTING physical ValueFields certificate. The current whole-root wrapper discharges the initial store with MuStored.empty. An actual prefix wrapper uses the already checked CurrentTypeFieldCalls.prefix_muStored.

The two source observers below are new proposed API, not checked code. All abbreviated module names have the prefix SourceSynthesis. Existing checked code does not currently expose this whole-Type observer.

## Search result and existing boundaries

TypeGuardSites.RowAt:28 records a literal row address through arbitrary child, union, and binder positions. RowAt.guard_mem:82, generalize_site:155, typeNode_top:164, and allTypes_top:170 describe guards inside an ALREADY selected Type instruction. BuiltTypeGuardSites.rowCall_guard_site:33 and generalized_root_row:108 attach those selected Type rows to actual native calls. They do not identify which subinstructions of a whole Program are Type operands.

ProgramRoles.ProgramSyntax/ProgramRowSyntax:20-46 already determine every Program layout. An annotated row has one Type operand. An application has Type operands at zero and one and Program operands at two and three. A filter has a Type operand at zero and a Program operand at one. Literal names can coincide, so a name-based classifier is unnecessary and insufficient. No existing whole-source Type-operand observer or generic native ValueFields consumer over these roles was found.

InitialTypeFields.Program/ProgramRow:17-38 is historical and hardwires typesOf, historical query rows, and the historical goal. CurrentSourceGuards and CurrentProgramStructure deliberately do not assert it. CurrentTypeFieldCalls now supplies all six checked pure/prefix/component laws; do not reproduce them.

## Pure observer

Define only two finite source-data functions. They collect complete Type instructions and retain order and duplicates. They do not evaluate instructions or certify programs:

```lean
mutual
def typeOperands : Expression → List Expression
  | .empty | .var _ | .binder _ _ => []
  | .node rows => rows.flatMap rowTypeOperands
  | .union members => members.flatMap typeOperands

def rowTypeOperands : Row → List Expression
  | .mk _ _ [annotation] => [annotation]
  | .mk _ _ [types, marker, function, argument] =>
      types :: marker :: (typeOperands function ++ typeOperands argument)
  | .mk _ _ [goal, candidates] => goal :: typeOperands candidates
  | .mk _ _ _ => []
end
```

Structural size proves termination. The arity split selects positions only; a separate EXISTING ProgramSyntax proof supplies the actual source row layout, symbols, and guards. The empty cases for var/binder and other row shapes are safe only when the consumer also requires ProgramSyntax. Never use the list alone as a Program-role certificate. A complete Type instruction is collected as one operand, so Allowed checks every nested Type row and binder body without descending into it as a Program.

The exact source theorem needs no semantic/native premise:

```lean
theorem current_root_type_operands
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (returned : CurrentConstruction.firstOrderRaw lib query signed = .ok whole) :
    ∀ field ∈ typeOperands whole,
      Allowed (NativeTypeTrace.Origin (CurrentSourceGuards.encodedLibrary lib))
        (UniverseCallerBoundary.ordinarySymbols field)
```

Its generic local table induction carries only this list-membership property. Current Context supplies it internally: group/argument-only rows use CurrentTypeFieldCalls.current_generalized_allowed; canonical query rows and the filter goal use OriginalTypeAnnotations.rigid_allowed at encodedLibrary and encodeTy; application slot zero uses CurrentTypeFieldCalls.allTypes_allowed at the actual current catalog; slot one uses the existing marker_allowed. The remaining application/filter operands recurse. All avoid branches, ordered unions, and names-only selection use the same closure pattern as CurrentProgramStructure. There is no Eligible, name freshness, TypeIn, source-output, or future annotation premise. Existing CurrentProgramStructure.current_root_structure supplies ProgramSyntax separately, or the new source proof can retain that proof in a conjunction if this avoids another table traversal.

This is a new current-only positional closure. Whole-source guard alphabet and ProgramSyntax alone do not imply it. The former includes Program schemas; the latter intentionally leaves Type annotations unrestricted.

## Exact generic native consumer

The recommended generic header uses the current entry store. It does NOT request stores at future recursive calls or at future heaps:

```lean
theorem build_program_fields {S : Type} [DecidableEq (EdgeKey S Guard)]
    (literal : String → S) (valid : Guard → Prop)
    (expression : Expression) (roles : ProgramRoles.ProgramSyntax expression)
    (operands : ∀ field ∈ typeOperands expression,
      Allowed valid (ProgramBuildRolesGeneric.mapSyntax literal field))
    (before : State S Guard) (context : InternedFreshOrdinaryContext.Context before [])
    (stored : SourceCurrentHereditaryConstruction.MuStored valid before)
    (value : Value S Guard) (after : State S Guard)
    (actual : InternedFreshOrdinaryConstruction.build
      (ProgramBuildRolesGeneric.mapSyntax literal expression) [] before = .done value after) :
    SourceCurrentHereditaryConstruction.MuStored valid after ∧
      HereditaryProgramFields.ValueFields valid literal value
```

Here `operands` is a CURRENT pure instruction property. The public current wrapper derives it from current_root_type_operands; it is not a future worker/model supplier. `stored` refers only to before. At a root use MuStored.empty. At a genuine current prefix use the checked prefix_muStored on the SAME whole build and growth receipt. Do not add a forall-future-prefix store premise.

Prove this by ProgramSyntax.rec using the EXISTING role constructors. A private ordered traversal threads the SAME successful calls, Contexts, and MuStored through every input row and child. For each Type operand, SourceCurrentHereditaryConstruction.build:205 supplies both Annotated at that exact returned value and MuStored at its exact returned heap. For each Program operand, use the induction hypothesis with the store returned by its actual predecessor. Public MuStored.makeEdge:47, makeNode:41, and makeUnion:52 preserve the store independently of Program guards. Thus the whole Program need not be Allowed under the Type-only origin predicate.

Physical attachment uses the actual ordered children and rows, not independent existential annotations: OriginalProgramTypeFields.many_call:37; InternedFreshOrdinarySourceAlignment.buildMany_calls:18/buildEdges_calls:65; actual makeEdge fields; and HereditaryProgramFields.EdgeFields.annotated/application/filter:32-47. Node/union normalization uses HereditaryProgramFields.makeNode_fields:123 and makeUnion_fields:159, with the SAME constructor result, current Facts, residency, and availability. These public laws already retain source order, all Type slots, and recursive Program children. ValueFields.fields:90 then yields the weaker AnnotationFields result without a second proof.

The generic consumer may return the post-store conjunction rather than inventing a carrier. The existing HereditaryConstruction.Checked carrier is also usable internally if it reduces duplication, but pending-outcome preservation is not needed for the stated successful-build theorem. Do not derive values by a second native build or join independently chosen memo/model witnesses.

## Current wrapper and honest endpoint

The final root wrapper takes ONLY the actual current source return and SAME actual Label build:

```lean
theorem current_root_fields [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (returned : CurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (UniverseCallerBoundary.ordinarySymbols whole) [] empty = .done value heap) :
    SourceCurrentHereditaryConstruction.MuStored
      (NativeTypeTrace.Origin (CurrentSourceGuards.encodedLibrary lib)) heap ∧
    HereditaryProgramFields.ValueFields
      (NativeTypeTrace.Origin (CurrentSourceGuards.encodedLibrary lib))
      LabelProgramBuildRoles.literal value
```

Use current_root_structure, current_root_type_operands, mapSyntax_ordinarySymbols, empty_context, and MuStored.empty once. This consumes the observed native build; it does not produce a different build or assume a future field result. Every physical Type operand and recursive Program operand is covered by ValueFields. For a later source prefix, retain the exact call/context/growth and apply the same generic consumer with the source-derived prefix store.

No missing constructor or Mu-store primitive was found. New proof work is the narrow pure operand observer/closure and one generic consumer over existing roles. Current-source cache/projectability closure, whole worker completion, Room discharge, generated finite rank, default eager-order correspondence, and Haskell extraction remain separate.


## Frozen audit: Cold/raw startup cut

Earlier planning labels are superseded by the checked results above.

# Current raw caller and startup

Audit time: 2026-11-12 15:48 CET. This is a read-only source audit.
All source paths below are relative to `lean/MicroCFTA/`.

## Result and smallest next cut

A current raw cold caller can now be constructed from current source success.
Its universal initial Packet/model/work observer can attach before any native
worker and before whole Type-operand closure. This result needs no Room test.
The startup value is the original built value, not a pruned worker result.

The smallest next module is a current counterpart of
`SourceSynthesisOriginalCallerInitialization.accepted` (`:26`). Keep its complete
output. Change its source-success premise to
`SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression`.
Its public inputs remain `lib`, `query`, `signed`, `expression`, that actual `.ok`
identity, `width`, an arbitrary valid initial equality cache, `formulas`, and
`solver`. No native build, Context, normalization, Fields, model, or completed
worker is a caller supplier. The closed current root producer already obtains
the `.ok` identity on the nonnegative signed domain.

The complete initializer output should retain one actual build and:

* the full equality preparation Receipt and its actual returned cache;
* conjunction Fields for that same heap/cache;
* `Context formulas solver (inventory expression value heap built)` at
  `caller width cache heap` with the exact modeled `globals`;
* Facts, Available, ProgramValue, growth from empty, and issued-ID extension;
* the exact live empty inherited value and its EqReady proof;
* root closedness and Original;
* the current physical Derived(encoded-alphabet) heap invariant, already
  available as an observer of this same build.

Do not call both the old native-build producer and the new one. Choose the
actual expression once, invoke `closed_complete` once, and apply observers to
that build. Alternatively, use `CurrentNativeGuardOrigins.complete` once for
the nonnegative wrapper and retain all its returned data.

## Exact producer chain

1. `InternedFreshOrdinaryClosedCompletion.closed_complete` (`:50`) supplies the
   actual closed build. `InternedFreshOrdinaryFacts.closed_verified` (`:143`)
   supplies Facts, Available, growth, and issued history at that same return.
2. `SourceSynthesisCurrentProgramStructure.current_root_structure` (`:235`)
   supplies ProgramSyntax and `ProgramSize signed.toNat`. Feed its role proof
   into generic `SourceSynthesisProgramBuildRolesGeneric.build_mapped_program`
   (`:403`), at empty environment/state. The existing
   `mapSyntax_ordinarySymbols` equation gives the actual caller build identity.
3. `SourceSynthesisCurrentGuardPreparation.prepared_fields_of_build` (`:51`)
   supplies the actual full Receipt and conjunction Fields. It derives the
   normalized payload facts internally. Its inputs are the same current output,
   valid initial cache, and actual build identity, not future Fields.
4. `SourceCurrentAllocatedPartialInitialization.constructed` (`:106`) takes
   that Receipt's `history`, initial validity, the actual mapped expression,
   reflexive guard coverage, and the same build. It returns the full Context,
   exact inherited live value, EqReady, Available, closedness, and Original.
   Its `inventory` (`:65`) is computed from that same actual build.
5. `SourceSynthesisCurrentNativeGuardOrigins.constructed` (`:23`) observes
   that build and gives the full physical Derived(encoded-alphabet) invariant.
   It does not allocate or run another build.

The resulting Context contains ready/admitted/sound/stored/covered/correct/
globals/probes (`SourceCurrentAllocatedPartialInvariant.lean:27`). Initial
readiness already includes Good, semantic readiness, costs, scoped native
caches, and idle cells (`SourceCurrentConjunctionClassScan.lean:110`). The global
memo validity is the exact modeled empty-global initial state; this is not a
claim that Haskell resets its global caches at runtime.

## Universal startup attaches now

The existing generic consumer is
`SourcePruningEnumerationRecursive.initial_packet_models_origins_work`, defined
in `SourcePruningEnumerationInitialModelWork.lean:52`. Its exact input sequence is:

```text
formulas solver inventory caller memos metadata value
context : Context formulas solver inventory caller memos
available : Available caller.checked.native.machine.heap value
closed : value.free = []
emptyPending : metadata.pending = []
```

Pass the newly constructed raw cold Context, the same root value, and its
derived availability/closedness. The result retains exact handle/lookup,
initial slot, Packet, canonical/waiting facts, candidate expansion, graph and
reference carriers. It also gives, for every accepted term of that same value,
a satisfying assignment, refutation of pending groups, AssignmentOrigins,
exact pending size `N`, and work
`(N + 1) * N + (if recursiveBoundary value then 0 else 1)`, where
`N = NumberedTerms.size term`.

The Packet is unconditional on language inhabitance. Its model/work observer
has the ordinary accepted-term premise and derives the assignment; it does not
request a model supplier. Empty source languages yield no existential model.
No Type-origin Ready, ValueFields, worker completion, or Room occurs in this
generic startup consumer's input list.

Current component counts can attach to each accepted term through generic
`SourceSynthesisOriginalProgramTermSize.build_accepted` (`:34`) and the derived
current ProgramSize proof. This is the same build. It does not bound `N`.

For an ordinary-specific existential witness, the checked
`SourceSynthesisCurrentRelevantAdmission.uses_root_member` (`:296`) already
supplies current root success and the same whole term under current Eligible,
original token coverage, and empty avoid. Its goal annotation is
`candidateRigid query.queryGoal`. `InternedGuardedExecution.closed_language`
(`:201`) transfers that exact term into the same raw built value, after which
the universal startup observer supplies its model/work witness. No full
Type-operand closure or old/current context equality is needed for this route.

## Physical projectability and Type readiness

Physical projectability is also source-derived on this initial build. The
small missing current observer is the literal-alphabet version of historical
`SourceSynthesisNativeGuardOrigins.initial_heap` (`:63`). Apply generic
`SourceEqualityAnnotationConstruction.build` (`:55`) with the predicate
`guard ∈ alphabet (encodedLibrary lib)`, using current `mapped_guards` and
`SourceEqualityConstraintOrigins.allowed`. Then
`SourceSynthesisOriginalGuardsProjectable.alphabet_projectable` (`:65`) derives
each physical guard's present source payload. This uses the same build.
It is not required by the minimal Context-to-Packet call above.

Do not infer projectability from Derived membership alone: conjunction origin
does not assert that normalization returned a present equality payload.
The stronger literal-alphabet observer is available specifically before the
worker from the actual source construction.

Even cold Type/SharedReady need not wait for whole Program Type-field closure.
Use checked `SourceSynthesisCurrentTypeFieldCalls.prefix_muStored` (`:121`) with
`Origin (encodedLibrary lib)`, `origin_top`, the same build, and `grows_refl heap`.
Feed it to `SourceCurrentHereditaryNativeUniversalStore.initial` (`:29`). Combine
the raw Context's readiness fields to construct
`SourceSynthesisNativeTypeClosedRequests.Ready`; use
`SourceSynthesisNativeTypeSharedState.initial` (`:37`) with empty memos for
shared readiness. Empty memo typed/physical laws and costs are already generic.

The remaining source gap is the entire current Program's `ValueFields`.
The generic hereditary traversal already proves preservation, once that initial
certificate is derived. Ordinary ProgramValue does not certify every Type
operand. The checked current component-call theorem is one field case, not this
whole-program conclusion.

## Later raw worker and the full checked objective

A Room-conditional raw worker composition can follow without ValueFields.
The actual build and empty tables derive all initial support, union normality,
causal publication, parent-origin, closed-store, and idle premises as in
`SourceSynthesisOriginalSharedRankCompletion.accepted` (`:46`). Derive Frame
with `SourceCurrentConstructedOuterInitial.frame` (`:38`). Use generic
`SourceCurrentSharedOuterRankAdequacy.initial_node_call` (`:177`) for the
actual stable run under its computed, single forecast-cover Room test.

Retain the graph, endpoint reads against globals, Post, Frame, Fits, full guard
carrier, Available, and NodeLaw from
`SourceCurrentSharedOuterInitialActual.node_call` (`:439`). Derive result
closedness independently with `SourceCurrentSharedOuterClosedInputs.node_call`
(`:449`), using the same actual run and already derived initial invariants.
Its returned Post.Context, Available, and closedness then feed the same startup
consumer at the pruned result. No Type readiness is needed by this raw path.

Literal numeric range Checks also have generic consumers:
`SourceCurrentSharedOuterInitialLiteralRanges.node_call` (`:308`),
`SourceCurrentAllocatedSharedPartialChecksFromRanges.node_call` (`:283`), and
`SourceCurrentAllocatedSharedPartialRangesFromChecks.node_call` (`:273`). These
are distinct from checked hereditary Type fields.

The full hereditary endpoint still requires source-derived whole ValueFields
for the `classified` premise of
`SourceSynthesisHereditarySharedOuterTraversal.nodeCall_fields` (`:592`). Retain
that gap and the complete Room/graph/global/typed-history/model/work objective.
Cold startup is a smaller valid result; it does not prove the later worker ran,
that a fixed word width satisfies computed Room, or that enumeration completes.

No code, compiler, Git, Haskell, repository, or evidence changes were made.
