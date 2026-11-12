# Current input admission and ordered native scan

Base: a75af3a25fba672b807960f38d8b8f0a4830e3d8. Integrated main:
e53852064d3ef5a2eafec47d754c27504b11de5f, with PR210/211 merged.
The full formalization goal remains ACTIVE. No production Haskell changes.

## Checked modules

- SourceSynthesisCurrentGroupAdmission: 137 lines; 2 laws; SHA256 c194a61c99b1c36e9788621634104e486ae5286f03923fb588cdcc28c1f53435.
  - MicroCFTA.SourceSynthesisCurrentGroupAdmission.group_member
  - MicroCFTA.SourceSynthesisCurrentGroupAdmission.argumentOnly_member
- SourceSynthesisCurrentTypeAdmission: 238 lines; 2 laws; SHA256 e8eaaff31ec99062ec10c2c4492b4e6c18400c62a4c893932c9158392107301b.
  - MicroCFTA.SourceSynthesisCurrentTypeAdmission.typeIn_iff_admitted
  - MicroCFTA.SourceSynthesisCurrentTypeAdmission.universe_member_iff_admitted
- SourcePruningEnumerationSharedBranching: 118 lines; 5 laws; SHA256 bd52ff31dbe6707457658aa21245276e9b6407dcd104c8fe088d2eda38d4f1d7.
  - MicroCFTA.SourcePruningEnumerationSharedBranching.scan_nil
  - MicroCFTA.SourcePruningEnumerationSharedBranching.scan_stopped
  - MicroCFTA.SourcePruningEnumerationSharedBranching.scan_complete
  - MicroCFTA.SourcePruningEnumerationSharedBranching.scan_pruned
  - MicroCFTA.SourcePruningEnumerationSharedBranching.run_eq_scan

## Exact scope

CurrentGroupAdmission retains original ordinary Typed and one actual current
size-one termsRows leaf. It retains the exact candidateRigid(substTy rho
scheme) annotation, Projection, toProgram and component count one. Group
bindings and argument-only bindings use their original library origins.
Argument-only requires the actual argument role. The only image premises
are genuine per-use TypeIn facts for variables demanded by the encoded
scheme. Checked substitution/alias safety are derived once. No name
freshness, query uniqueness or future whole-program admission is assumed.

CurrentTypeAdmission defines one structural RawAdmitted predicate. It proves
TypeIn(currentCatalog,candidateRigid typ) iff RawAdmitted(currentCatalog,typ).
Its semantic corollary uses the actual current context.types and the exact
type-universe theorem. The criterion has exactly the raw rigid variables
a,b,c,d; recursive current escaped constructor signatures; and the Fun/2
arrow alias. Catalog separation follows from the current factory. It is not
an extra public premise. Apply this criterion only where the source demands
a universe image or application result. Rigid query leaves and goals do not
blanket-require it. This does not yet prove every arbitrary generated term
is a candidateRigid image; that is the next type-reification target.

SharedBranching.scan runs an actual supplied visitor at the same captured
Cached for each sibling. The complete continuation endpoint supplies native
Caller and full query Memos to the suffix. Processed receipts and outputs
append in order. A stopped prefix stops the scan. A completed empty output
still supplies its native effects. visitCaptured executes the existing
CapturedEdge.run/advance/endpoint/hook path. run_eq_scan is equality of the
ENTIRE existing Result, not an output projection. Existing result/stop/hook
carriers are reused. Optional absent endpoints and stopped receipts remain.
The existing worker and shallow child operations are unchanged. The factor
alone does not implement eager recursive children or settle lazy demand.

## Compatibility and reproduction

Strict checks pass for all three modules and all nine public laws. Full Audit
passes: 5801 live modules, four affected modules, 4798 Audit imports and
93653 axiom reports. All 260153 old Audit bytes remain after three imports.
All four source/compatibility checkers pass from /tmp. The effective limits
are memory.max=memory.high=4294967296 and memory.swap.max=0. The checks use
project Nix, one Lean thread and the repository Lake cache. No binary archive
is copied. Each own-source check emits explicit #check and axiom reports for
every public law. The exact declared names and namespaces are compared.

The previous checkpoint source audit retains merged Haskell source hashes
and local Fourmolu plus 16 focused SynthesisSpec cases with zero failures.
No Haskell source, Cabal file, full-suite or benchmark result changes here.
See ../20261112-marker-model-compatibility/source-audit.md and its prior link.
Historical negative packets keep their old source hashes and expected bad
outputs. Their checkers must reject the repaired current checkout.

## Haskell findings for the external owner

No new Haskell repair or runtime defect is established by this checkpoint.
PR210/211 already repair constructor namespaces, non-two Fun discovery and
inconsistent duplicate-query types. The exact universe law explains the
limited generated rigid-variable domain; it does not justify restricting
all rigid query/goal types. Curried marker names remain reserved domain names.
Liquid synthesis duplicate-name reader policies remain under external review.
Liquid Haskell contracts can target these same pure definitions and per-use
admission boundaries. External proof results do not enter Lean automatically
or certify the compiler/runtime. Preserve all old findings and counterexamples.

## Next obligations and retained runtime records

The current raw-input root certificate and generic application closure are
specified below. Membership alone does not transfer old hardwired source
origins or produce native cache/roles/type-field closure. Preserve the exact
original token permutation and current last-query types. Startup must derive
source-wide closure from the current factory and retain the SAME endpoint,
assignment, full graph/global/model/work receipt and computed conditional Room.

The shared eager child extension must interleave head alternatives with their
complete tail continuations. Core is branch-local. Native Caller and full
Memos are shared. Ordinary eager children use SelectedEdge, not outer
CapturedEdge finalization. Reuse the actual shared path and preserve the old
shallow adapter. Source lazy demand/implicit native sharing remain separate.

Continue all earlier hooks/alternatives, original-input work/depth, reduction,
refold/weights, ordered source multiplicity, both inverse contracts, full
guards, signed/Word/Int/errors, refinement and training. Annotation size is
not Program component count. Default synthesis does not call boundDepth.

Runtime: /tmp/mcfta-current-admission-20261112-1424/. Frozen failed drafts and
strict logs remain in this runtime and the preceding R241 runtime. Current
TypeAdmission progressed beadf711 -> 0b9c0f0e -> e8eaaff3; SharedBranching
progressed fccebd8c -> bd52ff31. Only proof scripts changed after public
headers were frozen. Every public header remained equal. R241 root-progress
points to R242. At 14:35 CET, primary usage was 19% and free space was
184.3 GiB. The last readable /tmp total was about 35 GiB, excluding six
private directories. Check usage by 14:51. Above 80%, save handoff, pause the
goal and notify Matti. No publication is a reason to pause the active goal.

## Frozen current root audit

# Current root admission and startup seam

2026-11-12 14:34 CET. Bounded read-only R242 audit. No compiler, repository, Git, Haskell, old-source, or ADR changes. Current source means merged main e538 after PR210/211. The checked CurrentContext, CurrentGroupAdmission, Pr210Substitution, and CurrentTypeAdmission laws are the base.

The smallest positive closure does not need a second whole TermsTyping/RelevantTyping stack. Keep their historical definitions. Add ONE current raw-input derivation certificate, prove direct terms/relevant membership by its finite induction, and reuse two context-indexed application closure steps. Base cases are the existing checked current leaf packets. Native startup then requires a separate source-wide closure bridge; positive membership alone cannot instantiate the old original-source wrappers.

## Raw input domain, without a semantic admission supplier

Use original `Typed`, `Equivalent`, Program, Library, Query, and original query tokens. The new certificate below records only original binding choices, raw per-use rho, role, demanded raw type admission, and marked token occurrences. It contains NO source expression, row membership, source typing proof, successful compiler/worker result, semantic model, or future whole Admits field. It combines the three old LeafEligible/ProgramEligible/UsesEligible levels to avoid copying all their judgments.

```lean
-- C := SourceSynthesisCurrentContext.constructorCatalog lib query
-- RawAdmitted is the CHECKED current raw type predicate, not a new placeholder.
inductive Eligible (lib : Library) (query : Query) :
    Bool → Program → Ty → List (String × Ty) → Prop where
  | group (asArgument : Bool) (entry : String × Ty × List String)
      (binding : entry ∈ lib.libraryGroups) (rho : String → Ty)
      (images : ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2.1) →
        RawAdmitted (constructorCatalog lib query) (rho raw)) :
      Eligible lib query asArgument (.var entry.1) (substTy rho entry.2.1) []
  | argumentOnly (entry : String × Ty) (binding : entry ∈ lib.libraryArgumentOnly)
      (rho : String → Ty)
      (images : ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2) →
        RawAdmitted (constructorCatalog lib query) (rho raw)) :
      Eligible lib query true (.var entry.1) (substTy rho entry.2) []
  | queryArgument (asArgument : Bool) (name : String) (typ : Ty)
      (found : queryLookup query.queryArguments name = some typ) :
      Eligible lib query asArgument (.var name) typ []
  | queryToken (asArgument : Bool) (token : String × Ty) (typ : Ty)
      (found : queryLookup query.queryArguments token.1 = some typ) :
      Eligible lib query asArgument (.var token.1) typ [token]
  | application {asArgument : Bool} {function argument : Program} {domain codomain : Ty}
      {left right : List (String × Ty)}
      (first : Eligible lib query false function (.tFun domain codomain) left)
      (second : Eligible lib query true argument domain right)
      (result : RawAdmitted (constructorCatalog lib query) codomain) :
      Eligible lib query asArgument (.app function argument) codomain (left ++ right)
  | conversion {asArgument : Bool} {program : Program} {first second : Ty}
      {tokens : List (String × Ty)}
      (admitted : Eligible lib query asArgument program first tokens)
      (same : Equivalent first second) :
      Eligible lib query asArgument program second tokens
```

`CurrentTypeAdmission.RawAdmitted:30` tests exactly the four raw rigid variables, current escaped constructor signatures, and Fun/2 alias. `typeIn_iff_admitted:174` converts ONLY the demanded images/results into the existing TypeIn witnesses. Do not require all query/goal types or domains to enter the universe. `candidateRigid_eq_iff:171` handles conversion. Group and argument-only cases call their checked current membership law once; marked and unmarked query cases share CurrentContext.query_argument_member. Alias safety is already derived. No original AliasSafe, query uniqueness, or name freshness is an extra input.

## Two generic closure headers

The first substantive generic helper can be written with the existing `Context`, catalog, and fixed term witnesses. `Eval e t` below abbreviates only `evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal e) t`; `M := .node (literal "(->)") []`. These are notation in this note, not proposed carriers.

```lean
theorem terms_application_member_at [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ctx : Context) (catalog : List (String × Nat))
    (types : ctx.types = allTypes top catalog) (unpruned : ctx.avoid = [])
    (asArgument : Bool) (left right : Nat) (leftPos : 0 < left) (rightPos : 0 < right)
    (domain codomain functionTerm argumentTerm : Term Symbol)
    (function : ∃ expression ∈ termsRows ctx false left, Eval expression functionTerm)
    (argument : ∃ expression ∈ termsRows ctx true right, Eval expression argumentTerm)
    (functionType : functionTerm.atPath [0] =
      some (.node (literal "->") [M, domain, codomain]))
    (argumentType : argumentTerm.atPath [0] = some domain)
    (result : TypeIn catalog codomain) :
    ∃ expression ∈ termsRows ctx asArgument (left + right),
      Eval expression (.node (literal "app") [codomain, M, functionTerm, argumentTerm])
```

For sum two, positivity forces left=right=1. Extract the actual function row from its size-one evaluation and include it in fallbackFunctionRows ctx. Because avoid=[], that pool contains all component/query function rows and excludes argument-only rows, as required. Use the actual argument expression in termsRows ctx true 1. For larger sums choose positiveSplits index left. Then use existing AnnotatedProgramWitnesses.application_member:101. This is the semantic counterpart of OrdinaryProgramCompleteness.unpruned_function_leaf:51 / eligible_program_terms:67; it uses the same exact terms, not an independently generated witness. The row-extraction helper is a small existing-evaluation observer. No new traversal or typing semantics is required.

For relevant rows, the exact helper replaces the child terms predicates above by observations at the ACTUAL winner's take/drop keys:

```lean
theorem relevant_application_member_at [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ctx : Context) (catalog : List (String × Nat)) (types : ctx.types = allTypes top catalog)
    (asArgument : Bool) (size left offset : Nat) (names : List String)
    (winner : List (String × Row)) (resolved : resolveArguments ctx names = some winner)
    (nonempty : winner ≠ []) (enough : winner.length ≤ size)
    (positive : 0 < left) (smaller : left < size) (offsetBound : offset ≤ winner.length)
    (domain codomain functionTerm argumentTerm : Term Symbol)
    (function : ∀ rows,
      relevantRows ctx false left ((winner.take offset).map Prod.fst) = .ok rows →
        Eval (.union rows) functionTerm)
    (argument : ∀ rows,
      relevantRows ctx true (size-left) ((winner.drop offset).map Prod.fst) = .ok rows →
        Eval (.union rows) argumentTerm)
    (functionType : functionTerm.atPath [0] =
      some (.node (literal "->") [M, domain, codomain]))
    (argumentType : argumentTerm.atPath [0] = some domain) (result : TypeIn catalog codomain) :
    ∀ rows, relevantRows ctx asArgument size names = .ok rows →
      Eval (.union rows) (.node (literal "app") [codomain, M, functionTerm, argumentTerm])
```

This is an INTERNAL finite-induction step. Its child observations come from induction hypotheses; they are not public future-success suppliers. Its proof follows SourceRelevantTyping.relevantRows_member:61's actual successful mapM trace. Select the actual split/offset with mapM_success_all₂ and all₂_child; keep all alternatives and their source order. Child key resolution comes from SelectionClosure.resolveSelection_take_drop; all-mapM success comes from FirstOrderTotality.relevantRows_total_of_resolution:19. Do not assume prior siblings/unused source constructor calls succeed without that existing totality proof.

The current certificate induction yields terms membership (tokens may be forgotten) and relevant membership whenever its current key resolves. If tokens=[], use the terms result and resolveSelection_empty. Marked singleton uses a current singleton resolver derived by the old RelevantSingletonLookup:174-201 map/last-lookup proof at current encoded rows. An application with nonempty tokens uses the actual resolved winner and offset=leftTokens.length; names and length follow resolveSelection_spec, and exact take/drop names follow the same old proof at OrdinaryRelevantCompleteness:136-184. This is the unavoidable new closure. Reusing old whole TermsTyping/RelevantTyping or pretending the old eligible_program_terms/uses_root_member now refer to currentContext is invalid.

## Current source root and exact positive target

Define a small versioned wrapper, reusing all existing row algorithms:

```lean
def firstOrderRaw (lib : Library) (query : Query) (signed : Int) : Except MissingKey Expression := do
  let ctx := SourceSynthesisCurrentContext.context lib query
  if signed < 0 then .error (.relevant true signed (ctx.argumentEdges.map Prod.fst))
  else do
    let chunks ← (SourceSynthesisSelections.permutations ctx.argumentEdges).mapM fun selected =>
      relevantRows ctx true signed.toNat (selected.map Prod.fst)
    pure (ofType (.union chunks.flatten) (SourceSynthesisCurrentContext.typeNode query.queryGoal))
```

Prove nonnegative totality using generic relevantRows_total_of_resolution/root_lookup_exists/pure_mapM_total, not historical firstOrderRaw_total. Negative names equal original names by context_argument_names. Then the exact current positive root header is:

```lean
theorem uses_root_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments) :
    Typed lib query program query.queryGoal ∧
      ∃ expression body,
        firstOrderRaw lib query (Int.ofNat program.components) = .ok expression ∧
        Eval expression (.node (literal "filter") [candidateRigid query.queryGoal, body]) ∧
        (Term.node (literal "filter") [candidateRigid query.queryGoal, body]).atPath [0] =
          some (candidateRigid query.queryGoal) ∧
        Projection literal Prod.fst
          (.node (literal "filter") [candidateRigid query.queryGoal, body]) program ∧
        toProgram literal Prod.fst
          (.node (literal "filter") [candidateRigid query.queryGoal, body]) = program ∧
        (toProgram literal Prod.fst
          (.node (literal "filter") [candidateRigid query.queryGoal, body])).components = program.components
```

Map covered tokens through ONE FIXED original query lookup: `tokenRow query token := (token.1, .mk token.1 top [CurrentContext.typeNode ((queryLookup query.queryArguments token.1).getD token.2)])`. Then covered.map supplies an actual permutation of current argumentEdges. Never normalize each permutation using that permutation's own last lookup. Marked token payloads remain original tokens; every marked leaf's actual type comes from original last lookup. Query names and multiplicities remain exact, including duplicates. Original Typed still records explicit library/query binding origins. The current positive proof needs no blanket library/query disjointness, Program-symbol freshness, or new shadowing priority.

## Native startup and the full checked Room packet

No module named OrdinaryProgramWork was found in the current repository or the bounded runtime search. The concrete existing endpoints are `SourceSynthesisOrdinaryInitialModelWork.uses_native_initial:47` and `SourceSynthesisOrdinaryCheckedInitialModelWork.uses_checked_native_initial:80`. Both still call OLD uses_root_member and OLD OriginalCallerInitialization.accepted / OriginalCheckedSharedProgramCount.accepted. They cannot consume the new root equation as-is.

The raw startup bridge is smaller than a new native compiler. Derive the current expression's cached guards, projectable equality payloads, ProgramSyntax, and ProgramSize from its ACTUAL full source run. Reuse existing context-parametric private inductions rather than recreate them: ProgramRoles.ContextRoles:101 with termsRows_checked:136/relevantRows_checked:211; ProgramSourceSize.ContextSizes:66 with termsRows_checked:101/relevantRows_checked:176; OriginalGuardsCached.ContextGood:122 with terms_good:155/relevant_good:224. Those predicates are already generic in ctx. Exposing their exact generic wrappers with bodies unchanged is a possible later focused edit; this audit edits nothing. Current factory fields discharge them directly using encoded schemes, arbitrary catalog allTypes, and actual query bindings. Guard caching and projectability hold for every generated eqGuard, so no new external guard supplier is needed.

Use ONE InternedFreshOrdinaryClosedCompletion.closed_complete:50 on ordinarySymbols expression; it already returns the actual build for arbitrary input syntax. Observe that SAME build with closed_verified and ProgramBuildRolesGeneric.build_mapped_program. Prepare guards once with SourceEqualityOriginalAllocationPreparation.prepare_complete. Apply generic PartialInitialization.constructed:106 with its returned history and actual guard list. Use AnnotationConstruction.build for the SAME initial physical heap's projectable guards and closed_language for the SAME accepted whole term. Then call InitialModelWork.initial_packet_models_origins_work:52 ONCE. Retain its full Packet/carriers/canonical/index fields, SAME assignment sigma with sigma 0=whole, original empty-pending refutation and origins, P=N=NumberedTerms.size whole, and W=(N+1)*N+the actual boundary flag. Reproduce the entire old raw startup conclusion, replacing only the old source wrapper/goal encoder and derivation certificate. Do not expose future build/member/model premises.

Checked startup requires MORE than that raw packet. Old InitialTypeFields.Program/ProgramRow:17-39 and ContextFields:42 hardwire old typesOf, old schemes and query rows. Their dependent hereditary/type-origin proofs cannot merely be relabeled. Current encoded schemes also change equalityClasses for formerly colliding constants; old Origin lib is not automatically the current Type-origin predicate. The least source-faithful route is an internally derived encodedLibrary (same representative/member/avoid/encoding fields, only group and argument-only schemes mapped by encodeTy) and Origin(encodedLibrary lib). Rigid annotations already have generic rigid_allowed:93. Universe/generalized allowed:102/79 need a catalog-parametric adapter: their proofs only use Top in allTypes plus the selected encoded scheme's derived guard. Do not assume typesOf encodedLibrary equals current universe; its historical discovery still drops non-Fun/2 entries. This current source-field/hereditary closure is a genuine remaining bridge before transporting the full checked worker packet.

After that bridge, keep the existing full conditional checked conclusion, not only NodeLaw or one success: actual request=emptyValue(cache),value; output=envelope budget (count inheritedPayload value) (mass value) (seed heap); first=Phase.node output.1 request currentCaller; need=phaseNeed budget first (seed heap); and EXACT `Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2)`. Preserve that current-input condition, every sufficient-fuel exact endpoint/range law, actual graph/Checks/Reads/Post/Frame/Fits/physical annotation Heap, final Memos, type/memo fields, NodeLaw and original/requested Program counts. Obtain the SAME whole term at result by NodeLaw reverse under actual empty inherited value, then one startup/work producer at Post.context/final Memos. Keep all fields of OrdinaryCheckedInitialModelWork:80-169 and the one-assignment derivation at :171-228. Do not assert Room has been discharged, join separate endpoint/model witnesses, or replace the checked worker with an unchecked build.

These are current source-admission/startup cuts. Neither local P/W nor Program.components bounds full annotation size, all earlier branches, global enumeration depth, runtime work, or default eager-order correspondence. Historical definitions and counterexamples remain valid on their explicit source versions.

## Frozen native branching audit

# One shared path for eager child branching

Frozen: 2026-11-12 14:09 CET. READ-ONLY audit. The interface and wiring below are UNPROVED PLAN. No new defect, source edit or compiler result is asserted.

## Actual source contract

Haskell Data/CFTA/Enumeration.hs:328-335 defines EnumerateM directly as CPS. It is not a transformer stack containing native state. Its branch-local state and order are the order of StateT EnumerationState []; the source says this explicitly at319-327. Bind at347-350 invokes each successful value's continuation immediately. Alternative at352-356 invokes both alternatives with the SAME input EnumerationState. branches at372-375 preserves list order; allBranches at377-380 returns results lazily.

All EnumerationState fields at228-266 belong to the branch: UVar supply, union-find, values, expandable set, waiting counts, residual obligations, both ancestry stores, edgesOf and constrained-recursion flag. The last two are captured source configuration and normally remain fixed. At a choice, copy this entire state, not only values or the representative forest. Callback metadata ost is a separate ordinary argument to enumerateUntil'; a sibling does not inherit another alternative's updated metadata. The corresponding formal hook closes over captured metadata.

Default enumerateFully' at920-927 passes eager enumerateNode to enumerateUntil'. enumerateNode:720-755 has these cases:

- EmptyNode rejects with mzero before partitioning constraints.
- With no terminal constraint: Mu/InternedUnion allocate one opaque hole; ordinary Node chooses branches (edgesOf n), then enumerateEdge; Rec raises an error.
- With terminal constraints: representative reads/unions/assimilation and mergeNodeIntoUVarVal precede one returned hole.

The actual edge implementation at763-782 first checks inherited child indices, allocates its own equality variables, then zipWithM traverses children left to right using prepareChild. enumerateEdge:757-761 supplies eager enumerateNode. Each parent edge therefore enumerates the ordered Cartesian product of its children's alternatives, depth first. Residual recording occurs for EACH completed child tuple, after its children succeed.

The singleton formal child component is a distinct source component. SourcePruningEnumerationShallowChild.prepareChild:14-31 allocates/stores an ordinary child as a pending hole. This matches Haskell prepareShallowChild:803-809, used by enumerateShallowHere:789-795. It does not implement the ordinary eager arm of default enumerateNode. This is a correspondence boundary, not a Haskell defect. Merely accepting a longer raw list in the existing singleton pattern cannot close it.

## Shared native state and order

Native interning/query caches are not EnumerationState fields. For example Enumeration.hs:537-546 and Interned/Operations.hs:466-483 use NOINLINE unsafePerformIO memo caches; failed pure branches do not roll those global tables back. The current formal shared endpoint is the ENTIRE Caller width plus SourceEndpointMemo.Memos, not only the native heap. Preserve both through every child and continuation; full-memo/resource receipts remain separate proof data at those same endpoints.

This is a bounded EAGER operational abstraction. Haskell allBranches is lazy, and native operations use implicit sharing. A literal correspondence of global allocation/demand order needs the existing source-effect/demand bridge; it does not follow from CPS list order alone. Do not claim that every unforced source alternative ran.

Correct order for a child with alternatives A,B is A, all later-child continuations of A, B, all later-child continuations of B. A design that collects all head-child rows, then maps the remaining children over them, changes native effect order. A list of rows plus one final native endpoint is insufficient to define bind faithfully.

At a child alternative, clone the cached Core captured immediately BEFORE that child choice. Continue later child indices at that alternative's returned Cached. At the next alternative of the SAME child, restore the captured Cached, but pass the native caller/queries returned by the PREVIOUS alternative's COMPLETE continuation. At the next parent edge, restore the parent's captured pre-edge Cached; retain native effects from the previous edge and its continuation. Branch-local UVar numbers can therefore be reused across alternatives; native allocations/memos persist.

## Existing formal operations to reuse

SourcePruningEnumerationSharedSelectedContinuations.lean contains the actual shared path:

- ChildDispatch.observe/run:46/64 retain terminal raw receipts and native endpoints. Nonterminal child preparation delegates to the shallow component. On that nonterminal prepared-cache arm, multiple raw results have no matching single cache: run accepts only [] or singleton cached preparation, otherwise candidate=None.
- ChildTraversal.Result/run:201/211 accept exactly one successful child row with its returned cache, then traverse the suffix at that cache and reached caller/queries. Other observations remain stopped receipts. This cannot represent the eager Cartesian product.
- SelectedEdge.run:455 prepares current own classes, invokes ChildTraversal, then records the residual through finish:427 for the completed tuple.
- CapturedEdge.run:523 adds outer selected-UVar finalization to that edge receipt.
- NativeContinuations.HookResult:576 already supplies ordered outputs with a complete shared endpoint or an explicit stopped prefix. advance:599 recognizes ordinary rejection and a stopped empty child observation with a cache as normal edge rejection. endpoint:606 preserves actual native endpoints.
- NativeContinuations.run:619 is the RIGHT ordered-shared pattern: a completed edge invokes its hook BEFORE the next edge; the hook's returned caller/queries feed the suffix, while the captured Cached is fixed. It appends outputs and stops on an actual stopped hook. Its run_append law is SourcePruningEnumerationSharedScanModels.lean:131.

No generic shared native branching bind was found in these operational dependencies. NativeContinuations.run is specialized to CapturedEdge.run and the singleton child path. Reuse its algorithm and HookResult, but do not claim its current signature can already visit multiple eager child results. EnumerationCPS.lean:47-51 and EnumerationCPSChecked.lean:52-60 provide branch-local CPS choice/bind; Checked.bindRows:126 is State/Except/List flatMap. They have no separately threaded native endpoint. Adding Caller/Queries to their cloned State would roll globals back incorrectly.

## Smallest operational interface

Expose a hook-based child operation on the SAME shared SelectedEdge/ChildTraversal path. A representative current type is:

```lean
noncomputable def ChildDispatch.visit
    (hook : Fragment → Caller width → Queries → Cached →
      NativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k recursiveFuel : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    NativeContinuations.HookResult Output (ChildStop Reason width) width
```

Here edgesOf is the SAME captured source ordering configuration, as in existing NativeOrdinaryContinuations.run:712, not a future list/completion supplier. ChildStop should retain the actual ChildDispatch Observation/optional cache, recursive-fuel exhaustion with its current input, or the original hook stop. It must not erase native failures into an empty success. The exact error embedding is a small implementation choice; keep actual observed endpoints and leave endpoint=None untouched when a hook supplies none.

This signature is an OPERATION, not a theorem assuming a future complete child, supported rows, or a model. The recursive child calls and the hook are executed by it. HookResult is already the actual shared continuation type; do not introduce a parallel result/model hierarchy.

The necessary wiring is:

1. Factor the existing ordered-shared scan pattern so one actual row visitor can execute its hook before the suffix. Complete outputs append; stopped prefixes stop. Use it for both root/captured and child/uncaptured edge alternatives. A generic algebra lemma by itself does not close the source gap.
2. ChildTraversal.visit binds a head child to the REST of the actual children immediately, using a hook that accumulates the ordered fragment prefix. It does not collect head rows before traversing tails.
3. SelectedEdge's one own-class prefix runs before its child visit. Each completed tuple forms its actual symbol fragment, records that edge's residual, then invokes the supplied hook at the tuple's cache/native endpoint.
4. Ordinary eager CHILD nodes scan edges through SelectedEdge, without CapturedEdge.finalize. Source eager children do not allocate a selected-root UVar of their own. CapturedEdge remains the OUTER selected-UVar adapter: finalize each completed fragment before invoking the existing callback/restart hook. Calling CapturedEdge directly for an eager child would add an unrequested UVar write.
5. Reuse current terminal and opaque ChildDispatch operations for their exact singleton/rejected/stopped observations. Ordinary nonterminal input chooses the eager route. Refactor or extend the SAME public shared path with an explicit child policy; do not add a disconnected shadow worker and claim old driver theorems use it automatically. Preserve existing shallow specialization and receipt observers.

An equivalent small internal Code A interface is hook → Caller → Queries → Cached → HookResult. pure invokes the hook; rejection returns complete [] at the reached native endpoint; bind supplies the next actual operation as the hook; choice runs the left operation and its hook, then the right operation at the original Cached and left continuation's final globals. This is the existing shared scan discipline. A full generic CPS datatype is not needed for the first source cut.

## Empty, failure and stop cases

- Empty child list: invoke the list hook ONCE with [] and unchanged current cache/native endpoint. This is one successful tuple, not no alternatives.
- Empty ordinary edge list or EmptyNode: zero child results; no hook. Continue the surrounding alternative scan at the reached native endpoint.
- Inherited arity rejection: no own-class/child work; zero results for that edge. Continue its siblings.
- A child rejects after earlier child/native work: discard that branch's Core effects/results, keep its native endpoint, and try the previous choice's next alternative. Never run later child indices for that failed tuple.
- A hook completes with []: its branch is pruned normally. Its returned native endpoint still feeds the next alternative.
- Singleton opaque/terminal success: invoke the hook with the actual returned fragment/cache/caller/queries. No extra selected-UVar finalization inside a child.
- Several successes: invoke the hook for EVERY success, left to right, and append each continuation's outputs in order. Keep duplicated outputs; this layer does not deduplicate.
- Model fuel exhaustion, unsupported raw shape, missing candidate cache, native pending/failure/error, or a stopped hook: retain exact reason, completed output prefix and actual endpoint. Do not execute the suffix or classify the observation as mzero. recursiveFuel zero must be a stopped observation, not complete [].

Current ChildTraversal records empty child output as stopped, but NativeContinuations.advance recognizes that exact .ok(some[])/some-cache receipt and continues OUTER siblings. Do not misreport this as halting the entire current worker. The new eager bind must also resume earlier CHILD alternatives, which the singleton traversal cannot express.

Haskell guard/mzero/pattern-fail reject branches (Enumeration.hs:352-364). Raw Rec uses error at734-738. Lean Checked.failure preserves explicit diagnostic errors and recovers ordinary source CPS only on error-free executions (EnumerationCPSChecked.lean:5-10). Keep these distinct; no claim that arbitrary Lean errors denote Haskell empty branches is justified.

The first bounded cut should prove branch-copy/shared-endpoint/hook-order equations for this actual visit, including empty/failure/stopped prefixes. Adequate recursive/native/work fuel, range/resource admission, all earlier hooks, source-effect correspondence, and whole default enumeration remain separate. No Haskell fix is established by this audit. No main merge-status claim is made.
