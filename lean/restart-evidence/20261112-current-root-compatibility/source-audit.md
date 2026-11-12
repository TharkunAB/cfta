# Current root admission and native callback integration

Base: 8331f9c10f444e1cd9715e6837190049fb2dc11b. Integrated main:
e53852064d3ef5a2eafec47d754c27504b11de5f, with PR210/211 merged.
The full formalization goal remains ACTIVE. No production Haskell changes.

## Checked modules

- SourceSynthesisContextApplications: 207 lines; 2 laws; SHA256 fa7db392dab222fcaa1b6d402612513941387580e25bfbc5f7c367f9dd15498f.
  - MicroCFTA.SourceSynthesisContextApplications.terms_application_member_at
  - MicroCFTA.SourceSynthesisContextApplications.relevant_application_member_at
- SourceSynthesisCurrentProgramAdmission: 138 lines; 1 laws; SHA256 7c43d9ee681836f2287c510e79e9bef72448850988526e29cdd8868e737a077c.
  - MicroCFTA.SourceSynthesisCurrentProgramAdmission.eligible_program_member
- SourceSynthesisCurrentRelevantAdmission: 352 lines; 2 laws; SHA256 187f0e174ea2a89c0ccd2073b92be79d557fbd1bdb609e20ebdcfcaf824e6465.
  - MicroCFTA.SourceSynthesisCurrentRelevantAdmission.eligible_relevant_member
  - MicroCFTA.SourceSynthesisCurrentRelevantAdmission.uses_root_member
- SourceSynthesisCurrentConstruction: 65 lines; 3 laws; SHA256 87b658df7fb9135396b705c98c70ebf9a36c18b683650547cd7b0d2a0eeac24b.
  - MicroCFTA.SourceSynthesisCurrentConstruction.firstOrderRaw_negative
  - MicroCFTA.SourceSynthesisCurrentConstruction.firstOrderRaw_total
  - MicroCFTA.SourceSynthesisCurrentConstruction.firstOrderRaw_ok_iff_nonnegative
- SourceSynthesisCurrentTypeReification: 181 lines; 2 laws; SHA256 9bb08bd7a802c493763cafb83a984febd3ef82bc13b4a2296123df2e34d302c3.
  - MicroCFTA.SourceSynthesisCurrentTypeReification.typeIn_reify
  - MicroCFTA.SourceSynthesisCurrentTypeReification.universe_reify
- SourcePruningEnumerationSharedChildVisitors: 193 lines; 4 laws; SHA256 0c785c6944b8c9e8c9486e3653e1fa1f4b2ae0c8c4f9dd5aa19a61b07e035edd.
  - MicroCFTA.SourcePruningEnumerationSharedChildVisitors.visitChildren_shallow
  - MicroCFTA.SourcePruningEnumerationSharedChildVisitors.visitSelected_shallow
  - MicroCFTA.SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_shallow
  - MicroCFTA.SourcePruningEnumerationSharedChildVisitors.run_eq_scan_shallow

## Strongest current source statement

With lib.libraryAvoid=[], a program satisfying the six-case current raw
Eligible certificate and covering the ORIGINAL query token list has a
constructive witness in the actual current FirstOrder root at its Program
component count. The theorem derives original ordinary Typed and actual
firstOrderRaw=.ok expression. The SAME filtered term is accepted, has exact
candidateRigid goal annotation, projects/decodes to that Program and retains
its component count. No future whole-source membership, model, worker or
Room witness is a premise.

Eligible records original group/argument-only binding origins, raw rho,
argument role, marked/unmarked query leaves, demanded RawAdmitted images,
application-result admission and conversion. It is the stated input domain,
not all ordinary Typed derivations. Only actual demanded images/results need
universe admission. Rigid query and goal types do not blanket-require it.
The six constructors reuse the existing Ty, Program, Library and Query.
There is no second whole TermsTyping/RelevantTyping hierarchy.

The terms proof retains exact source rows and child bodies. The relevant
proof derives actual source success from current key resolution and uses
one body for every actual child return. Its internal resolver premise is
not inferred from arbitrary Eligible tokens: a certificate can mark x twice
when the input has one x. The outer root instead derives the required
resolution from tokens.Perm ORIGINAL queryArguments. It applies the fixed
ORIGINAL query normalization before mapping that permutation. Duplicate name
occurrences remain separate required tokens; each current row has the last
original binding type. No freshness or query uniqueness premise is added.

## Other exact contracts

CurrentTypeReification proves that every TypeIn term of the actual current
catalog, and every semantic current-universe member under topHeld, is
candidateRigid of an admitted raw Ty with EXACT term equality. Constructor
name origins and exclusion of genuine Fun/2 signatures are source-derived.
It adds no decoder carrier, catalog/inverse supplier or whole soundness claim.

ContextApplications gives exact terms/relevant application membership at an
arbitrary existing Context with the stated universe and local conditions.
It observes actual split/offset mapM traces and uses the exact child terms.
Unused source alternatives are covered by existing source totality.

CurrentConstruction reuses the existing row algorithms at the repaired
factory. Its signed negative result retains the original names and signed
size. It succeeds exactly on nonnegative signed sizes. Success at size zero
is syntax construction and does not supply an inhabitant.

SharedChildVisitors executes child continuations inside visitChildren,
retains the actual own-class prefix and residual completion in visitSelected,
and adds only actual outer finalization in visitCapturedWith. The shallow
adapter is equality of the ENTIRE old shared result, and run_eq_scan_shallow
rewrites the actual old NativeContinuations worker into this callback path.
Every native endpoint, processed receipt, stopped prefix and absent endpoint
remains. All operational definitions stayed byte-identical during proof
repairs. This module adds no eager recursive policy, datatype, configuration
or whole-worker completion claim. The source lazy-demand/native-sharing
correspondence remains open.

## Compatibility and reproducibility

All six strict source checks pass for fourteen public laws. Full Audit passes:
5807 live modules, seven affected modules, 4804 Audit imports, 93766 axiom
reports. All 260317 old Audit bytes remain after six new imports. All seven
portable source/compatibility checks pass from /tmp. Exact public names and
namespaces, source hashes and standard axioms are checked. The effective
limits are memory.max=memory.high=4294967296, memory.swap.max=0, one Lean
thread. Project Nix and the repository Lake cache are used. No binary archive
is copied. The intermediate five-module full/six-portable receipts remain
in the runtime; the sixth checked module caused the final frontier rerun.

Prior Haskell validation and source hashes remain in the linked audits:
../20261112-current-admission-compatibility/source-audit.md and its prior link.
Merged main passed Fourmolu and 16 focused SynthesisSpec cases, zero failures.
No Haskell, Cabal file, full-suite or benchmark result changes here.

## Haskell findings for the external owner

No new production Haskell repair or runtime defect is established. PR210/211
already repair constructor namespaces, non-two Fun discovery and inconsistent
duplicate-query types. Current pure source contracts now include exact raw
admission, reification and constructive whole-root membership on the stated
domain. These are useful matching Liquid Haskell contract targets. External
proof results do not enter Lean automatically or certify Haskell execution.
Historical negative packets keep their old hashes and expected bad outputs;
their checkers must reject repaired current source. Curried markers and raw
generated-variable restrictions stay separate. Liquid synthesis duplicate-
name reader policies remain under external review.

The native source audit also found a proof-transport counterexample: empty
library, no arguments, goal Fun[a,b,c]. The current catalog is [(Fun,3)];
historical discovery always excludes that signature. Whole old/current
context equality is false, including after naive input encoding. This is a
source audit finding, not a newly kernel-checked counterexample or Haskell
bug. Once-encoded library guard origins remain reusable independently.

## Remaining work and runtime

Current whole-root POSITIVE admission is now closed on the stated certificate.
Do not leave the earlier audit's planning statement about that gap as current.
Full source soundness in the reverse direction remains separate. Current
source-wide roles/counts/complete guards/PlainMu closure and hereditary native
Type fields at actual prefixes must still be produced for the same build.
Generic allocation, initialization, rank completion and graph/startup
consumers already exist. Retain the full actual endpoint, graph/global/full-
memo/model/work packet and computed conditional Room. Do not infer Room,
model existence or full work bounds from Program count or syntax totality.

The actual eager child policy must use the checked callback path, run source
classification once, and interleave each head choice with all tail work.
Core is branch-local; native Caller/full Memos are shared. Ordinary eager
children use SelectedEdge without outer CapturedEdge finalization. Retain
truthful stops and actual receipts. Per-invocation child-height descent does
not establish outer restart termination or source lazy-demand equivalence.

Continue all earlier hooks/alternatives; original-input work/depth; reduction,
refold/weights; source order/multiplicity; both inverse contracts; full guards,
signed/Word/Int/errors; refinement/training. Annotation size is not Program
count. Default synthesis does not call boundDepth. The full goal is incomplete.

Runtime: /tmp/mcfta-current-root-20261112-1448/. R242 root-progress points here.
Failed drafts/logs are retained there and in preceding runtimes, including
reification326b->5bcc->9bb, callbacks ef015->0afc->0c785, relevant0106->187f.
At 15:07 CET, primary usage was 20%, filesystem free space 184.0 GiB, and
runtime records occupied about 193 kB. Check usage by 15:22. Above 80%, save
handoff, pause the goal and notify Matti. Do not pause after publication.
Next runtime-only drafts: CurrentProgramStructure (Gamma) and CurrentSourceGuards
(Beta), plus next-eager-child-policy.md (Alpha audit). They are UNVERIFIED.

## Frozen native source-closure audit

The following read-only audit predates the checked current root theorem above.

# Current source closure for the existing native endpoint

Audit time: 2026-11-12 15:08 CET. This is a read-only source audit.
No theorem in this note is a new checked result. The current reification module
passed its separate strict check. Historical source definitions remain separate.
All source paths below are relative to `lean/MicroCFTA/`.

## Result

The native engine can be reused. The missing part is a producer of structural
and Type-field facts for the current factory. The old source wrappers do not
provide these facts for every current input. In particular, transporting the
whole current context to an old context is false on genuine `Fun/3`.

Two source proof cuts remain: context-parametric table closure, then hereditary
Type-field construction at actual prefixes of the same whole native build.
Allocation, initialization, native rank completion, graph checks, and enumeration
startup already have generic consumers. Do not replace these consumers.

## The failed context transport

Take an empty library, no query arguments, and goal
`TCons "Fun" [TVar "a", TVar "b", TVar "c"]`.
`encodeTy` preserves this type. Current constructor discovery includes
`("Fun", 3)`; historical discovery excludes every constructor named `Fun`.
The catalog results are therefore `[ ("Fun", 3) ]` and `[]`.
See `SourceSynthesisCurrentContext.lean:37`, `:45`, `:138`, and historical
`SourceSynthesisTypeSyntax.lean` (`constructorsOf`, `constructorCatalog`, `typesOf`).

Consequently, the two `context.types` fields contain different `allTypes` syntax.
Their languages also differ: the current universe admits the `Fun` node with
three variable children; the historical empty catalog does not. This comparison
is a direct source expansion, not a new kernel theorem or runtime defect claim.
No historical input can put a `Fun/3` signature into the historical catalog.
Adding dummy historical inputs cannot repair this transport.

A proof-only encoded library is still useful. Map each group scheme and each
argument-only scheme through `encodeTy` once. Preserve names, member lists,
avoid lists, and the encoding field. A proof-only encoded query can map
`queryBindings query` through `encodeTy` and encode the goal. Preserve all name
occurrences and their order. These maps do not currently exist as Lean definitions.
They can reuse guard-origin bookkeeping; they cannot establish context equality.
Do not escape these already encoded schemes a second time.

## Source facts that derive from the current factory

Let `libE` denote that proof-only encoded library and let `ctx` be the actual
`SourceSynthesisCurrentContext.context lib query`.

* Roles: each component and argument-only row is an ordinary annotated row.
  Each query row has one annotation child. Application and filter layouts are
  unchanged. `SourceSynthesisProgramRoles.component_roles` (`:51`),
  `application_roles` (`:59`), and `filter_roles` (`:70`) accept arbitrary fields.
  Its `ContextRoles` (`:101`) and generic table inductions (`:136`, `:211`) are
  private. The public root theorem (`:280`) still uses the historical factory.
* Counts: every startup row has component count one. Application adds child
  counts; filter preserves the count. `SourceSynthesisProgramSourceSize.lean:24`
  and `:31` define the existing predicates. `ContextSizes` (`:66`) and the two
  generic table inductions (`:101`, `:176`) are private. None of this bounds
  native annotation size or proves `Room`.
* Complete literal guards: current source guards belong to
  `SourceSynthesisOriginalGuardAlphabet.alphabet libE` (`:31`). This list contains
  Top, the application guard, the filter guard, and equality guards for the
  actual encoded schemes. `generalize_guards` in
  `SourceSynthesisGeneralizeSyntax.lean:326` supplies the component step;
  `allTypes_guards` and `typeNode_guards` supply the Top-only steps.
  The old `program_guards` (`OriginalGuardAlphabet:105`) and `mapped_guards`
  (`:198`) still require historical source certificates.
* Cache and projectability: derive cache correctness from that literal guard
  inclusion, `SourceEqualityGuardReadback.normalize_cached`, and `top_cached`.
  The alternative cached-context induction already exists privately as
  `SourceSynthesisOriginalGuardsCached.ContextGood` (`:122`), `terms_good` (`:155`),
  and `relevant_good` (`:224`). Projectability follows directly from
  `SourceSynthesisOriginalGuardsProjectable.alphabet_projectable` (`:65`) on
  `libE`. Its `generalized_projectable` is valid for any scheme.
* Mu bodies: `SourceSynthesisRecursiveOrigins.allTypes_plainMu` (`:118`),
  `typeNode_plainMu` (`:122`), `component_plainMu` (`:194`),
  `application_plainMu` (`:203`), and `ofType_plainMu` (`:216`) are generic.
  The `CleanContext` and table closure proofs in that file are private.
  The current context satisfies their field obligations without catalog
  separation, raw-type admission, or blanket goal-universe membership.

The current query rows use canonical payloads. Their name sequence and duplicate
count remain unchanged (`CurrentContext:128`, `:133`). Selection, splitting,
last-winner lookup, and unused successful table alternatives remain the actual
existing algorithms. These closure proofs need no new name-uniqueness premise.

## Minimal missing source closure API

The first useful public producer should have the following concrete shape.
This is a proposed header, not an implemented interface:

```lean
current_closed_source (lib : Library) (query : Query) (signed : Int)
    (nonnegative : 0 <= signed) :
  ∃ expression,
    CurrentConstruction.firstOrderRaw lib query signed = .ok expression ∧
    ProgramSyntax expression ∧ ProgramSize signed.toNat expression ∧
    PlainMu top expression ∧
    (∀ guard ∈ guards (ordinarySymbols expression), guard ∈ alphabet libE)
```

Here the short names denote the existing predicates above. `libE` is the
explicit once-encoded library, not a supplied guard universe. Obtain the actual
expression from `CurrentConstruction.firstOrderRaw_total` (`:35`). Expose or
factor the existing private context-parametric inductions and instantiate them
with current fields. One table induction can prove the conjunction. Preserve
the old wrappers and definitions. No second source evaluator is needed.

Symbol mapping retains guards, but the guard-equality lemmas in
`OriginalGuardAlphabet:166` and `NativeTypeSites:153` are private. Expose this
small generic map fact, or derive the mapped inclusion in the same proof.
`NativeTypeSites.mapped_plainMu` (`:195`) is already public.
The resulting Program role proof can already feed generic
`SourceSynthesisProgramBuildRolesGeneric.build_mapped_program` (`:403`).
No historical root equation is needed by that native role consumer.

## Checked Type fields and hereditary Program fields

`SourceSynthesisInitialTypeFields.Program` (`:18`) and `ProgramRow` (`:25`)
hardcode historical `typesOf lib query`. `ContextFields.types` (`:42`) requires
that exact equality. It fails on the Fun/3 example even after encoding inputs.
This is the remaining source indexing issue, not a missing native type engine.

Factor their table closure to use the actual universe and the actual encoded
scheme origins. Type-only annotations use `Origin libE` from
`SourceSynthesisNativeTypeTrace.lean:35`. Do not use the full Program alphabet
as the Type-only origin predicate: application and filter owner guards have a
different role. The existing Type-field ingredients are:

1. Generalized fields use `generalize_guards`, literal encoded-scheme pool
   membership, and Top-only `allTypes` guards. Generalize the hardwired
   `OriginalTypeAnnotations.generalized_allowed` (`:79`) and `universe_allowed`
   (`:102`) to an arbitrary actual catalog/universe. `rigid_allowed` (`:93`)
   already accepts arbitrary types and can use `libE` and `encodeTy typ`.
2. Whole-build `PlainMu` gives actual stored Mu-body annotations through generic
   `SourceSynthesisNativeTypeSites.build_mu_bodies` (`:71`). Monotonicity and
   `origin_top libE` give `MuStored (Origin libE)` on that same heap. Obtain each
   earlier prefix store with `SourceSynthesisOriginalPrefixMuStore.muStored_of_grows`
   (`:21`). Do not assume a future store certificate.
3. For each actual Type-field subcall, use its real prefix, environment, Facts,
   availability, and growth. `SourceSynthesisOriginalProgramTypeFields.many_call`
   (`:37`) extracts real ordered child calls. Generic
   `SourceCurrentHereditaryConstruction.build` (`:205`) then derives
   `Annotated (Origin libE)` from the field's `Allowed` proof and that prefix
   store. Captured lexical references retain their existing annotation proof.
4. Reuse `SourceSynthesisHereditaryProgramFields.ValueFields` (`:24`),
   `EdgeFields` (`:32`), and its generic `makeEdge_fields` (`:115`),
   `makeNode_fields` (`:123`), and `makeUnion_fields` (`:159`). Generalize the
   source premise of `OriginalHereditaryProgramFields.at_prefix` (`:193`);
   its present public statement is historical-source only.

The next concrete native producer is therefore `current_build_fields`: actual
current `.ok` identity plus the same actual closed build imply
`ValueFields (Origin libE) literal value`. It must derive the Type-field and
prefix facts above internally. Its unconditional wrapper obtains `.ok` and
the build from the already closed producers. Do not accept `ValueFields`,
`Annotated`, `MuStored`, a model, or a completed worker as caller suppliers.
Do not build a second copy of a Type field and transfer its result to the first.

## Reuse the native initialization and full endpoint

Obtain ONE actual build using `InternedFreshOrdinaryClosedCompletion.closed_complete`
(`:50`). Obtain its Facts and growth through `InternedFreshOrdinaryFacts.closed_verified`
(`:143`). The current literal-cache proof feeds
`SourceEqualityOriginalAllocationPreparation.prepare_complete` (`:85`). Its
actual history feeds `SourceCurrentAllocatedPartialInitialization.constructed`
(`:106`) and `SourceCurrentConstructedOuterInitial.frame` (`:38`). These consumers
are source-independent.

From current `MuStored`, obtain native store readiness with
`SourceCurrentHereditaryNativeUniversalStore.initial`. Compose semantic cache
readiness, initial scope/idle facts, and the actual heap cost proof as in
`SourceSynthesisOriginalTypeSharedState.initial_ready` (`:34`). Then use generic
`SourceSynthesisNativeTypeSharedState.initial` (`:37`) with empty physical and
typed merge memos. No old/current context equality is needed.

Use generic `SourceCurrentSharedOuterRankAdequacy.initial_node_call` (`:177`)
to produce the actual stable run. Derive its initial support, union normality,
publication history, parent origins, closed-input store, and idle obligations
from the same initialized build, as in `OriginalSharedRankCompletion.accepted`
(`:46`). Retain its exact computed condition:

```text
Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2)
```

Use the same produced run with generic
`SourceSynthesisHereditarySharedOuterTraversal.nodeCall_fields` (`:592`).
Preserve the complete packet from
`OriginalCheckedHereditarySharedCompletion.accepted` (`:52`): sufficient-fuel
stable runs and literal ranges; the actual graph and Checks; endpoint reads
against globals; Post, Frame, Fits, full forecast guard carrier, Available,
NodeLaw, shared readiness, Mu-profile GuardHeap, History, closed result,
NodeFields, and ValueFields. Add component counts with the already generic
`SourceSynthesisOriginalProgramTermSize.build_accepted` (`:34`).

The Mu-profile `GuardHeap` is a body/probe profile equality for completed Mu
records (`SourceCurrentConstrainedCapGuardHeap.lean:25`). It is not a claim that
every physical guard belongs to `Origin libE`. Full physical projectability
comes separately from the complete literal alphabet and the generic annotation
heap construction.

Finally preserve the startup packet from
`SourceSynthesisOrdinaryCheckedInitialModelWork.uses_checked_native_initial`
(`:80`). The generic final consumer is
`SourcePruningEnumerationInitialModelWork.lean:52`, theorem
`SourcePruningEnumerationRecursive.initial_packet_models_origins_work`.
It needs Context, Available, closedness, and empty pending metadata. It produces
the same handle/lookup and initial slot, Packet and canonical/waiting facts,
candidate expansion, and graph/reference carriers. For every term accepted by
that same result, it also derives a satisfying assignment with origins, exact
pending size, and exact startup work
`(N + 1) * N + (if recursiveBoundary result then 0 else 1)` for
`N = NumberedTerms.size term`. The complete native startup packet and this
universal accepted-term observer need no future model or inhabitance supplier.

The ordinary-specific existential version additionally needs a constructive
current root witness for the same Program. Historical `UsesEligible` and
historical root membership cannot be silently relabeled as current. Current
group/argument/application membership laws provide constructive pieces, not a
closed current whole-root ordinary admission theorem. Keep this independent
bridge explicit. It does not block the universal native observer above. An
empty size-zero root language does not acquire an inhabitant from syntax
totality. Current source closure itself needs no ordinary typing, type-universe
admission, or inhabitance assumption.

This plan preserves the full resource and work objective. Program component
count, native term size, weighted size, and `Room` remain distinct. It does not
prove default enumeration completion, fixed-word capacity, unrestricted ordinary
completeness, or Curried correctness.
