# Current sufficient capacity, eager frontier and Type inversions

Base: bf723bd595dab57ef2d6e8f17ec898b64e728351. Integrated main:
e53852064d3ef5a2eafec47d754c27504b11de5f, including PR210/211.
The full formalization goal remains ACTIVE. No production Haskell changes.

## Checked modules

- SourceSynthesisCurrentArrowReification: 119 lines; 2 laws; SHA256 338a532f341c4929bc477b3ee5a4dc7ba88656c2c3523ec484393bade6b68ab9.
  - MicroCFTA.SourceSynthesisCurrentArrowReification.candidateRigid_ne_marker
  - MicroCFTA.SourceSynthesisCurrentArrowReification.marker_child_arrow
- SourceSynthesisCurrentComputedWidthSharedCompletion: 112 lines; 1 laws; SHA256 8c33da87e26ce332bf77b04eda94cfd593439cc9415edcd0b9f74941daf2f329.
  - MicroCFTA.SourceSynthesisCurrentComputedWidthSharedCompletion.accepted
- SourceSynthesisCurrentGeneralizeReification: 485 lines; 1 laws; SHA256 04fb9ad4ea24c0b4677f2bcd2b7dbb8769ce9b999ef06b04ab16b5fd4b12af06.
  - MicroCFTA.SourceSynthesisCurrentGeneralizeReification.generalize_instance
- SourceSynthesisCurrentInitialComputedRoom: 96 lines; 2 laws; SHA256 e3d0ab46926aebafe61f34ceed957b6cdc1f5c448f60ee480b6262db9952b0e2.
  - MicroCFTA.SourceSynthesisCurrentInitialComputedRoom.profile_of_build
  - MicroCFTA.SourceSynthesisCurrentInitialComputedRoom.room_of_build
- SourceSynthesisCurrentOrdinaryComputedWidthModelWork: 182 lines; 1 laws; SHA256 6827a5a50c265cc751a353a0b27c312660a8404df67fbfd5e56b99d9a9237571.
  - MicroCFTA.SourceSynthesisCurrentOrdinaryComputedWidthModelWork.uses_computed_native_initial
- SourceSynthesisCurrentRigidTypeReification: 109 lines; 2 laws; SHA256 4a793e2009e71fb9dc72a063d89393fd8c002695b32e4adff94ca579d3451c6f.
  - MicroCFTA.SourceSynthesisCurrentRigidTypeReification.typeNode_only
  - MicroCFTA.SourceSynthesisCurrentRigidTypeReification.current_typeNode_only
- SourcePruningEnumerationSharedEagerFrontierResources: 253 lines; 1 laws; SHA256 d99218ef7e6ee3c6a73e6abcc2544676491522fa5bc9380e9fc698a5095e2cc8.
  - MicroCFTA.SourcePruningEnumerationSharedEagerFrontierResources.visitSelected_frontier_models_packet
- SourcePruningEnumerationSharedEagerNullaryResources: 227 lines; 1 laws; SHA256 5da03d61a39686e187fcd20bdce75066b457edc689229b2edd8fc1f2a0818ec3.
  - MicroCFTA.SourcePruningEnumerationSharedEagerNullaryResources.visitSelected_nullary_model_packet

## Capacity from original inputs

CurrentInitialComputedRoom.profile and bits depend only on the original
library, query, signed size and native budget. They observe the deterministic
current source constructor and its deterministic native build. Error/pending
fallbacks assert no successful source/build result. The exact initial phase
forecast and phaseNeed discard caller/request values. emptyValue_live fixes
its inherited payload to some [] at every initial cache. The output envelope,
heap seed and joined numeric profile therefore have no width/cache dependence.
profile_of_build identifies the EXACT worker profile on the SAME actual source
and build at arbitrary cache/width. room_of_build applies the existing
roomBits/room_computed law at that SAME profile. These are mathematical
noncomputable selectors. They are not an extracted Haskell width algorithm.
No second initializer, native-build producer or completed graph is used.

CurrentComputedWidthSharedCompletion.accepted invokes the checked current
worker once at this original-input width. It retains the ENTIRE initializer
and ENTIRE checked endpoint. The full cache/Receipt/conjunction Fields/Context/
inventory/caller/globals, Facts/Available/roles/growth/issued/physical origins/
inherited identity/readiness/closed/Original remain. The exact computed
request/output/need and base literal ranges remain. All larger outer fuels
return the SAME result/after and literal ranges. One graph/next/final retains
Checks, full Reads globals-to-final, Post/Frame/Fits/full forecast physical
Heap, Available/NodeLaw/SharedReady/Type-profile GuardHeap/History/closed/
NodeFields/whole ValueFields. The same returned build discharges Room.
No external Room, future Ready/model/worker or second producer is assumed.

CurrentOrdinaryComputedWidthModelWork.uses_computed_native_initial removes
only the external Room implication and bits input from the previous complete
ordinary checked startup theorem. The bits expression uses ORIGINAL lib,
query, Int.ofNat Program.components and budget. The source per-use Eligible,
empty libraryAvoid, original token Perm and empty pending premises remain.
The EXACT annotated original Program/goal/count, entire initializer and worker,
one SAME-result startup Packet/canonical/waiting/candidate/carrier/reference
receipt and actual satisfying assignment/origins/pending-size/work remain.
All 55 conjunctions and four universal quantifiers remain. Work is
(N+1)*N + root-expandability bit, where N is annotated-term size. It does not
bound total generator work. A sufficient mathematical width is now derived.
Fixed Haskell word capacity and executable correspondence remain separate.

## Exact header repair

An unchanged-header diagnostic with a deliberate proof failure returned
unknown free variable _fvar.23209 BEFORE its proof tactic. This isolates the
observed failure to header elaboration. The specific Lean internal cause is
not established. The final repair expands only the outer let bits binding
at eight bound width occurrences. The identity is exactly
let bits := B; P bits = P B by definitional zeta reduction. Its proof body is
byte-identical to the staged 183-line attempt. Every input/instance, 55
conjunctions and four universal quantifiers remain. No premise or output was
removed. No compiler option or linter was disabled. The final 182-line source
passes strict, full and portable checking. Runtime JSON records the exact
source hashes and header comparison; the reproducible packet checks final code.

## Actual eager resource bases

SharedEagerNullaryResources.visitSelected_nullary_model_packet derives the
actual own projection/arity/prefix from CURRENT accepted model and packet.
It invokes the existing own-model producer once. It constructs the real
nullary ordinary fragment and derives the complete same-metadata Packet,
Post.refl at SAME entire Caller/inventory/full Memos/query/Fits/physical Heap,
exact counter growth, old-variable protection/origin/stratification and bounds.
The same assignment extension satisfies before/after and fills the accepted
term. The visitor/consume identity is the ACTUAL visitSelected operation.
It does not claim that arbitrary consume preserves resources. No captured
target is labelled Admitted before the separate captured finalization.

SharedEagerFrontierResources.visitSelected_frontier_models_packet covers
CURRENT selected children whose ordinaryNonterminal test is false. Each
actual eager child therefore uses the old fallback dispatch once. Private
current-member congruence preserves the ENTIRE complete/stopped receipt.
Pure selected_admission derives own projection/arity internally. ONE existing
SelectedEdge model/resource producer returns the SAME endpoint/full Memos/
Post/Fits/Heap/cache/model/origin fields. The theorem derives same-metadata
Packet/order and identities for actual eager and height-guarded visitors.
Its existing Reserved bits/seed/edgeCost premise remains valid ONLY on this
fallback frontier. It is not a budget for deeper ordinary descendants or
all tuple alternatives. The arbitrary consumer's effects remain separate.

## Reverse current Type primitives

CurrentGeneralizeReification.generalize_instance extracts ONE raw substitution
from actual current generalized-annotation acceptance under canonical PCS.
Structural replace inversion retains path membership and same-tree rebuilding.
Actual equality classes identify repeated-variable images. Current universe
reification and existing lifted substitution reify only demanded images.
The conclusion retains exact candidateRigid(substTy rho scheme) and RawAdmitted
only for names used by the scheme. No future rho/instance/membership, AliasSafe,
catalog separation, annotation or new typing hierarchy is supplied.

CurrentRigidTypeReification.typeNode_only proves exact finite rigid meaning
for arbitrary guard interpretation. Its current specialization observes the
escaped Type on the SAME term. Ordered children and documented Fun/2 remain.
It needs no TopHeld or universe admission supplier.

CurrentArrowReification.candidateRigid_ne_marker excludes the internal marker
leaf for EVERY raw type. marker_child_arrow recovers actual arrow children
and OrdinaryTyping.Equivalent to an arrow from a marker at child zero. It
applies to rigid query types outside RawAdmitted. It does not reflect encoded
equality to strict raw type equality. Typed already permits Fun/2 conversion.
Application PCS path inversion, original leaf/row/relevant/root induction
remain next. A complete reverse Typed theorem is not asserted here.

## Validation and full scope

All eight strict source packets pass. Full Audit passes: 5830 live modules,
nine affected, 4827 imports, 94048 axiom reports. All nine portable packets
pass from /tmp. All 261559 old Audit bytes remain after eight imports. Every
affected source hash is pinned. Effective memory.max and memory.high are
4294967296; memory.swap.max is zero. One Lean thread and the repository Lake
cache are used. No binary archive is copied. Standard axiom checks do not
establish Haskell compiler/extraction/runtime correspondence.

Deeper eager CPS resource/model preservation and an original/current-input
budget for ordered tuple tails, shared native effects and interleaved callbacks
remain open. Core storage is branch-max; shared native work accumulates in
source order. Old shallow cost and processed-length bounds are not deeper
eager bounds. Exact callback Frames do not describe whole allocation steps.
Use existing protection/origin/history across those state changes.

Source reverse soundness, earlier hooks/all alternatives, original-input whole
work/depth/fixed-host capacity, reduction/refold/weights, source order and
multiplicity/lazy demand, both inverses, full guards/signed/Word/Int/errors,
refinement/training and runtime correspondence remain explicit targets. Default
does not call boundDepth. Derived guard origins alone are not literal physical
projectability. Native annotation size is not Program component count.

No Haskell source/Cabal/production repair changes. FINDINGS retains external
owner post1182's reproduced Liquid duplicate-name contradictory-refinement
and first/each/last-reader defects, exact controls and intended LAST type AND
refinement repair. Owner branch fix/liquid-repeated-argument-names is not yet
reported pushed or merged. ROOT has not repeated that runtime experiment.
Liquid arguments have optional use; Hectare original required-token coverage
permits extra unmarked uses. Do not duplicate the external repair. Earlier
PR210/211 focused Nix/GMP/fourmolu checks remain: 16 examples, zero failures;
no full Haskell suite/corpus/benchmark claim. Historical source pins remain.
Liquid Haskell results do not automatically enter Lean or certify execution.

## Frozen next application and eager descent plans

These read-only plans describe NEXT work. They are not additional public
premises or checked theorems. Runtime-only application/leaf/unary source drafts
must pass their own strict/full/portable checkpoint before any further claim.


# Current application step for reverse row soundness

Read-only audit, 2026-11-12 17:37 CET. Generalize, rigid Type and arrow inversions
are checked. The next cut connects the actual application guard to ordinary
Typed. It uses the existing source evaluator and independent typing judgment.

## One minimal public observer

Proposed module: SourceSynthesisCurrentApplicationSoundness.lean.
Open the existing source namespaces. Symbol, literal and marker retain their
usual meanings. Expression is FirstOrderConstruction.Expression.

```lean
theorem application_typed [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query)
    (functionExpression argumentExpression : Expression)
    (annotation actualMarker functionTerm argumentTerm : Term Symbol)
    (functionProgram argumentProgram : Program) (functionType argumentType : Ty)
    (children : forest (SourceEqualityPCSGuard.holds formulas solver) []
      (mapChildren literal [(context lib query).types, arrowMarker top,
        functionExpression, argumentExpression])
      [annotation, actualMarker, functionTerm, argumentTerm])
    (guardHeld : SourceEqualityPCSGuard.holds formulas solver
      (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      (.node (literal "app") [annotation, actualMarker, functionTerm, argumentTerm]) = true)
    (functionTyped : Typed lib query functionProgram functionType)
    (functionProjection : Projection literal Prod.fst functionTerm functionProgram)
    (functionAnnotation : functionTerm.atPath [0] = some (candidateRigid functionType))
    (argumentTyped : Typed lib query argumentProgram argumentType)
    (argumentProjection : Projection literal Prod.fst argumentTerm argumentProgram)
    (argumentAnnotation : argumentTerm.atPath [0] = some (candidateRigid argumentType)) :
    ∃ resultType : Ty,
      Typed lib query (.app functionProgram argumentProgram) resultType ∧
      annotation = candidateRigid resultType ∧
      Projection literal Prod.fst
        (.node (literal "app") [annotation, actualMarker, functionTerm, argumentTerm])
        (.app functionProgram argumentProgram)
```

The forest and guard are the exact observations obtained by unfolding the
accepted application edge (FirstOrderConstruction.application:47 and
InternedGuardedSyntax.edgeMeaning). They are not future table memberships.
The child IH receipts refer to the SAME functionTerm and argumentTerm in that
forest and guard. Each raw type belongs to its own receipt. No global rho or
independently chosen Program witness is supplied. The two projections build
Projection.application on the SAME whole term.

Keeping the actual four-child forest exposes the true marker source. No caller
must assume actualMarker is already the internal marker. The proof reads its
second slot. The result-type universe membership is present in the actual
forest but does not need an additional admission premise for this typing step.

## Exact equality-path argument

First derive actualMarker = marker. The marker slot accepts arrowMarker top.
Use CurrentRigidTypeReification.typeNode_only:70 at the historical literal raw
tCons "(->)" []: that typeNode is exactly arrowMarker top. This uses the generic
rigid lemma, not current_typeNode_only, which would escape that constructor.
No top-held or universe hypothesis is needed for rigid uniqueness.

From guardHeld extract its Sat conjunct with SourceEqualityPCSGuard.holds_exact:45.
Rewrite GeneralizeSyntax.eqGuard_eq_source:113 and apply
SourceEqualityPCSGuard.normalize_sat:20 to obtain the ORIGINAL three ClassSat facts.
Each pair has distinct literal Nat paths. Its ClassSat gives an existing common
subterm at both paths. No separate Active payload or solver soundness premise
is required, and absent paths must not be treated as an equality witness.

For the first pair, [1] is marker and [2,0,0] is the function annotation's child0.
Language.atPath_append:445 and functionAnnotation give
(candidateRigid functionType).atPath [0] = some marker.
CurrentArrowReification.marker_child_arrow:92 then returns domain and codomain,
Equivalent functionType (tFun domain codomain), and the complete candidate arrow.
This includes the documented Fun/2 alias. It gives no strict raw Ty equality.

For the second pair, [3,0] is candidateRigid argumentType and [2,0,1] is
candidateRigid domain. Thus candidateRigid_eq_iff gives Equivalent argumentType
domain (Pr210TypeReflection:171). Typed.conversion changes each child type to
its required arrow/domain. Typed.application then types the ordinary App at codomain.
For the third pair, [0] is annotation and [2,0,2] is candidateRigid codomain.
It supplies the SAME result annotation equality in the proposed output.

No extra semantic bridge is missing inside this local argument. A small
private pair-path extraction helper and the exact source forest decomposition
are the remaining proof work. Do not introduce a new typing or term syntax.

## Remaining row and root work

Invert actual successful termsRows and relevantRows equations by size. For leaf
groups/argument-only entries, GeneralizeReification.generalize_instance:431
extracts each occurrence's own rho. Rigid query leaves use current_typeNode_only
and Pr211QueryBindings.queryBindings_member:62 for ORIGINAL last lookup.
The application observer supplies the induction step in size2 restricted/fallback
rows and larger positive splits. Avoid rows only select existing leaves, so no
avoid=[] assumption is needed for reverse typing. Resolve actual winning name
keys; canonical query bindings supply coherent types despite duplicate names.

At the root, current_typeNode_only fixes the exact rigid goal. The filter PCS
pair [[0],[1,0]] and candidateRigid_eq_iff permit Typed.conversion to ORIGINAL
queryGoal. CurrentProgramStructure.current_root_structure:235 and
ProgramTermSize.accepted_projection:155 already give requested component counts.
Projection.toProgram_eq:61 identifies that counted Program with the SAME typed
Program. No new count bound or weighted annotation-size argument is required.

Do not add blanket RawAdmitted query/goal assumptions, ordinary Eligible,
tokens.Perm, model, native worker or Room suppliers to reverse typing.
Marked-token coverage is a separate result and permits extra unmarked uses.
This note adds no code, compile, runtime acceptance or Haskell correspondence claim.

# R247: genuine ordinary-descendant CPS induction

Status: READ-ONLY UNPROVED PLAN. ROOT reports frontier 253L/d99218ef PASS1.
Source paths below are relative to lean/MicroCFTA/. Only this runtime note changed.

## What survives at the same actual endpoints

MergedOrdinaryHeight.lean:16/50 defines height on the immutable complete native
payload and proves strict decrease for every actual ordinary edge child.
SourcePruningEnumerationSharedEagerChildren.lean:57/184 transports that fact
through SAME CachedOwn.prepare and staged input membership. Prefix allocation
changes the enumeration core, not the child value or its physical height.
SourcePruningEnumerationEdgeInputs.lean:25 supplies available/closed genuine
children, exact buckets, counter growth, safe storage and actual indexes.
A later actual Post transports OLD payload availability with effects.keeps.available
(SourcePruningEnumerationSharedPreparedFiniteSiblingResources.lean:263). No identity-to-height inverse
is needed: canonical sharing does not make physical IDs unique by source depth.
SourceCurrentConstrainedCapRequiredResources.lean:50/59 bounds actual row count
and arity from CURRENT HeapFits/availability. SourcePruningEnumerationRecursiveReservation.lean:191
(edge_shape_from_packet) derives arity and projected own-class width from current
Packet/Fits/physical guard Heap. GuardWidth.project_le is in
SourcePruningEnumerationGuardWidth.lean:39. Descended bucket lengths do not
increase: SourcePruningEnumerationCostBounds.lean:17/23.
These fixed payload bounds persist when the actual caller/memos advance. Native
heap growth can change later profiles and callback roots; it does not rewrite
this captured immutable ordinary subtree or its staged input list.

## New induction and reservation that are actually needed

Ordinary height alone proves local recursion termination. It does not bound the
work performed by callbacks or by all alternatives. The private CPS IH needs:
current Packet/Context + model, actual immutable input/buckets, Fits/physical Heap,
and a DERIVED arithmetic plan for its actual success and stopped continuations.
Keep structural resource/stop preservation for ALL visited rows separate from
compatible-model progress for the chosen accepting row; its model does not
certify preceding alternatives.
Tuple-list and row-list induction must invoke it at the actual reached Caller,
full Memos, inventory and branch cache, then run the tuple tail BEFORE siblings.
Current source selection must certify actual selected membership; otherwise the
height and availability proof do not apply. A row-count bound also needs actual
selector length/multiplicity control, or a count computed from its literal list.
The frontier needed neither condition because it never executed child edgesOf.

A derived plan must distinguish three quantities. Source cache counter/mass
bounds use the maximum reached branch, since Core/Cached are cloned by choices.
Native work/profile bounds sum earlier choices and multiply tuple-tail work by
the number of actual child successes. Callback work occurs at EVERY such success.
SourcePruningEnumerationSharedEagerChildren.lean:42 prepends nested processed
receipts, so old processed.length<=selectedEdges.length (SourcePruningEnumerationSharedPreparedFiniteSiblingResources.lean:207)
is NOT an eager row-count certificate. Do not index eager processed receipts as
if each were one outer row. Preserve their full actual lists and stop structure.

One possible UNPROVED count schema from current payload bounds: let H be its
ordinary height, M a current row-count bound, A arity, W own-guard width, and
B=current bucket length+H*W. For fallback, callback count<=1 and mixed-query
steps<=B+1. A tuple of a children costs sum_i(product of earlier success bounds)
*childWork_i; its success bound is product of child success bounds. Sum these
over actual ordered rows. A coarse majorant could use C0=1, Q0=B+1,
C(h+1)=max(1,M*C(h)^A), Q(h+1)=Q0+M*(sum_(i<A) C(h)^i)*Q(h).
This is a counting PLAN, not a proved native profile/Room or workFuel theorem.
A callback bound K would contribute at most C(h)*K ONLY in the same counted unit.
The actual outer callback also narrows/restarts. Its forecast must be composed
at each planned Seed, not appended as one incoming-query count at the end.
SourcePruningEnumerationSharedRecursiveReservation.lean:42/50/54 already shows
that phase order: final/step/stage place the smaller-depth callback after EACH
head. General eager composition must replace its shallow head and mass forecast,
retain checked profile-role/alphabet monotonicity, and derive arithmetic admission
along the whole plan from ORIGINAL/CURRENT input data and an explicit CURRENT
capacity condition. There is no unconditional fixed-word Room promise. No future heap or completed
packet may supply this plan. SourcePruningEnumerationSharedIncomingReservation.lean:77 is legitimate
current arithmetic admission; it does not by itself derive the new plan length.
The existing row graph budget (SourceNativeOrdinaryRowsBudget.lean:71) certifies
ordinary graph structure/term bounds, not eager shared work or callback cost.

## Resource/model callback IH

Retain full SAME-run Post/final.query, inventory/full Memos, current metadata
Packet, Fits/physical annotation Heap, counter/mass, origin/protection/pending,
stratification, and all completed outputs. The semantic IH retains one extension
agreeing below the original counter, before/after Satisfies at actual native
heaps, fill and assignment origins. Later buckets must survive that extension;
SourcePruningEnumerationSharedChildTraversalModelResources.lean:34/56 shows the current shallow argument.
Native model transport is SourcePruningEnumerationNativeLanguage.lean:87 (satisfies_keeps). Actual callback
recordTypes retains its own Frame and metadata update (SourcePruningEnumerationSharedPreparedHookInduction.lean:116/139).
Its ResumeComplete:92 still names OLD resume; versioning an operator did not
prove its eager IH. Do not demand CompressionFrame across eager allocations.
Stopped callbacks keep exact accumulated receipts/outputs and known-or-None
native endpoints. Normal rejection keeps its actual globals and resumes choice.
Even a compatible later row need not be reached after an unsupported prior row
or stopped tuple callback. Height/finite fuel do not discharge that reach gap.

## Smallest next genuine base if the recurrence is deferred

Prove one ACTUAL ordinary descent: a selected unary parent whose single actual
staged child is an ordinary node with ONE actual selected nullary row. Require
CURRENT child payload rows=[leaf], edgesOf child=[leaf], leaf.children=[], and
ordinaryNonterminal stagedBucket child=true. Derive both projections/arity and
child model from current parent acceptance; singleton native meaning is exposed
by InternedGuardedLanguage.lean:24/27. No future Packet/receipt supplier.
Use actual parent own prefix ONCE, checked prepared_child_eager, and the nullary
model/Packet base ONCE for that reached child. Both prefixes/residual updates are
pure: before the outer consumer, the ENTIRE native Caller/inventory/full Memos,
Fits and physical Heap are unchanged. The local mixed-query reservation is zero.
Derive the actual parent fragment/model/Packet and exact combined fresh-slot
counter bound; add its real CPS identity. The child consumeSelected prepends
its complete inner receipt to BOTH complete and stopped consumer results; do not
claim the result equals a bare outer consumer or that arbitrary consumers preserve
resources. There is no later child row on which unbounded consumer work could run.
This crosses an ordinary descendant, which neither nullary nor fallback-frontier
proof does. It adds no reservation hierarchy and supplies the first recursive
semantic case. Multiple child rows, tuple products, arbitrary callback budgets,
source/default order, lazy native effects and global completion remain open.
