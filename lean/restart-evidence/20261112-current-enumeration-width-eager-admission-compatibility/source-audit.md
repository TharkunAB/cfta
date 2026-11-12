# Current-input Program outputs and eager arithmetic admissions

Base `1fe4b017b0d8e09341c0c51acf739f58ed2711d5`; integrated main `e53852064d3ef5a2eafec47d754c27504b11de5f`.
Three current source modules have 630 lines and six public laws. Four laws
are new. Two original forecast laws and the entire checked 224-line prefix
remain byte-identical. Every current own-source strict compiler and explicit
public declaration/axiom report passes. Only propext, Classical.choice and
Quot.sound occur. The actual full closure and four portable packet results
are in checked.json and portable-check.json. All 265474 old Audit
bytes remain an exact suffix. Only the two new module imports are prepended.
The existing forecast import is retained without duplication.

## Exact source pins and public statements

### SourceSynthesisCurrentProgramEnumerationWidth

62 lines, 2 public laws (2 new). SHA256 `737c1c72eaf371d8777b7f9f884ff6af5f5ffb81b69a5ca07d8160cabdc6131a`.

```lean
theorem enumProfile_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    enumProfile lib query signed depth =
      (SourcePruningEnumerationSharedPreparedReservation.final depth (seed heap) 0).2
```

```lean
theorem enum_reserved_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    SourcePruningEnumerationSharedPreparedReservation.Reserved
      (enumBits lib query signed depth) depth (seed heap) 0
```

### SourceSynthesisCurrentProgramOutputs

187 lines, 1 public laws (1 new). SHA256 `b8985a4833b09135d069c361a7423d677311f504d6402fb104b3b36a5edbb197`.

```lean
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = [])
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (order : Metadata Typing → List Nat → Option Nat) :
    let bits := SourceSynthesisCurrentProgramEnumerationWidth.enumBits lib query signed depth
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
        ValueFields (Origin (encodedLibrary lib)) literal value ∧
        ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
          ProgramSlots (Origin (encodedLibrary lib)) literal heap
            (EnumerationState.initial handle) (fun uv => uv = 0) ∧
          let startup : Cached :=
            ⟨EnumerationState.initial handle,
              fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
              fun _ => none⟩
          let initialCaller := SourceCurrentAllocatedPartialInitialization.caller (bits + 2) cache heap
          let initialSeed := seed heap
          ((Packet formulas solver
              (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
              initialCaller SourceCurrentAllocatedPartialInitialization.globals metadata startup ∧
            EnumerationValidity.Canonical startup.core ∧
            startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
            SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
            EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
            ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
              ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot)) ∧
            EnumerationCarriers.CarriesGraph startup.core 0 ∧
            EnumerationGraphReferences.ReferencesCarry startup.core) ∧
          Fits initialSeed.2 initialCaller.checked ∧
          Heap (fun guard => guard ∈ initialSeed.1) heap ∧
          SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth initialSeed 0 ∧
    ∃ bound outcome,
      (
      (∀ extra, run holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none order (bound + extra) depth
        metadata initialCaller SourceCurrentAllocatedPartialInitialization.globals.query startup = outcome) ∧
      OutcomeResources formulas solver initialCaller
        (SourcePruningEnumerationSharedPreparedReservation.final depth initialSeed 0) outcome ) ∧
      ∀ output ∈ emitted outcome, ∃ finalMarked : Nat → Prop,
        (∀ uv, uv = 0 → finalMarked uv) ∧ finalMarked 0 ∧
        SourceSynthesisProgramEnumerationRoles.ProgramSlots (Origin (encodedLibrary lib)) literal
          output.caller.checked.native.machine.heap output.cache.core finalMarked ∧
        output.metadata = none ∧
        EnumerationPureSelection.next (fun _ => none) output.cache = .done ∧
          ∃ (next : Inventory) (final : Memos) (outputMetadata : Metadata Typing),
            SourceCurrentAllocatedPartialInvariant.Post formulas solver next initialCaller output.caller final ∧
            final.query = output.queries ∧
            Packet formulas solver next output.caller final outputMetadata output.cache ∧
            (output.metadata = none ∨ output.metadata = some outputMetadata) ∧
            Fits (SourcePruningEnumerationSharedPreparedReservation.final depth initialSeed 0).2
              output.caller.checked ∧
            Heap (fun guard => guard ∈
              (SourcePruningEnumerationSharedPreparedReservation.final depth initialSeed 0).1)
              output.caller.checked.native.machine.heap ∧
            ∃ (level : Nat → Nat) (frontier : Nat),
              EnumerationOrder.Stratified output.cache.core level frontier ∧
              ∃ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                (after : EnumerationState.State Symbol Constraint),
                (∀ extra,
                  Success (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra))
                    output.cache.core actualPartial after ∧
                  ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra) output.cache.core) =
                    [.ok (actualPartial, after)]) ∧
                EnumerationDriver.RenderStable output.cache.core after ∧
                EnumerationCompressionFrame.Frame output.cache.core after ∧
                EnumerationOrder.Stratified after level frontier ∧
                (∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
                  (assignment : Nat → Language.Term Symbol),
                  Satisfies language meaning assignment output.cache.core →
                    Satisfies language meaning assignment after ∧
                    SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
                ∃ program, SourceSynthesisProgramTermSize.Projection literal Prod.fst
                    (SourcePruningPositions.openProgram true actualPartial) program ∧
                  ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
                    SourcePruningPartialMatch.Completes assignment actualPartial full →
                      SourceSynthesisProgramTermSize.Projection literal Prod.fst full program
```

### SourcePruningEnumerationSharedEagerReservation

381 lines, 3 public laws (1 new). SHA256 `988794e6954f4e8e7e7594237f4655ad3f48017dd0d2d11be6eb8066efc9c75b`.

```lean
theorem eagerFinal_ge (depth : Nat) (seed : Seed) (ceiling : Nat) :
    Le seed.2 (eagerFinal depth seed ceiling).2 ∧
      seed.1 ⊆ (eagerFinal depth seed ceiling).1
```

```lean
theorem first_row_callback_le_final (depth : Nat) (seed : Seed) (ceiling : Nat)
    (positive : 0 < scalar (preparedSeed seed).2) :
    let captured := preparedSeed seed
    let N := scalar captured.2
    let b := ceiling + SourcePruningEnumerationGuardWidth.width captured.1
    let rowStart := eagerFinal depth (advance captured (ceiling + 1)) (ceiling + ceiling)
    let first := eagerFinal depth (advance rowStart (N * (b + 1))) (ceiling + N * b)
    let whole := eagerFinal (depth + 1) seed ceiling
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1
```

```lean
theorem eagerReserved_of_final_room (bits depth : Nat) (seed : Seed) (ceiling : Nat)
    (room : Room bits (eagerFinal depth seed ceiling).2) :
    eagerReserved bits depth seed ceiling
```

## Scope and coupling

The pure width selector matches only ORIGINAL library/query/signed-size/depth
and the deterministic current source/build expressions. SAME returned/built
equations normalize it to final depth(seed heap)0 and existing reserved_computed.
There is no second build producer, initializer, worker or Room provider. The
width is a mathematical sufficient width, not a fixed host-word guarantee.

The current-source accepted theorem retains the ENTIRE current initializer
receipt at the empty cache. Its public inputs are the successful current
front-end equation, chosen depth, formulas/solver, current empty-pending metadata
and driver configuration. It chooses enumBits from ORIGINAL inputs before
ONE actual initializer. The SAME Context/value/handle supplies startup/carrier
Packet, exact physical seed Fits/Heap, mass zero, nodeEdges selection, mark0
and ProgramSlots. Handle identity uses the two SAME encodeNode equations.
Then ONE checked no-stop ProgramOutputs producer supplies its ENTIRE stable
all-fuel OutcomeResources and unconditional per-output Program-root receipt.
No after-state Packet/roles/model/Room/finishedness or completed-worker supplier
is public. No old completed-nodeCall output is renamed raw startup. No second
initializer, native producer, worker or root reader is introduced.

This is the modeled cold SHALLOW route. Source construction must succeed.
Depth remains a chosen input. The theorem does not prove output existence, a satisfying Type assignment,
or eager/default correctness. Every full completion of each actual
partial root shares its Program projection. The old exact Eligible construction/
pruning statement retains its own avoid-empty and mathematical-width boundary.
This structure/startup cut needs no avoid-empty premise.

The eager arithmetic definition depends only on original bits/depth/Seed/mass
and deterministic finite plan stages. Its only public Room premise refers to
that ORIGINAL computed final profile. Private tuple/row/callback admission
parameters close recursively from smaller depth. Numeric Room/Admits/Reserved
contain no future Fits, Packet, model or execution provider. The added theorem
proves computed stage admission only. Actual eager execution domination, fuel
adequacy, native/full-Memos resource preservation and Program roles remain
open. The concrete CPS depth/height/tuple/consumer proof is the next work.

No Haskell source changed. FINDINGS keeps the external repeated-name Liquid
LAST-type/refinement defect, its owner and current main pin. Old counterexamples
and current repairs remain. Default Mu semantics, satisfying models, source
adequacy, total original-input work/capacity, order/multiplicity, both inverse
laws and verified Haskell compiler/extraction/FFI correspondence remain open.

## Component notes and reviews

### current-source-program-outputs-next.md

# Current source to the same no-stop Program outputs

Read-only audit, 2026-11-12 23:30 CET. No implementation or compilation.
The smallest honest composition starts at the COLD raw source value. It does
not require the completed nodeCall from CheckedHereditary208/ComputedWidth112.

ONE producer: CurrentProgramSlotsInitialization.accepted:34 (71-line module).
Keep its ENTIRE fields/cache/value/heap/built/preparation/conjunctionFields/
Context/Facts/Available/ProgramValue/growth/issued/Derived-guard-Heap/identity/
emptyValue/Ready/closed/Original/ValueFields/handle/encode/decode/ProgramSlots
receipt. Fix initial cache to Cache.emptyState, initial validity to empty_valid,
valid role predicate to Origin(encodedLibrary lib), and marked uv to uv=0.
The actual caller is Initial.caller (bits+2) cache heap; inventory and full
Initial.globals are those of this SAME built value and prepared cache.
There is no need to call CallerInitialization80 separately.

Packet: InitialPacket.initial_packet:30, or InitialCarriers.initial_packet_carriers:27,
takes THAT Context/Available/closed and CURRENT metadata.pending=[]. It supplies
literal startup, Packet, Canonical, stored root, suspendedBound=0, exact waiting
and every candidate flag; the carrier variant also keeps root/reference carriers.
Its returned handle equals the retained initializer handle by their two
encodeNode value=some handle equalities. No native operation is repeated.
startup.core is exactly EnumerationState.initial handle, so existing mark-zero
ProgramSlots applies definitionally. initialMass uses ceiling=0 and suspended=0.

Seed: OriginalSharedRankCompletion.seed:41 is
  (ConjunctionGuardUniverse.guards heap,
   <heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap>).
SAME initial Fits is <le_refl, le_refl, le_refl, InternedValueMassHeap.initial heap facts>.
SAME physical Heap follows from ConjunctionGuardUniverse.initial:26 heap facts.
CheckedHereditary208:126-129 already uses these exact proofs; these are observers
of current heap data, not a completed-worker endpoint or future resource supplier.
Keep the initializer's Derived guard Heap too; it is a different predicate.

Selection: choose InternedEdgeResidency.nodeEdges:16. On .node it is EXACTLY rows.
selectionMembers is fun _ _ _ _ _ member => member; selectionLength is le_refl.
Do not substitute MergedFreshOrdinaryExposure.nodeEdges:37: that is a heap-changing
fuelled exposure, not this Node->List selector. A different actual ordering may
retain the generic old selection inputs, but is a separate configuration cut.

Capacity is the only small NEW source-input bridge. CurrentInitialComputedRoom.bits
covers a NodeCall forecast; no existing law says it reserves the enumeration
final depth (seed heap) 0. Reusing it without a comparison would be unjustified.
The exact proposed pure selector (same implicit equality instances throughout):
  enumProfile lib query signed depth :=
    match CurrentConstruction.firstOrderRaw lib query signed with
    | .error _ => <0,0,0,0>
    | .ok expression =>
      match build (ordinarySymbols expression) [] empty with
      | .pending _ _ => <0,0,0,0>
      | .done _ heap => (SharedPreparedReservation.final depth (seed heap) 0).2
  enumBits lib query signed depth := ParentInitialRoom.roomBits
    (enumProfile lib query signed depth)
Small NEXT public headers, using current existing Profile/Reserved only:
  enumProfile_of_build (lib query signed expression returned depth value heap built) :
    enumProfile lib query signed depth =
      (SharedPreparedReservation.final depth (seed heap) 0).2
  enum_reserved_of_build (lib query signed expression returned depth value heap built) :
    SharedPreparedReservation.Reserved
      (enumBits lib query signed depth) depth (seed heap) 0
The shared explicit binders for these two headers are:
  (lib : Library) (query : Query) (signed : Int) (expression : Expression)
  (returned : CurrentConstruction.firstOrderRaw lib query signed = .ok expression)
  (depth : Nat) (value : Node) (heap : State Symbol Constraint)
  (built : FreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
Here returned and built are the SAME literal source/build equations used by71.
The first proof is simp [enumProfile,returned,built]. The second rewrites it and
uses SharedPreparedReservation.reserved_computed:312 (or reserved_of_final_room:272).
The pure match is a deterministic input expression, not a second build producer.
This computes a mathematical sufficient width, not a fixed host-word guarantee.

Exact future wrapper shape: original lib/query/signed/expression/returned, depth,
formulas/solver, current metadata/emptyPending, and existing current driver
holeKey/fits/admits/graph/templates/checkEmpty/order. Choose bits=enumBits from these
ORIGINAL inputs before the ONE71 call. Preserve its entire literal result above.
Append exact same-handle startup/carrier packet plus its SAME Fits/Heap, then
invoke SharedPreparedProgramOutputs.run_finite_complete_resources_program_outputs
ONCE with inventory/build caller/globals/startup/metadata, seed=(seed heap), ceiling=0,
valid=Origin(encodedLibrary lib), marked=(.=0), root=rfl, selector=nodeEdges.
Append its ENTIRE bound/outcome/stable all-fuel/OutcomeResources and unconditional
each-output metadata-none/finished/extended-marks/ProgramSlots/full Program-root
receipt. This uses no second native build, initializer, pruning worker or readback.
There is no supplied after-Packet/roles/model/Room/finishedness/provider premise.

The new wrapper retains the source initializer71, not a fictional nodeCall endpoint.
208/112/Typed158 remain separate completed-pruning results; their outputs are not
renamed as the raw startup. Program-output shape alone does not establish ordinary
Typed for every emitted Program or existence of a satisfying ground completion.
No avoid=[] premise is needed for this source-structure/startup cut; existing
positive Eligible/root language completeness still has its explicit avoid=[] domain.
Depth remains an explicit INPUT, with no adequate-depth or output-existence claim.
The worker remains shallow shared prepared enumeration, with default/eager/Haskell
correspondence and whole-search completeness/termination separate.

### shared-eager-admission-note.md

# Original-plan query admission
Status: UNCOMPILED EXTENSION. Root owns all compilation and publication.
Source: SourcePruningEnumerationSharedEagerReservation.lean, 379 lines.
SHA256: d07876368198c985f41d63346642b8998f8f369874d1a2a91df06bc9d0b8a07a.
The CHECKED224/f8bcdd4c source is the exact byte prefix. Snapshot:
shared-eager-reservation-224-f8bcdd4c.lean. The failed738 snapshot is separate.
All old definitions and public statements/proofs remain unchanged.
New definition/header were frozen before the proof:
shared-eager-admission-definitions.lean.txt SHA98a867ea44114c4a7b9c059edfc28ae615dc8282dc43e8efdd9b7a2299d0bda3.
shared-eager-admission-header.txt SHA940584a482fd1f04f32d75c4267b3eead024f66742f1b7b573d68ac39a256356.

New public API in MicroCFTA.SourcePruningEnumerationSharedEagerReservation:
- eagerReserved bits depth originalSeed originalMassCeiling.
- eagerReserved_of_final_room bits depth seed ceiling room.
The theorem accepts ONLY Room at eagerFinal depth seed ceiling's profile.
Existing eagerFinal_ge and first_row_callback_le_final remain intact.

The new predicate computes admission over exactly the mathematical plan stages.
Fallback requires existing IncomingReservation.Reserved bits seed (B+1), then
its concrete continuation's arithmetic reservation at that reached planned Seed.
Tuples put the tail predicate INSIDE the head continuation. Ordinary rows use
all exact iterate entries, after the initial fallback phase. Outer callback
reservation is recursive eagerReserved at smaller outer depth, updated planned
Seed and the path-specific mass ceiling. No execution witness is requested.

The proof uses only inflationary profile/alphabet growth within this plan,
Room.mono, iterate_add and existing reserved_of_final_room. Private generic
continuation and child admission hypotheses are mathematical and DISCHARGED by
height/tuple/outer-depth induction. No cross-seed monotonicity is used.

This isolates the remaining admission bridge before an operational resource IH.
Actual eager execution domination, stable common workFuel, full OutputResources
and OutcomeResources preservation are NOT proved by this extension. Their exact
public/private contracts are frozen in coupled-eager-resource-contracts.md.
The final-profile Room is an input-derived sufficient arithmetic condition.
It does not assert that a future heap fits, nor derive capacity for fixed64 bits.
No executable worker, existing checkpoint source, compiler, Git or Haskell changed.

Focused repair, 2026-11-12 23:52 CET: Root reports379/d078 reached only a
default200000 heartbeat timeout in the final public proof; no earlier diagnostic.
The381-line candidate988794e6954f4e8e7e7594237f4655ad3f48017dd0d2d11be6eb8066efc9c75b
changes only that proof. It explicitly unfolds the two positive equations and
generalizes captured Seed/scalar/guard width before the typed induction lemma.
No heartbeat option changed. All frozen definitions/header and checked224 prefix
remain exact. Root recheck pending; original379/d078 is preserved separately.

### r258-eager-admission-scope-review.md

# R258 eager arithmetic-admission scope review

2026-11-12 23:54 CET. Read-only review of the original immutable candidate.
Source: SourcePruningEnumerationSharedEagerReservation-d0787636.lean, 379 lines.
SHA256: d07876368198c985f41d63346642b8998f8f369874d1a2a91df06bc9d0b8a07a.
Its first 224 checked lines are byte-identical to prior source f8bcdd4c.
Current 381-line revision SHA256: 988794e6954f4e8e7e7594237f4655ad3f48017dd0d2d11be6eb8066efc9c75b.
That revision changes only final proof elaboration. All definitions and
public headers match the reviewed immutable source exactly.
The original new law is UNVERIFIED; a timeout does not certify it.
Alpha owns its separate proof repair. No substantive scope concern found.

Exact public definition header at 262:
def eagerReserved (bits : Nat) : Nat → Seed → Nat → Prop
Its only inputs are original bits, depth, Seed and mass ceiling. At zero
depth it is True. At positive depth it computes preparedSeed, scalar limit
and alphabet width, then uses nodeReserved with eagerFinal at smaller
depth and predicate eagerReserved at that SAME smaller depth. No external
callback, admitted predicate or after-state is accepted by this definition.

Private definitions at 233/238/249 combine deterministic plan stages.
fallbackReserved requires SharedIncomingReservation.Reserved at its
computed seed and recursive admission at its computed advance result.
tupleReserved fixes its tail and admission from the same tuple plan.
nodeReserved quantifies only row index < computed limit, at the explicit
iterate row first index seed. It quantifies no actual future heap, Core,
caller, Packet, resource producer, execution or after-state.

SharedIncomingReservation.Reserved:77 is exactly
∀ index, index<count → Admits bits (advance seed index).2.
CreditProfile.Admits:25 means Room bits profile OR Entry bits profile.
Both are numeric inequalities on that profile. Room:105 bounds its nodes,
edges and domains plus the explicit instruction-credit term. No physical
Fits, future Context or successful worker is hidden in these definitions.

Exact public theorem header at 364:
theorem eagerReserved_of_final_room (bits depth : Nat) (seed : Seed) (ceiling : Nat)
    (room : Room bits (eagerFinal depth seed ceiling).2) :
    eagerReserved bits depth seed ceiling

The Room premise is at the ORIGINAL computed eagerFinal profile, using
original depth/seed/ceiling. No caller-supplied final profile, future Room
oracle, quantified execution fit or child-resource provider is assumed.
Private accepted/growth premises are proof generalizations. The public
proof instantiates them from smaller-depth induction and eagerFinal_ge.
They add no assumption to eagerReserved or its public theorem.

If checked, the law derives arithmetic entry admission at computed plan
stages. It does not execute the eager worker, connect actual native states
to those stages, produce OutcomeResources, prove future actual Heap/Fits,
or satisfy Room for any chosen machine width. It gives no fuel adequacy,
output existence, model or end-to-end default result. Those execution and
resource correspondence obligations remain independent.
No source, compiler, repository, Git, Haskell or evidence action was run.

Historical candidate notes keep their original validation time. The exact
source pins above all have successful current own-source reports. The initial
admission draft hit the default proof-checker heartbeat limit at final373.
The final proof unfolds only the selected equations, then generalizes computed
limits before applying the existing induction lemma. Heartbeat settings, all
definitions and every public header remain unchanged. This compiler fix is
not an execution-time or work-fuel theorem.

## Preserved failed admission draft

Apply this standard zero-context reverse patch to the current forecast source
with `patch --output NEXT PREVIOUS PATCH`. The patch was replayed and checked.
The snapshot adds ZERO public laws. Expected379-line SHA256
`d07876368198c985f41d63346642b8998f8f369874d1a2a91df06bc9d0b8a07a`.

```diff
--- SourcePruningEnumerationSharedEagerReservation.lean
+++ admission-d0787636.lean
@@ -370,5 +370,3 @@
-      simp only [eagerReserved]
-      simp only [eagerFinal] at room
-      generalize preparedSeed seed = captured at room ⊢
-      generalize scalar captured.2 = limit at room ⊢
-      generalize SourcePruningEnumerationGuardWidth.width captured.1 = own at room ⊢
+      let captured := preparedSeed seed
+      let limit := scalar captured.2
+      let own := SourcePruningEnumerationGuardWidth.width captured.1
```

## Independent current-input coupling review

# R258 current-source Program outputs: coupling review

2026-11-13 00:01 CET. Independent read-only review. No substantive issue found.
CurrentProgramOutputs:187, SHA256
b8985a4833b09135d069c361a7423d677311f504d6402fb104b3b36a5edbb197.
Its exact public header at50-145 is byte-identical to the frozen96-line
current-program-outputs-header.txt, SHA256
7fb677b3b119b0d68e0645f88109b502ce8ac06151c3333884fb9e17220332af.
The sole compiler reported strict PASS for this source.

Dependency pins:
CurrentProgramSlotsInitialization:71, SHA256
9374295e5b120f35eb64db19a6031cf054f39b92850bbdb6ecb5530239f29bd7.
CurrentProgramEnumerationWidth:62, SHA256
737c1c72eaf371d8777b7f9f884ff6af5f5ffb81b69a5ca07d8160cabdc6131a.
SharedPreparedProgramOutputs:121, SHA256
509cf19617920893163688e76434d0f83d917928dc2f8432e0510d8b00add9e0.

Mechanical complete-conclusion comparison PASSED for both interfaces.
The initializer's ENTIRE tuple matches the new prefix after specializing
initial=Cache.emptyState and width=enumBits(original input,depth)+2.
The ENTIRE noStop worker/resource/readback conclusion matches the new
suffix after its actual input substitution. No receipt field is dropped.

The initializer is called ONCE at151-152. Its SAME fields/cache/value/heap
and literal build equation supply Receipt, conjunction Fields, Context,
Facts/Available, ProgramValue, growth/issued extension, physical guard
origins, empty identity/EqReady, closedness/Original, ValueFields and exact
handle lookup plus initial ProgramSlots. All remain in the final tuple.
There is no independently chosen build, caller, source expression or heap.

initial_packet_carriers at161 uses THAT Context/value and emptyPending.
Its encoded handle is identified with THAT initializer handle at164-165.
The whole Packet/canonical/pending-zero/mass-zero/waiting/candidate-index
and graph/reference carrier receipt remains. No initialized Packet is
supplied by a caller. The initial Program mark is literally uv=0.

Fits at166 uses the SAME heap profile and initial mass theorem; Heap at168
uses THAT Facts. Reservation at170-172 is derived by the checked original-
input enum_reserved_of_build law using returned and the SAME built receipt.
Width's deterministic build occurrence is identified by that equation;
it creates no independent initializer endpoint. No Room provider is input.

One actual ProgramOutputs producer is called at175-181 with these SAME
caller/inventory/globals/startup/value-derived mark/heap/seed and ceiling0.
Selection is literal nodeEdges with identity membership/length proofs.
The whole stable ALL-larger-fuel OutcomeResources receipt is retained.
Every emitted output retains its marks, ProgramSlots, metadata=None/done,
full Post/memos/Packet/Fits/Heap and original readback/model observers:
ALL read fuels, exact singleton, Frame/RenderStable/Stratified, conditional
Satisfies/Completes and the SAME Program for the partial and ALL completions.

New public inputs are only current source .ok identity, chosen depth,
metadata with empty pending, and ordinary formulas/solver/worker config.
No future state, model, Packet, role, fit, Room or capacity supplier appears.
This is an actual shallow enumeration run, not old completed-nodeCall output
under a new label. It proves no emitted-output or model existence, adequate
recursive depth, eager traversal or full default/Haskell correspondence.
Its mathematical enumBits is not a fixed-machine-width capacity theorem.
No source, compiler, repository, Git, Haskell or evidence action was run.
