import MicroCFTA.SourceSynthesisHereditaryChildTransport
import MicroCFTA.SourceSynthesisHereditaryClosedMemo
import MicroCFTA.SourceSynthesisNativeTypeCallerSteps
import MicroCFTA.SourceSynthesisHereditarySharedOuterEdgeWorker
import MicroCFTA.SourceCurrentSharedOuterInitialActual
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerGraph
import MicroCFTA.SourceCurrentMuReconstructionEffects
import MicroCFTA.MergedColdReaderClosed

/-!
# Recursive fields through actual shared outer traversal

The induction follows the literal successful shared worker. Each completed
prefix supplies the next Context, Frame and scheduled resource seed. One
initial phase Room supplies each reached Parent reservation. Returned row
schemas classify the actual child vector. Cold publication retains the
same body's full fields and closedness at its captured owner.

The public graph, canonical reads and full Post come from one package at
the same actual endpoint. The field proof does not change the canonical
read schedule to the observed lower fuels. Current Type state, guard
profile, closed classified inputs and conditional warm history remain
premises. This proof does not establish failed-prefix fields, completion,
native word capacity or Haskell driver correspondence.
-/
namespace MicroCFTA.SourceSynthesisHereditarySharedOuterTraversal
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceSynthesisHereditaryMemoFields (TypeRow)
open SourceSynthesisHereditaryClosedMemo (NodeFields EdgeFields History)
open SourceSynthesisHereditaryChildTransport (ChildMap)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List SourceSynthesisGeneralizeSyntax.Guard × Profile
namespace Schedule
export SourceCurrentSharedOuterInitialSchedule
  (parent rebuild node body rows descendants children walk parent_ge rebuild_ge node_ge body_ge
    rows_ge descendants_ge children_ge walk_ge parent_reserved)
end Schedule
open SourceCurrentAllocatedSharedPartialWorkerStability (bind_done_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "descend" => SourceCurrentAllocatedSharedPartialGraph.descend
local notation "prefixState" => SourceCurrentAllocatedSharedPartialGraph.prefixState
local notation "ProgramRow" => SourceSynthesisHereditaryProgramFields.EdgeFields
variable {width bits : Nat} {lib : Library} {literal : String → Symbol}

private structure Stable (lib : Library) (literal : String → Symbol) (state : Caller width) : Prop where
  typed : SharedReady lib (initialShared state.checked state.merge)
  guards : GuardHeap (Origin lib) state.checked.native.machine.heap
  history : History lib literal state

private def Classified (lib : Library) (literal : String → Symbol) (value : Node) : Prop :=
  Annotated (Origin lib) value ∨ ValueFields (Origin lib) literal value

private def RowClassified (lib : Library) (literal : String → Symbol) (row : Edge) : Prop :=
  TypeRow lib row ∨ ProgramRow (Origin lib) literal row

private def RowMap (lib : Library) (literal : String → Symbol) (input output : Edge) : Prop :=
  (TypeRow lib input → TypeRow lib output) ∧
    (ProgramRow (Origin lib) literal input → ProgramRow (Origin lib) literal output)

private theorem children_classified {row : Edge} (classified : RowClassified lib literal row) :
    ∀ child ∈ row.children, Classified lib literal child := by
  rcases classified with typed | fields
  · exact fun child member => Or.inl (typed.2 child member)
  · cases fields with
    | annotated source annotation guard children typed =>
        intro child member
        rw [children] at member
        cases List.mem_singleton.mp member
        exact Or.inl typed
    | application source types marker function argument symbol guard children typesTyped markerTyped functionFields argumentFields =>
        intro child member
        rw [children] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact Or.inl typesTyped
        · exact Or.inl markerTyped
        · exact Or.inr functionFields
        · exact Or.inr argumentFields
    | filter source goal candidates symbol guard children goalTyped candidateFields =>
        intro child member
        rw [children] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact Or.inl goalTyped
        · cases List.mem_singleton.mp member
          exact Or.inr candidateFields

private theorem rows_typed {inputs outputs : List Edge}
    (aligned : All₂ (RowMap lib literal) inputs outputs)
    (typed : ∀ row ∈ inputs, TypeRow lib row) : ∀ row ∈ outputs, TypeRow lib row := by
  induction aligned with
  | nil => intro row member; cases member
  | cons first rest ih =>
      intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact first.1 (typed _ List.mem_cons_self)
      · exact ih (fun row included => typed row (List.mem_cons_of_mem _ included)) row member

private theorem rows_program {inputs outputs : List Edge}
    (aligned : All₂ (RowMap lib literal) inputs outputs)
    (fields : ∀ row ∈ inputs, ProgramRow (Origin lib) literal row) :
    ∀ row ∈ outputs, ProgramRow (Origin lib) literal row := by
  induction aligned with
  | nil => intro row member; cases member
  | cons first rest ih =>
      intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact first.2 (fields _ List.mem_cons_self)
      · exact ih (fun row included => fields row (List.mem_cons_of_mem _ included)) row member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable (lib : Library) (literal : String → Symbol)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    Stable lib literal before →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    request.value.free = [] → Classified lib literal request.value →
    Room bits (Schedule.node fuel budget seed).2 →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    Stable lib literal after ∧ NodeFields lib literal request result

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    Stable lib literal before →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    request.value.free = [] → Classified lib literal request.value →
    Room bits (Schedule.body fuel budget seed).2 →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    Stable lib literal after ∧ NodeFields lib literal request result

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values results : List Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    Stable lib literal before →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    ClosedEdges values → (∀ row ∈ values, RowClassified lib literal row) →
    Room bits (Schedule.rows fuel budget seed).2 →
    rows fuel g s r e p h m c n budget inherited values before = .done results after →
    Stable lib literal after ∧ ClosedEdges results ∧ All₂ (RowMap lib literal) values results

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    Stable lib literal before →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    ClosedValues value.children → RowClassified lib literal value →
    Room bits (Schedule.descendants fuel budget seed).2 →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    Stable lib literal after ∧ EdgeFields lib literal ⟨inherited, value⟩ result

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    Stable lib literal before →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    ClosedValues values → (∀ value ∈ values, Classified lib literal value) →
    Room bits (Schedule.children fuel budget seed).2 →
    children fuel g s r e p h m c n budget combined values before = .done results after →
    Stable lib literal after ∧ ClosedValues results ∧ All₂ (ChildMap (Origin lib) literal) values results

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    Stable lib literal before →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    ClosedValues values → (∀ value ∈ values, Classified lib literal value) →
    Room bits (Schedule.walk fuel budget seed).2 →
    walk fuel g s r e p h m c n budget combined index values before = .done results after →
    Stable lib literal after ∧ ClosedValues results ∧ All₂ (ChildMap (Origin lib) literal) values results

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt lib literal formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt lib literal formulas solver (bits := bits) smaller) :
    WalkAt lib literal formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined index values results before after inventory memos seed
    initial frame fits known stable inherited available closed classified room done
  cases values with
  | nil =>
      simp only [walk] at done
      cases done
      refine ⟨stable, ?_, .nil⟩
      intro item member
      cases member
  | cons value rest =>
      cases fuel with
      | zero => simp only [walk] at done; cases done
      | succ fuel =>
          rw [Schedule.walk] at room
          simp only [walk] at done
          obtain ⟨headValue, middle, first, remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨restValues, finalState, tail, last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          obtain ⟨descentReceipt, descentFrame, descentFits, descentPost⟩ :=
            SourceCurrentInheritedNumeric.descent formulas solver inventory before memos combined index
              initial frame seed.2 fits inherited
          obtain ⟨_typedDescent, _typedPost, descentReady, descentGuards, _⟩ :=
            SourceSynthesisNativeTypeCallerSteps.descent lib literal formulas solver inventory before memos
              initial stable.typed stable.guards stable.history.fields combined index inherited
          have descentHistory : History lib literal (descend before combined index).2 :=
            SourceSynthesisHereditaryClosedMemo.advance stable.history _ _ _
          have descentStable : Stable lib literal (descend before combined index).2 :=
            ⟨descentReady, descentGuards, descentHistory⟩
          have headAvailable := descentPost.effects.keeps.available _ (available value List.mem_cons_self)
          have nodeRoom : Room bits (Schedule.node fuel budget seed).2 :=
            room.mono (Schedule.walk_ge fuel budget (Schedule.node fuel budget seed)).1
          obtain ⟨headStable, headFields⟩ := nodes fuel (Nat.lt_succ_self _)
            (request := ⟨(descend before combined index).1, value⟩) seed
            descentPost.context descentFrame descentFits known descentStable descentReceipt.inherited headAvailable
            (closed value List.mem_cons_self) (classified value List.mem_cons_self) nodeRoom first
          obtain ⟨headInventory, headMemos, _headGraph, _headReads, headPost, headFrame,
              headFits, headKnown, _headAvailable, _headLaw⟩ :=
            SourceCurrentSharedOuterInitialActual.node_call formulas solver fuel
              (request := ⟨(descend before combined index).1, value⟩) seed
              descentPost.context descentFrame descentFits known descentReceipt.inherited headAvailable nodeRoom first
          have firstPost := descentPost.trans headPost
          have tailAvailable : Values middle.checked.native.machine.heap rest :=
            fun child member => firstPost.effects.keeps.available _ (available child (List.mem_cons_of_mem _ member))
          obtain ⟨tailStable, tailClosed, tailFields⟩ := tails fuel (Nat.lt_succ_self _)
            (Schedule.node fuel budget seed) headPost.context headFrame headFits headKnown headStable
            (inherited.grows firstPost.effects.grows.constraint_growth) tailAvailable
            (fun child member => closed child (List.mem_cons_of_mem _ member))
            (fun child member => classified child (List.mem_cons_of_mem _ member)) room tail
          refine ⟨tailStable, ?_, .cons ⟨headFields.typed, headFields.program⟩ tailFields⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact headFields.closed (closed value List.mem_cons_self)
          · exact tailClosed child member

private theorem children_step (fuel : Nat) (walks : WalkAt lib literal formulas solver (bits := bits) fuel) :
    ChildrenAt lib literal formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined values results before after inventory memos seed
    initial frame fits known stable inherited available closed classified room done
  cases combined with
  | contradiction =>
      simp only [SourceCurrentAllocatedSharedPartialWorker.children] at done
      cases done
      refine ⟨stable, ?_, SourceSynthesisHereditaryChildTransport.erased (Origin lib) literal values⟩
      intro value member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      rfl
  | live identity records =>
      simp only [SourceCurrentAllocatedSharedPartialWorker.children] at done
      exact walks seed initial frame fits known stable inherited available closed classified
        (by simpa only [Schedule.children] using room) done

private theorem descendants_step (fuel : Nat) (child : ChildrenAt lib literal formulas solver (bits := bits) fuel) :
    DescendantsAt lib literal formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited value result before after inventory memos seed
    initial frame fits known stable inheritedReady resident closed classified room done
  rw [Schedule.descendants] at room
  cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [descendants, observed] at done; cases done
      | ok answer =>
          cases answer with
          | none => simp only [descendants, observed] at done; cases done
          | some combined =>
              have prefixSame : prefixState before value inherited =
                  advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                    ⟨before.checked.native.machine.heap, operations⟩) before.fourth before.merge := by
                simp only [SourceCurrentAllocatedSharedPartialGraph.prefixState, SourceCurrentAllocatedInheritedPrefix.state, observed]
              simp only [descendants, observed] at done
              rw [← prefixSame] at done
              obtain ⟨values, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              have combinedEquation : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited
                  before.checked.operations).1 = .ok (some combined) := by rw [observed]
              obtain ⟨actualCombined, prefixReceipt, prefixFrame, prefixFits, prefixPost⟩ :=
                SourceCurrentInheritedNumeric.resident_complete formulas solver inventory value inherited before memos
                  initial frame seed.2 fits (fun _ => resident) (fun _ => inheritedReady)
              have same := Option.some.inj (Except.ok.inj (prefixReceipt.actual.symm.trans combinedEquation))
              cases same
              obtain ⟨_typedCombined, _typedPrefix, _typedPost, prefixReady, prefixGuards, _⟩ :=
                SourceSynthesisNativeTypeCallerSteps.inherited_prefix lib literal formulas solver inventory before memos
                  initial stable.typed stable.guards stable.history.fields value inherited resident inheritedReady
              have prefixStable : Stable lib literal (prefixState before value inherited) :=
                ⟨prefixReady, prefixGuards, SourceSynthesisHereditaryClosedMemo.advance stable.history _ _ _⟩
              have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges value.entry.key value resident
              have childInputs : Values (prefixState before value inherited).checked.native.machine.heap value.children :=
                fun item member => prefixPost.effects.keeps.available _ (inputs item member)
              have childRoom : Room bits (Schedule.children fuel budget seed).2 :=
                room.mono (Schedule.rebuild_ge (Schedule.children fuel budget seed)).1
              obtain ⟨middleStable, middleClosed, aligned⟩ := child seed prefixPost.context prefixFrame prefixFits known
                prefixStable prefixReceipt.combinedReady childInputs closed (children_classified classified) childRoom first
              obtain ⟨childInventory, final, _graph, _reads, childPost, _childFrame,
                  _childFits, _childKnown, returned, _law⟩ :=
                SourceCurrentSharedOuterInitialActual.children formulas solver fuel seed prefixPost.context
                  prefixFrame prefixFits known prefixReceipt.combinedReady childInputs childRoom first
              have firstPost := prefixPost.trans childPost
              have originalResident := InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _ resident
              obtain ⟨receipt, _post, nextReady, nextGuards, _⟩ := SourceSynthesisNativeTypeCallerSteps.raw_edge
                lib literal formulas solver childInventory middle final childPost.context middleStable.typed
                middleStable.guards middleStable.history.fields value values originalResident returned aligned.length_eq.symm
              have facts := childPost.context.ready.semantic.ready.semantic.1.normal.facts
              have resultClosed : ClosedValues (SourceCurrentAllocatedRawRebuild.edge value values middle.checked).1.children := by
                rw [receipt.children]
                exact middleClosed
              refine ⟨⟨nextReady, nextGuards, SourceSynthesisHereditaryClosedMemo.advance middleStable.history _ _ _⟩,
                ⟨⟨?_, ?_⟩, fun _ => resultClosed⟩⟩
              · intro typed
                exact SourceSynthesisHereditaryChildTransport.raw_typed_edge (Origin lib) literal value values
                  middle.checked facts returned typed aligned
              · intro fields
                exact SourceSynthesisHereditaryRawRebuild.edge (Origin lib) literal value values middle.checked facts returned
                  (SourceSynthesisHereditaryChildTransport.edge_fields (Origin lib) literal value values fields aligned)

private theorem rows_step (fuel : Nat)
    (descendantsAt : ∀ smaller, smaller < fuel → DescendantsAt lib literal formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt lib literal formulas solver (bits := bits) smaller) :
    RowsAt lib literal formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited values results before after inventory memos seed
    initial frame fits known stable inheritedReady resident closed classified room done
  cases values with
  | nil =>
      simp only [rows] at done
      cases done
      refine ⟨stable, ?_, .nil⟩
      intro item member
      cases member
  | cons original rest =>
      cases fuel with
      | zero => simp only [rows] at done; cases done
      | succ fuel =>
          rw [Schedule.rows] at room
          simp only [rows] at done
          obtain ⟨narrowed, middle, first, remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨edgeResult, current, second, remaining⟩ := (bind_done_iff _ _ _ _).mp remaining
          obtain ⟨restResults, finalState, tail, last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          let edgeSeed := Schedule.parent budget seed
          let childSeed := Schedule.descendants fuel budget edgeSeed
          have edgeRoom : Room bits edgeSeed.2 := room.mono
            ((Schedule.descendants_ge fuel budget edgeSeed).1.trans (Schedule.rows_ge fuel budget childSeed).1)
          obtain ⟨edgeInventory, edgeMemos, _edgeGraph, _edgeReads, _edgeReceipt, edgePost,
              edgeFrame, edgeFits, edgeKnown, narrowedResident, _edgeLaw, edgeHistory,
              edgeFields, edgeReady, _edgeExtension, edgeClosed, edgeGuards⟩ :=
            SourceSynthesisHereditarySharedOuterEdgeWorker.edgeCall_verified_fields
              (lib := lib) (literal := literal) (request := ⟨inherited, original⟩) initial frame fits known
              (Schedule.parent_reserved bits budget seed edgeRoom) stable.typed stable.guards
              ⟨inheritedReady, resident original List.mem_cons_self⟩
              (closed original List.mem_cons_self) (classified original List.mem_cons_self) stable.history first
          have narrowedClassified : RowClassified lib literal narrowed := by
            rcases classified original List.mem_cons_self with typed | fields
            · exact Or.inl (edgeFields.typed typed)
            · exact Or.inr (edgeFields.program fields)
          have childRoom : Room bits childSeed.2 := room.mono (Schedule.rows_ge fuel budget childSeed).1
          obtain ⟨childStable, childFields⟩ := descendantsAt fuel (Nat.lt_succ_self _) edgeSeed
            edgePost.context edgeFrame edgeFits edgeKnown ⟨edgeReady, edgeGuards, edgeHistory⟩
            (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident edgeClosed
            narrowedClassified childRoom second
          obtain ⟨childInventory, childMemos, _childGraph, _childReads, childPost,
              childFrame, childFits, childKnown, _resultResident, _childLaw⟩ :=
            SourceCurrentSharedOuterInitialActual.descendants formulas solver fuel edgeSeed edgePost.context
              edgeFrame edgeFits edgeKnown (inheritedReady.grows edgePost.effects.grows.constraint_growth)
              narrowedResident childRoom second
          have firstPost := edgePost.trans childPost
          have tailResident : Edges current.checked.native.machine.heap rest :=
            fun row member => InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _
              (resident row (List.mem_cons_of_mem _ member))
          obtain ⟨tailStable, tailClosed, tailFields⟩ := tails fuel (Nat.lt_succ_self _) childSeed
            childPost.context childFrame childFits childKnown childStable
            (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident
            (fun row member => closed row (List.mem_cons_of_mem _ member))
            (fun row member => classified row (List.mem_cons_of_mem _ member)) room tail
          refine ⟨tailStable, ?_, .cons ⟨fun typed => childFields.typed (edgeFields.typed typed),
            fun fields => childFields.program (edgeFields.program fields)⟩ tailFields⟩
          intro row member
          rcases List.mem_cons.mp member with rfl | member
          · exact childFields.closed edgeClosed
          · exact tailClosed row member

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt lib literal formulas solver (bits := bits) smaller) :
    NodeBodyAt lib literal formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos seed
    initial frame fits known stable inherited available closed classified room done
  cases request with
  | mk inheritedValue value =>
      cases value with
      | empty =>
          simp only [nodeBody] at done
          cases done
          exact ⟨stable, ⟨⟨id, id⟩, id⟩⟩
      | union entry members depth free =>
          simp only [nodeBody] at done
          cases done
          exact ⟨stable, ⟨⟨id, id⟩, id⟩⟩
      | reference name => simp only [nodeBody] at done; cases done
      | mu entry body depth ordinary =>
          cases observed : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
          | pending => simp only [nodeBody, observed] at done; cases done
          | done value heap =>
              have completed := SourceCurrentMuReconstructionEffects.complete entry body depth ordinary
                before.checked.native.machine.heap initial.ready.semantic.ready.semantic.1.normal.facts.coherent
                initial.probes available
              obtain ⟨sameResult, sameHeap⟩ := InternedNestedConstruction.Outcome.done.inj
                (observed.symm.trans completed.1)
              subst value
              subst heap
              simp only [nodeBody, observed] at done
              cases done
              have sameCaller : advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                  ⟨before.checked.native.machine.heap, before.checked.operations⟩) before.fourth before.merge = before := rfl
              rw [sameCaller]
              refine ⟨stable, ⟨⟨?_, ?_⟩, ?_⟩⟩
              · intro typed
                change Annotated (Origin lib) (InternedNestedConstruction.finish true (.mu entry body depth ordinary))
                exact SourceCurrentHereditaryConstruction.finish_annotated (Origin lib) true _ typed
              · intro fields
                cases fields
              · intro inputClosed
                exact (InternedNormalizationFree.cleanup_free _).trans inputClosed
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at done; cases done
          | succ fuel =>
              rw [Schedule.body] at room
              simp only [nodeBody] at done
              obtain ⟨results, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              have edges := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _
                available.resident
              have originalClosed := MergedColdReaderClosed.node_children_closed before.checked.native.machine.heap
                initial.ready.semantic.ready.semantic.1.normal.facts entry original depth free available closed
              have rowClassified : ∀ row ∈ original, RowClassified lib literal row := by
                rcases classified with typed | fields
                · intro row member
                  exact Or.inl (SourceCurrentHereditaryConstructors.node_edge typed row member)
                · cases fields with
                  | node _ _ _ _ checked => exact fun row member => Or.inr (checked row member)
              have rowsRoom : Room bits (Schedule.rows fuel budget seed).2 :=
                room.mono (Schedule.rebuild_ge (Schedule.rows fuel budget seed)).1
              obtain ⟨middleStable, middleClosed, aligned⟩ := rowCalls fuel (Nat.lt_succ_self _) seed
                initial frame fits known stable inherited edges originalClosed rowClassified rowsRoom first
              obtain ⟨rowInventory, final, _graph, _reads, rowPost, _rowFrame,
                  _rowFits, _rowKnown, resident, _rowLaw⟩ :=
                SourceCurrentSharedOuterInitialActual.rows formulas solver fuel seed initial frame fits known inherited edges rowsRoom first
              have originalAvailable := rowPost.effects.keeps.available _ available
              obtain ⟨_receipt, _post, nextReady, nextGuards, _⟩ := SourceSynthesisNativeTypeCallerSteps.raw_modify
                lib literal formulas solver rowInventory middle final rowPost.context middleStable.typed
                middleStable.guards middleStable.history.fields entry original results depth free
                originalAvailable resident middleClosed
              have facts := rowPost.context.ready.semantic.ready.semantic.1.normal.facts
              have returnedClosed : (SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free)
                  original results middle.checked).1.free = [] := by
                by_cases same : results.map (fun row => row.entry.identity) = original.map (fun row => row.entry.identity)
                · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
                  exact closed
                · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte] using
                    MergedColdReaderClosedInputs.makeNode_closed results middle.checked.native.machine.heap facts resident middleClosed
              refine ⟨⟨nextReady, nextGuards, SourceSynthesisHereditaryClosedMemo.advance middleStable.history _ _ _⟩,
                ⟨⟨?_, ?_⟩, fun _ => returnedClosed⟩⟩
              · intro typed
                apply SourceSynthesisHereditaryChildTransport.raw_typed_modify (Origin lib) _ original results middle.checked
                  facts resident typed
                exact rows_typed aligned (fun row member => SourceCurrentHereditaryConstructors.node_edge typed row member)
              · intro fields
                apply SourceSynthesisHereditaryRawRebuild.modify (Origin lib) literal _ original results middle.checked
                  facts resident fields
                apply rows_program aligned
                cases fields with
                | node _ _ _ _ checked => exact checked

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem context_good {inventory : Inventory} {before : Caller width} {memos : Memos}
    (initial : Context formulas solver inventory before memos) : SourceCurrentOuterPrefixInvariants.Good before := by
  refine ⟨SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.ready.good)
    initial.ready.semantic initial.ready.costs, initial.stored, initial.probes, ?_, ?_⟩
  · refine ⟨initial.sound.valid.nodes.bounded, ?_, ?_⟩
    · intro key handle found
      obtain ⟨cell, present, linked⟩ := initial.sound.valid.nodes.linked key handle found
      exact ⟨cell, present, linked.2⟩
    · intro handle cell present
      have own := initial.sound.nodes handle cell present
      exact ⟨⟨own.inherited, own.input⟩, fun value returned => (own.returned value returned).1⟩
  · refine ⟨initial.sound.valid.edges.bounded, ?_, ?_⟩
    · intro key handle found
      obtain ⟨cell, present, linked⟩ := initial.sound.valid.edges.linked key handle found
      exact ⟨cell, present, linked.2⟩
    · intro handle cell present
      have own := initial.sound.edges handle cell present
      exact ⟨⟨own.inherited, own.input⟩, fun value returned => (own.returned value returned).1⟩

private theorem nodeCall_step (fuel : Nat) (body : NodeBodyAt lib literal formulas solver (bits := bits) fuel) :
    NodeCallAt lib literal formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos seed
    initial frame fits known stable inherited available closed classified room done
  rcases started : beginNode request before with ⟨handle, action, running⟩
  cases action with
  | ready value =>
      simp only [nodeCall, started] at done
      cases done
      obtain ⟨same, fields⟩ := SourceSynthesisHereditaryClosedMemo.node_ready stable.history
        (context_good formulas solver initial) ⟨inherited, available⟩ started
      cases same
      exact ⟨stable, fields⟩
  | evaluate original =>
      simp only [nodeCall, started] at done
      obtain ⟨value, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp done
      cases last
      obtain ⟨runningContext, owner, key, cell⟩ :=
        SourceCurrentAllocatedSharedPartialCallSteps.node_start formulas solver initial inherited available started
      have components := beginNode_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checkedSame, mergeSame, fourthSame, _⟩ := components
      have ownerSame : original = request := SourceCurrentOuterPrefixInvariants.same_key
        (context_good formulas solver runningContext) ⟨owner.inherited, owner.input⟩
        (by simpa only [SourceCurrentOuterPrefixInvariants.NodeReady, checkedSame] using And.intro inherited available) key
      have runningStable : Stable lib literal running := by
        have history := SourceSynthesisHereditaryClosedMemo.beginNode stable.history request
        rw [started] at history
        refine ⟨?_, ?_, history⟩
        · simpa only [checkedSame, mergeSame] using stable.typed
        · simpa only [checkedSame] using stable.guards
      have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checkedSame] using frame
      have runningFits : Fits seed.2 running.checked := by simpa only [checkedSame] using fits
      have runningKnown : Carrier (fun guard => guard ∈ seed.1) running.checked.native.machine.heap := by
        simpa only [checkedSame] using known
      have bodyRoom : Room bits (Schedule.body fuel budget seed).2 := by simpa only [Schedule.node] using room
      obtain ⟨middleStable, fields⟩ := body seed runningContext runningFrame runningFits runningKnown runningStable
        owner.inherited owner.input (by simpa only [ownerSame] using closed)
        (by simpa only [ownerSame] using classified) bodyRoom first
      have bodyFrame := SourceCurrentAllocatedSharedPartialWorkerGraph.nodeBody_frame first
        (SourceCurrentAllocatedSharedPartialFrames.Protocol.of_valid runningContext.sound.valid)
      have runningCell := bodyFrame.node_running handle original cell
      have published := SourceSynthesisHereditaryClosedMemo.finishNode middleStable.history runningCell fields
      refine ⟨⟨middleStable.typed, middleStable.guards, published⟩, ?_⟩
      simpa only [ownerSame] using fields
  | busy | absent => simp only [nodeCall, started] at done; cases done

private theorem all_fields (fuel : Nat) :
    NodeCallAt lib literal formulas solver (bits := bits) fuel ∧ NodeBodyAt lib literal formulas solver (bits := bits) fuel ∧
    RowsAt lib literal formulas solver (bits := bits) fuel ∧ DescendantsAt lib literal formulas solver (bits := bits) fuel ∧
    ChildrenAt lib literal formulas solver (bits := bits) fuel ∧ WalkAt lib literal formulas solver (bits := bits) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walks : WalkAt lib literal formulas solver (bits := bits) fuel :=
        walk_step lib literal formulas solver fuel (fun smaller less => (ih smaller less).1)
          (fun smaller less => (ih smaller less).2.2.2.2.2)
      have child : ChildrenAt lib literal formulas solver (bits := bits) fuel :=
        children_step lib literal formulas solver fuel walks
      have descendants : DescendantsAt lib literal formulas solver (bits := bits) fuel :=
        descendants_step lib literal formulas solver fuel child
      have rows : RowsAt lib literal formulas solver (bits := bits) fuel :=
        rows_step lib literal formulas solver fuel (fun smaller less => (ih smaller less).2.2.2.1)
          (fun smaller less => (ih smaller less).2.2.1)
      have body : NodeBodyAt lib literal formulas solver (bits := bits) fuel :=
        nodeBody_step lib literal formulas solver fuel (fun smaller less => (ih smaller less).2.2.1)
      exact ⟨nodeCall_step lib literal formulas solver fuel body, body, rows, descendants, child, walks⟩

/-- One actual shared return retains its canonical reads and both complete field families. -/
theorem nodeCall_fields
    {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller (bits+2)} {result : Node} {inventory : Inventory} {memos : Memos}
    (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (typedState : SharedReady lib (initialShared before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (history : History lib literal before)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (closed : request.value.free = [])
    (classified : Annotated (Origin lib) request.value ∨ ValueFields (Origin lib) literal request.value)
    (room : Room bits (Schedule.node fuel budget seed).2)
    (done : nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.NodeCall budget request before result after,
      SourceCurrentAllocatedSharedPartialEndpointReads.NodeCallReads formulas solver graph memos final ∧
      Post formulas solver next before after final ∧ Frame formulas solver next after.checked ∧
      Fits (Schedule.node fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.node fuel budget seed).1) after.checked.native.machine.heap ∧
      Available after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧
      SharedReady lib (initialShared after.checked after.merge) ∧
      GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after ∧
      result.free = [] ∧ NodeFields lib literal request result := by
  obtain ⟨retained, fields⟩ := (all_fields lib literal formulas solver fuel).1 seed initial frame fits known
    ⟨typedState, guards, history⟩ inherited available closed classified room done
  obtain ⟨next, final, graph, reads, post, returnedFrame, returnedFits, returnedKnown, returned, law⟩ :=
    SourceCurrentSharedOuterInitialActual.node_call formulas solver fuel seed initial frame fits known inherited available room done
  exact ⟨next, final, graph, reads, post, returnedFrame, returnedFits, returnedKnown, returned, law,
    retained.typed, retained.guards, retained.history, fields.closed closed, fields⟩

end MicroCFTA.SourceSynthesisHereditarySharedOuterTraversal
