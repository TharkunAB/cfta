import MicroCFTA.SourceCurrentActualParentNativeStores
import MicroCFTA.SourceCurrentOuterInitialActual
import MicroCFTA.SourceCurrentUnionNormalOuter
import MicroCFTA.SourceCurrentUnionNormalLocalParent
import MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion
import MicroCFTA.InternedShallowHeap

/-!
# Native stores through completed outer calls

The actual completed siblings supply their existing resource receipts.
The same returned callers retain native support and causal publication history.
Both Merge laws follow the actual Parent and constructor order.
-/
namespace MicroCFTA.SourceCurrentOuterNativeStores
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedPartialWorkerStability (bind_done_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeSupport" => SourceCurrentNativeRequestPositivePositions.Support
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "MergeSupport" => SourceCurrentMergePositivePosition.Support
local notation "Normal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "History" => SourceCurrentNativeMuPublication.History
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
namespace Schedule
export SourceCurrentOuterInitialSchedule
  (parent node body rows descendants children walk parent_reserved rows_ge descendants_ge walk_ge rebuild_ge)
end Schedule
variable {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def Stores [DecidableEq (EdgeKey Symbol Guard)] (state : Caller (bits+2)) : Prop :=
  NativeSupport state.checked.native.machine.heap state.checked.native ∧
    Nonempty (History empty state.checked.native.machine.heap) ∧
    MergeStored state.merge ∧ MergeSupport state.merge ∧ Normal state.checked.native.machine.heap

private theorem retained [DecidableEq (EdgeKey Symbol Guard)] {before after : Checked (bits+2)} {inventory : Inventory}
    (frame : Frame formulas solver inventory before)
    (supported : NativeSupport before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good after)
    (extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine)
    (nodes : after.native.nodes = before.native.nodes) (edges : after.native.edges = before.native.edges)
    (old : InternedShallowHeap.NoNewMu before.native.machine.heap after.native.machine.heap) :
    NativeSupport after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) :=
  ⟨SourceCurrentNativePositiveSupportAdvance.advance before after
    (SourceCurrentConstrainedCapOperandFrame.current frame) supported good extension nodes edges,
    ⟨.trans causal (.retain _ _ old)⟩⟩

private theorem reservation [DecidableEq (EdgeKey Symbol Guard)]
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest}
    {before : Caller (bits+2)} {memos : Memos} {profile : Profile} {alphabet : List Guard}
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentParentAlphabetReservation.UniformReserved bits budget alphabet profile) :
    SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile := by
  generalize started : beginEdge request before = observation
  obtain ⟨handle,action,running⟩ := observation
  cases action with
  | evaluate captured =>
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have checked := (beginEdge_components request before).1
      rw [started] at checked
      dsimp only at checked
      have bounded : Fits profile running.checked := by simpa only [checked] using fits
      have carrier : Carrier (fun guard => guard ∈ alphabet) running.checked.native.machine.heap := by simpa only [checked] using known
      have room := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet captured
        running memos runningContext profile bounded carrier owner.inherited owner.input uniform
      simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using room
  | ready | busy | absent => simp only [SourceCurrentEdgeCallNumeric.Reserved,started]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem edge_stores
    {inventory next : Inventory} {budget : Nat} {request : EdgeRequest}
    {before after : Caller (bits+2)} {memos final : Memos} {profile : Profile} {result : Edge}
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (reserved : SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile)
    (receipt : SourceCurrentEdgeCallNumeric.Receipt formulas solver next profile budget request before memos result after final)
    (stored : Stores before) : Stores after := by
  have actual := receipt.actual
  cases actual with
  | hit started =>
      have same := (SourceCurrentEdgeCallNumeric.ready formulas solver inventory budget request before memos
        initial frame profile fits inherited resident started).1
      subst after
      exact stored
  | evaluate started body =>
      rename_i handle running captured middle
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked,merge,_fourth,_nodes⟩ := components
      have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
      have runningFits : Fits profile running.checked := by simpa only [checked] using fits
      have runningStores : Stores running := by simpa only [Stores,checked,merge] using stored
      have reservation : SourceCurrentParentForecast.residentReserved bits budget captured running.checked profile := by
        simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using reserved
      cases body with
      | parent field parent =>
          rename_i loaded inheritedValue returned fourth memo sourceEdge
          let captured : EdgeRequest := ⟨inheritedValue,sourceEdge⟩
          have live : SourceCurrentParentNumeric.LiveInputs captured.value.entry.key.constraint loaded
              captured.inherited captured.value.children running := by
            intro test
            obtain ⟨cached,_loaded,_found⟩ := runningContext.ready.good.fields captured.value.entry.key captured.value owner.input
            exact ⟨cached,field test,owner.inherited,
              runningContext.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ captured.value owner.input⟩
          have room : SourceCurrentParentForecast.Reserved bits budget captured.value.children.length
              captured.value.entry.key.constraint loaded captured.inherited running.checked profile := by
            cases test : SourceEqualityMkEdgeAllocation.contradictory captured.value.entry.key.constraint with
            | true => simp only [SourceCurrentParentForecast.Reserved,test,ite_true]
            | false =>
                simpa only [captured,SourceCurrentParentForecast.residentReserved,test,Bool.false_eq_true,ite_false,field test] using reservation
          obtain ⟨g,s,r,e,p,h,m,c,n,stable⟩ :=
            SourceCurrentAllocatedParentWorkerCompletion.edge_complete parent field
          have observed := stable g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
            (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
          dsimp only at observed
          obtain ⟨causal⟩ := runningStores.2.1
          obtain ⟨_next,_final,_numeric,supported,history,merged,positive⟩ :=
            SourceCurrentActualParentNativeStores.parent formulas solver inventory budget captured.value.entry.key.symbol
              captured.value.entry.key.constraint loaded captured.inherited captured.value.children running memos
              runningContext runningFrame profile runningFits live room runningStores.2.2.2.2
              runningStores.1 causal runningStores.2.2.1 runningStores.2.2.2.1 observed
          have normal := SourceCurrentUnionNormalLocalParent.parent g s r e p h m c n budget
            captured.value.entry.key.symbol captured.value.entry.key.constraint captured.inherited captured.value.children
            running.checked running.fourth running.merge runningStores.2.2.2.2
          rw [observed] at normal
          exact ⟨supported,history,merged,positive,normal⟩

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.node fuel budget seed).2 →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    Stores before → Stores after

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.body fuel budget seed).2 →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    Stores before → Stores after

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values results : List Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Room bits (Schedule.rows fuel budget seed).2 →
    rows fuel g s r e p h m c n budget inherited values before = .done results after →
    Stores before → Stores after

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    Room bits (Schedule.descendants fuel budget seed).2 →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    Stores before → Stores after

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.children fuel budget seed).2 →
    SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n budget combined values before = .done results after →
    Stores before → Stores after

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.walk fuel budget seed).2 →
    walk fuel g s r e p h m c n budget combined index values before = .done results after →
    Stores before → Stores after

private theorem nodeCall_step (fuel : Nat) (bodyAt : NodeBodyAt formulas solver (bits := bits) fuel) :
    NodeCallAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos seed
    initial frame fits known inherited available room done stored
  rcases started : beginNode request before with ⟨handle,action,running⟩
  cases action with
  | ready value =>
      simp only [nodeCall,started] at done
      have hit := SourceCurrentAllocatedPartialMemoSound.beginNode_ready_sound formulas solver request before
        initial.sound initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited available handle value running started
      cases done
      rw [hit.1]
      exact stored
  | evaluate captured =>
      simp only [nodeCall,started] at done
      obtain ⟨value,middle,first,last⟩ := (bind_done_iff _ _ _ _).mp done
      cases last
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
      have components := beginNode_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked,merge,_fourth,_edges⟩ := components
      have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
      have runningFits : Fits seed.2 running.checked := by simpa only [checked] using fits
      have runningKnown : Carrier (fun guard => guard ∈ seed.1) running.checked.native.machine.heap := by simpa only [checked] using known
      have runningStores : Stores running := by simpa only [Stores,checked,merge] using stored
      have bodyRoom : Room bits (Schedule.body fuel budget seed).2 := by simpa only [Schedule.node] using room
      exact bodyAt (after := middle) seed runningContext runningFrame runningFits runningKnown owner.inherited owner.input bodyRoom first runningStores
  | busy | absent => simp only [nodeCall,started] at done; cases done

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt formulas solver (bits := bits) smaller) :
    WalkAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined index values results before after inventory memos seed
    initial frame fits known inherited available room done stored
  cases values with
  | nil => simp only [walk] at done; cases done; exact stored
  | cons value rest =>
      cases fuel with
      | zero => simp only [walk] at done; cases done
      | succ fuel =>
          rw [Schedule.walk] at room
          simp only [walk] at done
          obtain ⟨headValue,middle,first,remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨restValues,finalState,tail,last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          obtain ⟨descentReceipt,descentFrame,descentFits,descentPost⟩ := SourceCurrentInheritedNumeric.descent formulas solver
            inventory before memos combined index initial frame seed.2 fits inherited
          have nodeRoom : Room bits (Schedule.node fuel budget seed).2 :=
            room.mono (Schedule.walk_ge fuel budget (Schedule.node fuel budget seed)).1
          have headStores : Stores middle := nodes fuel (Nat.lt_succ_self _)
            (request := ⟨(descend before combined index).1,value⟩) (before := (descend before combined index).2)
            seed descentPost.context descentFrame descentFits known
            descentReceipt.inherited (descentPost.effects.keeps.available _ (available value List.mem_cons_self)) nodeRoom first stored
          obtain ⟨headInventory,headMemos,_graph,_reads,headPost,headFrame,headFits,headKnown,_available,_law⟩ :=
            SourceCurrentOuterInitialActual.node_call formulas solver fuel
              (request := ⟨(descend before combined index).1,value⟩) (before := (descend before combined index).2)
              seed descentPost.context descentFrame descentFits known
              descentReceipt.inherited (descentPost.effects.keeps.available _ (available value List.mem_cons_self)) nodeRoom first
          have firstPost := descentPost.trans headPost
          have tailAvailable : Values middle.checked.native.machine.heap rest := fun child member =>
            firstPost.effects.keeps.available _ (available child (List.mem_cons_of_mem _ member))
          exact tails fuel (Nat.lt_succ_self _) (Schedule.node fuel budget seed) headPost.context headFrame headFits headKnown
            (inherited.grows firstPost.effects.grows.constraint_growth) tailAvailable room tail headStores

private theorem children_step (fuel : Nat) (walks : WalkAt formulas solver (bits := bits) fuel) :
    ChildrenAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined values results before after inventory memos seed
    initial frame fits known inherited available room done stored
  cases combined with
  | contradiction =>
      simp only [SourceCurrentAllocatedPartialWorker.children] at done
      cases done
      exact stored
  | live identity records =>
      rw [Schedule.children] at room
      simp only [SourceCurrentAllocatedPartialWorker.children] at done
      exact walks seed initial frame fits known inherited available room done stored

private theorem descendants_step (fuel : Nat) (child : ChildrenAt formulas solver (bits := bits) fuel) :
    DescendantsAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited value result before after inventory memos seed
    initial frame fits known inheritedReady resident room done stored
  have normal := SourceCurrentUnionNormalOuter.descendant_pass fuel g s r e p h m c n budget inherited value before stored.2.2.2.2
  rw [done] at normal
  rw [Schedule.descendants] at room
  cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [descendants,observed] at done; cases done
      | ok answer =>
          cases answer with
          | none => simp only [descendants,observed] at done; cases done
          | some combined =>
              have prefixSame : prefixState before value inherited = advance before
                  (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨before.checked.native.machine.heap,operations⟩)
                  before.fourth before.merge := by simp only [prefixState,SourceCurrentAllocatedInheritedPrefix.state,observed]
              simp only [descendants,observed] at done
              rw [←prefixSame] at done
              obtain ⟨values,middle,first,last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              have combinedEquation : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited
                  before.checked.operations).1 = .ok (some combined) := by rw [observed]
              obtain ⟨chosen,prefixReceipt,prefixFrame,prefixFits,prefixPost⟩ :=
                SourceCurrentInheritedNumeric.resident_complete formulas solver inventory value inherited before memos
                  initial frame seed.2 fits (fun _ => resident) (fun _ => inheritedReady)
              have same := Option.some.inj (Except.ok.inj (prefixReceipt.actual.symm.trans combinedEquation))
              subst chosen
              have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges value.entry.key value resident
              have childInputs : Values (prefixState before value inherited).checked.native.machine.heap value.children :=
                fun item member => prefixPost.effects.keeps.available _ (inputs item member)
              have childRoom : Room bits (Schedule.children fuel budget seed).2 := room.mono (Schedule.rebuild_ge _).1
              have childStores := child seed prefixPost.context prefixFrame prefixFits known prefixReceipt.combinedReady
                childInputs childRoom first stored
              obtain ⟨next,final,graph,_reads,childPost,childFrame,_fits,_known,available,_law⟩ :=
                SourceCurrentOuterInitialActual.children formulas solver fuel seed prefixPost.context prefixFrame prefixFits known
                  prefixReceipt.combinedReady childInputs childRoom first
              have sourceResident := InternedEdgeResidency.edge_grows _ _ (prefixPost.trans childPost).effects.keeps.growth _ resident
              have raw := (SourceCurrentAllocatedPartialStepEffects.raw_edge formulas solver next middle final childPost.context
                value values sourceResident available graph.length).1
              obtain ⟨causal⟩ := childStores.2.1
              have old : InternedShallowHeap.NoNewMu middle.checked.native.machine.heap
                  (SourceCurrentAllocatedRawRebuild.edge value values middle.checked).2.native.machine.heap :=
                fun _ _ _ _ _ present => present
              obtain ⟨supported,history⟩ := retained formulas solver childFrame childStores.1 causal
                raw.ready.good raw.extension raw.nodes raw.edges old
              exact ⟨supported,history,childStores.2.2.1,childStores.2.2.2.1,normal⟩

private theorem rows_step (fuel : Nat)
    (descendAt : ∀ smaller, smaller < fuel → DescendantsAt formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt formulas solver (bits := bits) smaller) :
    RowsAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited values results before after inventory memos seed
    initial frame fits known inheritedReady resident room done stored
  cases values with
  | nil => simp only [rows] at done; cases done; exact stored
  | cons original rest =>
      cases fuel with
      | zero => simp only [rows] at done; cases done
      | succ fuel =>
          rw [Schedule.rows] at room
          simp only [rows] at done
          obtain ⟨narrowed,middle,first,remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨edgeResult,current,second,remaining⟩ := (bind_done_iff _ _ _ _).mp remaining
          obtain ⟨restResults,finalState,tail,last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          let edgeSeed := Schedule.parent budget seed
          let childSeed := Schedule.descendants fuel budget edgeSeed
          have edgeRoom : Room bits edgeSeed.2 := room.mono
            ((Schedule.descendants_ge fuel budget edgeSeed).1.trans (Schedule.rows_ge fuel budget childSeed).1)
          have uniform := Schedule.parent_reserved bits budget seed edgeRoom
          obtain ⟨edgeInventory,edgeMemos,edgeReceipt,edgeFits,edgeKnown⟩ :=
            SourceCurrentOuterEdgeGuardAlphabet.edge_call formulas solver inventory budget seed.1 ⟨inherited,original⟩
              before memos initial frame seed.2 fits known inheritedReady (resident original List.mem_cons_self) uniform first
          have reserved := reservation formulas solver (request := ⟨inherited,original⟩) initial fits known inheritedReady (resident original List.mem_cons_self) uniform
          have edgeStores := edge_stores formulas solver initial frame fits inheritedReady
            (resident original List.mem_cons_self) reserved edgeReceipt stored
          have childRoom : Room bits childSeed.2 := room.mono (Schedule.rows_ge fuel budget childSeed).1
          have childStores := descendAt fuel (Nat.lt_succ_self _) edgeSeed edgeReceipt.post.context edgeReceipt.frame edgeFits edgeKnown
            (inheritedReady.grows edgeReceipt.post.effects.grows.constraint_growth) edgeReceipt.semantic.resident childRoom second edgeStores
          obtain ⟨childInventory,childMemos,_graph,_reads,childPost,childFrame,childFits,childKnown,_resident,_law⟩ :=
            SourceCurrentOuterInitialActual.descendants formulas solver fuel edgeSeed edgeReceipt.post.context edgeReceipt.frame edgeFits edgeKnown
              (inheritedReady.grows edgeReceipt.post.effects.grows.constraint_growth) edgeReceipt.semantic.resident childRoom second
          have firstPost := edgeReceipt.post.trans childPost
          have tailResident : Edges current.checked.native.machine.heap rest := fun edge member =>
            InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _ (resident edge (List.mem_cons_of_mem _ member))
          exact tails fuel (Nat.lt_succ_self _) childSeed childPost.context childFrame childFits childKnown
            (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident room tail childStores

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt formulas solver (bits := bits) smaller) :
    NodeBodyAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos seed
    initial frame fits known inherited available room done stored
  have normal := SourceCurrentUnionNormalOuter.node_body fuel g s r e p h m c n budget request before stored.2.2.2.2
  rw [done] at normal
  cases request with
  | mk inheritedValue value =>
      cases value with
      | empty => simp only [nodeBody] at done; cases done; exact stored
      | union entry members depth free => simp only [nodeBody] at done; cases done; exact stored
      | reference name => simp only [nodeBody] at done; cases done
      | mu entry body depth ordinary =>
          have computed := SourceCurrentMuReconstructionEffects.complete entry body depth ordinary before.checked.native.machine.heap
            initial.ready.semantic.ready.semantic.1.normal.facts.coherent initial.probes available
          have unchanged : nodeBody fuel g s r e p h m c n budget ⟨inheritedValue,.mu entry body depth ordinary⟩ before =
              .done (cleanup (.mu entry body depth ordinary)) before := by
            simp only [nodeBody,computed.1]
            rfl
          have same := congrArg Outcome.state (done.symm.trans unchanged)
          change after = before at same
          subst after
          exact stored
      | node entry originals depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at done; cases done
          | succ fuel =>
              rw [Schedule.body] at room
              simp only [nodeBody] at done
              obtain ⟨results,middle,first,last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              have edges := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
              have rowsRoom : Room bits (Schedule.rows fuel budget seed).2 := room.mono (Schedule.rebuild_ge _).1
              have rowStores := rowCalls fuel (Nat.lt_succ_self _) seed initial frame fits known inherited edges rowsRoom first stored
              obtain ⟨next,final,_graph,_reads,rowPost,rowFrame,_fits,_known,rowsResident,_law⟩ :=
                SourceCurrentOuterInitialActual.rows formulas solver fuel seed initial frame fits known inherited edges rowsRoom first
              have sourceAvailable := rowPost.effects.keeps.available _ available
              have raw := (SourceCurrentAllocatedPartialStepEffects.modify formulas solver next middle final rowPost.context
                entry originals results depth free sourceAvailable rowsResident).1
              have old : InternedShallowHeap.NoNewMu middle.checked.native.machine.heap
                  (SourceCurrentAllocatedRawRebuild.modify (.node entry originals depth free) originals results middle.checked).2.native.machine.heap := by
                by_cases same : results.map (fun row => row.entry.identity) = originals.map (fun row => row.entry.identity)
                · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
                  exact InternedShallowHeap.noNewMu_refl _
                · simpa only [SourceCurrentAllocatedRawRebuild.modify,SourceEqualityPartialNodeRebuild.modify,same,↓reduceIte,
                    SourceEqualityNativeScoped.advanceHeap,SourceRecursiveIntersectionThunks.advance] using
                    InternedShallowHeap.makeNode_noNewMu results middle.checked.native.machine.heap
              obtain ⟨causal⟩ := rowStores.2.1
              obtain ⟨supported,history⟩ := retained formulas solver rowFrame rowStores.1 causal
                raw.ready.good raw.extension raw.nodes raw.edges old
              exact ⟨supported,history,rowStores.2.2.1,rowStores.2.2.2.1,normal⟩

private theorem all_stores (fuel : Nat) :
    NodeCallAt formulas solver (bits := bits) fuel ∧ NodeBodyAt formulas solver (bits := bits) fuel ∧
    RowsAt formulas solver (bits := bits) fuel ∧ DescendantsAt formulas solver (bits := bits) fuel ∧
    ChildrenAt formulas solver (bits := bits) fuel ∧ WalkAt formulas solver (bits := bits) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walks : WalkAt formulas solver (bits := bits) fuel := walk_step formulas solver fuel (fun smaller less => (ih smaller less).1) (fun smaller less => (ih smaller less).2.2.2.2.2)
      have child : ChildrenAt formulas solver (bits := bits) fuel := children_step formulas solver fuel walks
      have descendAt : DescendantsAt formulas solver (bits := bits) fuel := descendants_step formulas solver fuel child
      have rowsAt : RowsAt formulas solver (bits := bits) fuel := rows_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.2.1) (fun smaller less => (ih smaller less).2.2.1)
      have bodyAt : NodeBodyAt formulas solver (bits := bits) fuel := nodeBody_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.1)
      exact ⟨nodeCall_step formulas solver fuel bodyAt,bodyAt,rowsAt,descendAt,child,walks⟩

local notation "UnionNormal" => SourceCurrentRequiredUnionNormal.UnionNormal

/-- One fixed returned edge receipt retains all current store laws. -/
theorem edge_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory next : Inventory) (budget : Nat) (request : EdgeRequest)
    (before after : Caller (bits + 2)) (memos final : Memos) (profile : Profile) (result : Edge)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (reserved : SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile)
    (receipt : SourceCurrentEdgeCallNumeric.Receipt formulas solver next profile budget request before memos result after final)
    (normal : UnionNormal before.checked.native.machine.heap)
    (supported : NativeSupport before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap)
    (merged : MergeStored before.merge) (positiveMemo : MergeSupport before.merge) :
    NativeSupport after.checked.native.machine.heap after.checked.native ∧
      Nonempty (History empty after.checked.native.machine.heap) ∧
      MergeStored after.merge ∧ MergeSupport after.merge ∧ UnionNormal after.checked.native.machine.heap := by
  exact edge_stores formulas solver initial frame fits inherited resident reserved receipt
    ⟨supported,⟨causal⟩,merged,positiveMemo,normal⟩

/-- A completed node call retains stores through its actual completed siblings. -/
theorem node_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel : Nat) {g s r e p h m c n budget : Nat}
    {request : NodeRequest} {before after : Caller (bits + 2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (room : Room bits (SourceCurrentOuterInitialSchedule.node fuel budget seed).2)
    (normal : UnionNormal before.checked.native.machine.heap)
    (supported : NativeSupport before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap)
    (merged : MergeStored before.merge) (positiveMemo : MergeSupport before.merge)
    (observed : SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    NativeSupport after.checked.native.machine.heap after.checked.native ∧
      Nonempty (History empty after.checked.native.machine.heap) ∧
      MergeStored after.merge ∧ MergeSupport after.merge ∧ UnionNormal after.checked.native.machine.heap := by
  exact (all_stores formulas solver (bits := bits) fuel).1 seed initial frame fits known inherited available room observed
    ⟨supported,⟨causal⟩,merged,positiveMemo,normal⟩

/-- Actual completed descendants retain stores through the inherited prefix and raw rebuild. -/
theorem descendants
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (fuel : Nat) {g s r e p h m c n budget : Nat}
    {inherited : EqValue} {value result : Edge} {before after : Caller (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Resident before.checked.native.machine.heap value)
    (room : Room bits (SourceCurrentOuterInitialSchedule.descendants fuel budget seed).2)
    (normal : UnionNormal before.checked.native.machine.heap)
    (supported : NativeSupport before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap)
    (merged : MergeStored before.merge) (positiveMemo : MergeSupport before.merge)
    (observed : SourceCurrentAllocatedPartialWorker.descendants fuel g s r e p h m c n budget inherited value before = .done result after) :
    NativeSupport after.checked.native.machine.heap after.checked.native ∧
      Nonempty (History empty after.checked.native.machine.heap) ∧
      MergeStored after.merge ∧ MergeSupport after.merge ∧ UnionNormal after.checked.native.machine.heap := by
  exact (all_stores formulas solver (bits := bits) fuel).2.2.2.1 seed initial frame fits known inheritedReady resident room observed
    ⟨supported,⟨causal⟩,merged,positiveMemo,normal⟩

end MicroCFTA.SourceCurrentOuterNativeStores
