import MicroCFTA.SourceCurrentOuterInitialSchedule
import MicroCFTA.SourceCurrentOuterEdgeGuardAlphabet
import MicroCFTA.SourceCurrentOuterRebuildGuardAlphabet
import MicroCFTA.SourceCurrentAllocatedPartialActual
import MicroCFTA.SourceCurrentInheritedNumeric

/-!
# Initial resources at successful literal outer returns

The proof follows the actual successful bounded worker. Each smaller
return supplies its exact semantic law, caller Post, Frame and scheduled
resources before the next sibling starts. One initial final-profile Room
supplies each reached Parent reservation. No reached range or future
callee invariant is an input. General outer completion remains separate.
-/
namespace MicroCFTA.SourceCurrentOuterInitialActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialForestLanguage (RowsLaw)
open SourceCurrentAllocatedPartialWalkLanguage (ChildrenLaw WalkLaw)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialWorkerStability (bind_done_iff)
namespace Schedule
export SourceCurrentOuterInitialSchedule
  (parent rebuild node body rows descendants children walk parent_ge rebuild_ge node_ge body_ge
    rows_ge descendants_ge children_ge walk_ge parent_reserved)
end Schedule
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def Returned (seed : Seed) (inventory : Inventory) (before after : Caller (bits+2)) (final : Memos) : Prop :=
  Post formulas solver inventory before after final ∧ Frame formulas solver inventory after.checked ∧
    Fits seed.2 after.checked ∧ Carrier (fun guard => guard ∈ seed.1) after.checked.native.machine.heap

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.node fuel budget seed).2 →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    ∃ next final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧
      Returned formulas solver (Schedule.node fuel budget seed) next before after final ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.body fuel budget seed).2 →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    ∃ next final, ∃ actual : NodeBody budget request before result after,
      NodeBodyReads formulas solver actual memos final ∧
      Returned formulas solver (Schedule.body fuel budget seed) next before after final ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values results : List Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Room bits (Schedule.rows fuel budget seed).2 →
    rows fuel g s r e p h m c n budget inherited values before = .done results after →
    ∃ next final, ∃ actual : Rows budget inherited values before results after,
      RowsReads formulas solver actual memos final ∧
      Returned formulas solver (Schedule.rows fuel budget seed) next before after final ∧
      Edges after.checked.native.machine.heap results ∧ RowsLaw formulas solver actual

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    Room bits (Schedule.descendants fuel budget seed).2 →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    ∃ next final, ∃ actual : Descendants budget inherited value before result after,
      DescendantsReads formulas solver actual memos final ∧
      Returned formulas solver (Schedule.descendants fuel budget seed) next before after final ∧
      Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver ⟨inherited,value⟩ result

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.children fuel budget seed).2 →
    SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n budget combined values before = .done results after →
    ∃ next final, ∃ actual : Children budget combined values before results after,
      ChildrenReads formulas solver actual memos final ∧
      Returned formulas solver (Schedule.children fuel budget seed) next before after final ∧
      Values after.checked.native.machine.heap results ∧ ChildrenLaw formulas solver actual

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.walk fuel budget seed).2 →
    walk fuel g s r e p h m c n budget combined index values before = .done results after →
    ∃ next final, ∃ actual : Walk budget combined index values before results after,
      WalkReads formulas solver actual memos final ∧
      Returned formulas solver (Schedule.walk fuel budget seed) next before after final ∧
      Values after.checked.native.machine.heap results ∧ WalkLaw formulas solver actual

private theorem nodeCall_step (fuel : Nat) (bodyAt : NodeBodyAt formulas solver (bits := bits) fuel) :
    NodeCallAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos seed initial frame fits known inherited available room done
  rcases started : beginNode request before with ⟨handle,action,running⟩
  cases action with
  | ready value =>
      simp only [nodeCall,started] at done
      cases done
      have same := (SourceCurrentAllocatedPartialMemoSound.beginNode_ready_sound formulas solver request before
        initial.sound initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited available handle value running started).1
      subst running
      obtain ⟨post,resident,law⟩ := SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver initial inherited available started
      have padded := Schedule.node_ge fuel budget seed
      exact ⟨inventory,memos,.hit started,.hit (started := started),
        ⟨post,frame,fits.mono padded.1,fun key edge found => padded.2 (known key edge found)⟩,resident,law⟩
  | evaluate original =>
      simp only [nodeCall,started] at done
      obtain ⟨value,middle,first,last⟩ := (bind_done_iff _ _ _ _).mp done
      cases last
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
      have checked := (beginNode_components request before).1
      rw [started] at checked
      have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
      have runningFits : Fits seed.2 running.checked := by simpa only [checked] using fits
      have runningKnown : Carrier (fun guard => guard ∈ seed.1) running.checked.native.machine.heap := by
        simpa only [checked] using known
      obtain ⟨next,final,actual,reads,returned,resident,law⟩ := bodyAt seed runningContext runningFrame runningFits
        runningKnown owner.inherited owner.input room first
      obtain ⟨post,returnedFrame,numeric,carrier⟩ := returned
      obtain ⟨finished,returnedAvailable,returnedLaw⟩ := SourceCurrentAllocatedPartialCallSteps.node_finish formulas solver
        initial inherited available started actual post resident law
      exact ⟨next,final,.evaluate started actual,.evaluate (started := started) reads,
        ⟨finished,returnedFrame,numeric,carrier⟩,returnedAvailable,returnedLaw⟩
  | busy | absent => simp only [nodeCall,started] at done; cases done

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt formulas solver (bits := bits) smaller) :
    WalkAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined index values results before after inventory memos seed
    initial frame fits known inherited available room done
  cases values with
  | nil =>
      simp only [walk] at done
      cases done
      have padded := Schedule.walk_ge fuel budget seed
      exact ⟨inventory,memos,.nil,.nil,
        ⟨Post.refl initial,frame,fits.mono padded.1,fun key edge found => padded.2 (known key edge found)⟩,
        (by intro value member; cases member),
        SourceCurrentAllocatedPartialWalkLanguage.walk_nil formulas solver budget combined index before⟩
  | cons value rest =>
      cases fuel with
      | zero => simp only [walk] at done; cases done
      | succ fuel =>
          simp only [walk] at done
          obtain ⟨headValue,middle,first,remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨restValues,finalState,tail,last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          obtain ⟨descentReceipt,descentFrame,descentFits,descentPost⟩ := SourceCurrentInheritedNumeric.descent formulas solver
            inventory before memos combined index initial frame seed.2 fits inherited
          have nodeRoom : Room bits (Schedule.node fuel budget seed).2 :=
            room.mono (Schedule.walk_ge fuel budget (Schedule.node fuel budget seed)).1
          obtain ⟨headInventory,headMemos,headGraph,headReads,headReturned,headAvailable,headLaw⟩ :=
            nodes fuel (Nat.lt_succ_self _) seed descentPost.context descentFrame descentFits known descentReceipt.inherited
              (descentPost.effects.keeps.available _ (available value List.mem_cons_self)) nodeRoom first
          obtain ⟨headPost,headFrame,headFits,headKnown⟩ := headReturned
          have firstPost := descentPost.trans headPost
          have tailAvailable : Values middle.checked.native.machine.heap rest :=
            fun child member => firstPost.effects.keeps.available _ (available child (List.mem_cons_of_mem _ member))
          obtain ⟨next,final,tailGraph,tailReads,tailReturned,restAvailable,tailLaw⟩ :=
            tails fuel (Nat.lt_succ_self _) (Schedule.node fuel budget seed) headPost.context headFrame headFits headKnown
              (inherited.grows firstPost.effects.grows.constraint_growth) tailAvailable room tail
          obtain ⟨tailPost,tailFrame,tailFits,tailKnown⟩ := tailReturned
          refine ⟨next,final,.cons headGraph tailGraph,.cons headReads tailReads,
            ⟨firstPost.trans tailPost,tailFrame,tailFits,tailKnown⟩,?_,
            SourceCurrentAllocatedPartialWalkLanguage.walk_cons_receipt formulas solver headGraph tailGraph descentReceipt headLaw tailLaw⟩
          intro child member
          rcases List.mem_cons.mp member with same | member
          · subst child
            exact tailPost.effects.keeps.available _ headAvailable
          · exact restAvailable child member

private theorem children_step (fuel : Nat) (walks : WalkAt formulas solver (bits := bits) fuel) :
    ChildrenAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget combined values results before after inventory memos seed
    initial frame fits known inherited available room done
  cases combined with
  | contradiction =>
      simp only [SourceCurrentAllocatedPartialWorker.children] at done
      cases done
      have padded := Schedule.children_ge fuel budget seed
      refine ⟨inventory,memos,.contradiction,.contradiction,
        ⟨Post.refl initial,frame,fits.mono padded.1,fun key edge found => padded.2 (known key edge found)⟩,?_,
        SourceCurrentAllocatedPartialWalkLanguage.children_contradiction formulas solver budget values before⟩
      intro value member
      obtain ⟨original,_member,same⟩ := List.mem_map.mp member
      subst value
      exact InternedProbeProvenance.empty_available _
  | live identity records =>
      simp only [SourceCurrentAllocatedPartialWorker.children] at done
      obtain ⟨next,final,actual,reads,returned,resident,law⟩ :=
        walks seed initial frame fits known inherited available room done
      exact ⟨next,final,.live actual,.live reads,returned,resident,
        SourceCurrentAllocatedPartialWalkLanguage.children_live formulas solver actual inherited.2 law⟩

end MicroCFTA.SourceCurrentOuterInitialActual
