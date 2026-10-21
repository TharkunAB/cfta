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
      have hit := SourceCurrentAllocatedPartialMemoSound.beginNode_ready_sound formulas solver request before
        initial.sound initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited available handle value running started
      cases done
      obtain ⟨same,resident,law⟩ := hit
      subst after
      have padded := Schedule.node_ge fuel budget seed
      exact ⟨inventory,memos,.hit started,.hit (started := started),
        ⟨Post.refl initial,frame,fits.mono padded.1,fun key edge found => padded.2 (known key edge found)⟩,resident,law⟩
  | evaluate original =>
      simp only [nodeCall,started] at done
      obtain ⟨value,middle,first,last⟩ := (bind_done_iff _ _ _ _).mp done
      cases last
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
      have checked := (beginNode_components request before).1
      rw [started] at checked
      dsimp only at checked
      have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
      have runningFits : Fits seed.2 running.checked := by simpa only [checked] using fits
      have runningKnown : Carrier (fun guard => guard ∈ seed.1) running.checked.native.machine.heap := by
        simpa only [checked] using known
      have bodyRoom : Room bits (Schedule.body fuel budget seed).2 := by simpa only [Schedule.node] using room
      obtain ⟨next,final,actual,reads,returned,resident,law⟩ := bodyAt seed runningContext runningFrame runningFits
        runningKnown owner.inherited owner.input bodyRoom first
      obtain ⟨post,returnedFrame,numeric,carrier⟩ := returned
      obtain ⟨finished,returnedAvailable,returnedLaw⟩ := SourceCurrentAllocatedPartialCallSteps.node_finish formulas solver
        initial inherited available started actual post resident law
      exact ⟨next,final,.evaluate started actual,.evaluate (started := started) reads,
        ⟨finished,returnedFrame,(by simpa only [Schedule.node,finishNode] using numeric),
          (by simpa only [Schedule.node,finishNode] using carrier)⟩,returnedAvailable,returnedLaw⟩
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
          rw [Schedule.walk] at room ⊢
          simp only [walk] at done
          obtain ⟨headValue,middle,first,remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨restValues,finalState,tail,last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          obtain ⟨descentReceipt,descentFrame,descentFits,descentPost⟩ := SourceCurrentInheritedNumeric.descent formulas solver
            inventory before memos combined index initial frame seed.2 fits inherited
          have nodeRoom : Room bits (Schedule.node fuel budget seed).2 :=
            room.mono (Schedule.walk_ge fuel budget (Schedule.node fuel budget seed)).1
          obtain ⟨headInventory,headMemos,headGraph,headReads,headReturned,headAvailable,headLaw⟩ :=
            nodes fuel (Nat.lt_succ_self _) (request := ⟨(descend before combined index).1,value⟩)
              (before := (descend before combined index).2) seed descentPost.context descentFrame descentFits known descentReceipt.inherited
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
      rw [Schedule.children] at room ⊢
      simp only [SourceCurrentAllocatedPartialWorker.children] at done
      obtain ⟨next,final,actual,reads,returned,resident,law⟩ :=
        walks seed initial frame fits known inherited available room done
      exact ⟨next,final,.live actual,.live reads,returned,resident,
        SourceCurrentAllocatedPartialWalkLanguage.children_live formulas solver actual inherited.2 law⟩

private theorem descendants_step (fuel : Nat) (child : ChildrenAt formulas solver (bits := bits) fuel) :
    DescendantsAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited value result before after inventory memos seed
    initial frame fits known inheritedReady resident room done
  rw [Schedule.descendants] at room ⊢
  cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [descendants,observed] at done; cases done
      | ok answer =>
          cases answer with
          | none => simp only [descendants,observed] at done; cases done
          | some combined =>
              have prefixSame : prefixState before value inherited =
                  advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                    ⟨before.checked.native.machine.heap,operations⟩) before.fourth before.merge := by
                simp only [prefixState,SourceCurrentAllocatedInheritedPrefix.state,observed]
              simp only [descendants,observed] at done
              rw [← prefixSame] at done
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
              have childRoom : Room bits (Schedule.children fuel budget seed).2 :=
                room.mono (Schedule.rebuild_ge (Schedule.children fuel budget seed)).1
              obtain ⟨next,final,actual,reads,childReturned,available,law⟩ := child seed prefixPost.context prefixFrame prefixFits
                known prefixReceipt.combinedReady childInputs childRoom first
              obtain ⟨childPost,childFrame,childFits,childKnown⟩ := childReturned
              have firstPost := prefixPost.trans childPost
              have sourceResident := InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _ resident
              obtain ⟨rebuilt,returned,numeric,carrier⟩ := SourceCurrentOuterRebuildGuardAlphabet.edge
                (Schedule.children fuel budget seed).1 formulas solver next (Schedule.children fuel budget seed).2
                  value values middle.checked childFrame childFits childKnown sourceResident available actual.length
              obtain ⟨_same,lastPost⟩ := SourceCurrentAllocatedPartialStepEffects.raw_edge formulas solver next middle final
                childPost.context value values sourceResident available actual.length
              exact ⟨next,final,.run combinedEquation actual,.run (combined := combinedEquation) reads,
                ⟨firstPost.trans lastPost,returned,numeric,carrier⟩,rebuilt.resident,
                SourceCurrentAllocatedPartialForestLanguage.descendants formulas solver prefixReceipt actual law rebuilt⟩

private theorem rows_step (fuel : Nat)
    (descendAt : ∀ smaller, smaller < fuel → DescendantsAt formulas solver (bits := bits) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt formulas solver (bits := bits) smaller) :
    RowsAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget inherited values results before after inventory memos seed
    initial frame fits known inheritedReady resident room done
  cases values with
  | nil =>
      simp only [rows] at done
      cases done
      have padded := Schedule.rows_ge fuel budget seed
      exact ⟨inventory,memos,.nil,.nil,
        ⟨Post.refl initial,frame,fits.mono padded.1,fun key edge found => padded.2 (known key edge found)⟩,
        (by intro row member; cases member),SourceCurrentAllocatedPartialForestLanguage.rows_nil formulas solver budget inherited before⟩
  | cons original rest =>
      cases fuel with
      | zero => simp only [rows] at done; cases done
      | succ fuel =>
          rw [Schedule.rows] at room ⊢
          simp only [rows] at done
          obtain ⟨narrowed,middle,first,remaining⟩ := (bind_done_iff _ _ _ _).mp done
          obtain ⟨edgeResult,current,second,remaining⟩ := (bind_done_iff _ _ _ _).mp remaining
          obtain ⟨restResults,finalState,tail,last⟩ := (bind_done_iff _ _ _ _).mp remaining
          cases last
          let edgeSeed := Schedule.parent budget seed
          let childSeed := Schedule.descendants fuel budget edgeSeed
          have edgeRoom : Room bits edgeSeed.2 := room.mono
            ((Schedule.descendants_ge fuel budget edgeSeed).1.trans (Schedule.rows_ge fuel budget childSeed).1)
          obtain ⟨edgeInventory,edgeMemos,edgeReceipt,edgeFits,edgeKnown⟩ :=
            SourceCurrentOuterEdgeGuardAlphabet.edge_call formulas solver inventory budget seed.1 ⟨inherited,original⟩
              before memos initial frame seed.2 fits known inheritedReady (resident original List.mem_cons_self)
              (Schedule.parent_reserved bits budget seed edgeRoom) first
          have childRoom : Room bits childSeed.2 := room.mono (Schedule.rows_ge fuel budget childSeed).1
          obtain ⟨childInventory,childMemos,childGraph,childReads,childReturned,childResident,childLaw⟩ :=
            descendAt fuel (Nat.lt_succ_self _) edgeSeed edgeReceipt.post.context edgeReceipt.frame edgeFits edgeKnown
              (inheritedReady.grows edgeReceipt.post.effects.grows.constraint_growth) edgeReceipt.semantic.resident childRoom second
          obtain ⟨childPost,childFrame,childFits,childKnown⟩ := childReturned
          have firstPost := edgeReceipt.post.trans childPost
          have tailResident : Edges current.checked.native.machine.heap rest :=
            fun edge member => InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _
              (resident edge (List.mem_cons_of_mem _ member))
          obtain ⟨next,final,tailGraph,tailReads,tailReturned,resultsResident,tailLaw⟩ :=
            tails fuel (Nat.lt_succ_self _) childSeed childPost.context childFrame childFits childKnown
              (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident room tail
          obtain ⟨tailPost,tailFrame,tailFits,tailKnown⟩ := tailReturned
          refine ⟨next,final,.cons edgeReceipt.actual childGraph tailGraph,.cons edgeReceipt.reads childReads tailReads,
            ⟨firstPost.trans tailPost,tailFrame,tailFits,tailKnown⟩,?_,
            SourceCurrentAllocatedPartialForestLanguage.rows_cons formulas solver edgeReceipt.actual childGraph tailGraph
              edgeReceipt.semantic.language childLaw tailLaw⟩
          intro edge member
          rcases List.mem_cons.mp member with same | member
          · subst edge
            exact InternedEdgeResidency.edge_grows _ _ tailPost.effects.keeps.growth _ childResident
          · exact resultsResident edge member

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt formulas solver (bits := bits) smaller) :
    NodeBodyAt formulas solver (bits := bits) fuel := by
  intro g s r e p h m c n budget request before after result inventory memos seed
    initial frame fits known inherited available room done
  cases request with
  | mk inheritedValue value =>
      cases value with
      | empty =>
          simp only [nodeBody] at done
          cases done
          have padded := Schedule.body_ge fuel budget seed
          exact ⟨inventory,memos,.empty,.empty,
            ⟨Post.refl initial,frame,fits.mono padded.1,fun key edge found => padded.2 (known key edge found)⟩,
            InternedProbeProvenance.empty_available _,SourceCurrentAllocatedPartialCallSteps.node_refl formulas solver _⟩
      | union entry members depth free =>
          simp only [nodeBody] at done
          cases done
          have padded := Schedule.body_ge fuel budget seed
          exact ⟨inventory,memos,.union,.union,
            ⟨Post.refl initial,frame,fits.mono padded.1,fun key edge found => padded.2 (known key edge found)⟩,
            available,SourceCurrentAllocatedPartialCallSteps.node_refl formulas solver _⟩
      | reference name => simp only [nodeBody] at done; cases done
      | mu entry body depth ordinary =>
          cases observed : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
          | pending => simp only [nodeBody,observed] at done; cases done
          | done value heap =>
              have computed := SourceCurrentMuReconstructionEffects.complete entry body depth ordinary
                before.checked.native.machine.heap initial.ready.semantic.ready.semantic.1.normal.facts.coherent initial.probes available
              have sameHeap : heap = before.checked.native.machine.heap :=
                congrArg InternedNestedConstruction.Outcome.state (observed.symm.trans computed.1)
              subst heap
              simp only [nodeBody,observed] at done
              cases done
              have unchanged : advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                  ⟨before.checked.native.machine.heap,before.checked.operations⟩) before.fourth before.merge = before := by
                cases before
                rfl
              obtain ⟨post,resident,law⟩ := SourceCurrentAllocatedPartialCallSteps.node_binder formulas solver initial available observed
              have padded := Schedule.body_ge fuel budget seed
              exact ⟨inventory,memos,.binder observed,.binder (actual := observed),
                ⟨post,(by simpa only [unchanged] using frame),
                  (by simpa only [unchanged] using fits.mono padded.1),
                  (by simpa only [unchanged] using (show Carrier (fun guard => guard ∈ (Schedule.body fuel budget seed).1)
                    before.checked.native.machine.heap from fun key edge found => padded.2 (known key edge found)))⟩,
                resident,law⟩
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at done; cases done
          | succ fuel =>
              rw [Schedule.body] at room ⊢
              simp only [nodeBody] at done
              obtain ⟨results,middle,first,last⟩ := (bind_done_iff _ _ _ _).mp done
              cases last
              have edges := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
              have rowsRoom : Room bits (Schedule.rows fuel budget seed).2 :=
                room.mono (Schedule.rebuild_ge (Schedule.rows fuel budget seed)).1
              obtain ⟨next,final,actual,reads,rowReturned,rowsResident,law⟩ :=
                rowCalls fuel (Nat.lt_succ_self _) seed initial frame fits known inherited edges rowsRoom first
              obtain ⟨rowPost,rowFrame,rowFits,rowKnown⟩ := rowReturned
              have sourceAvailable := rowPost.effects.keeps.available _ available
              obtain ⟨rebuilt,returned,numeric,carrier⟩ := SourceCurrentOuterRebuildGuardAlphabet.modify
                (Schedule.rows fuel budget seed).1 formulas solver next (Schedule.rows fuel budget seed).2
                  entry original results depth free middle.checked rowFrame rowFits rowKnown sourceAvailable rowsResident actual.length
              obtain ⟨_same,lastPost⟩ := SourceCurrentAllocatedPartialStepEffects.modify formulas solver next middle final
                rowPost.context entry original results depth free sourceAvailable rowsResident
              exact ⟨next,final,.ordinary actual,.ordinary reads,
                ⟨rowPost.trans lastPost,returned,numeric,carrier⟩,rebuilt.available,
                SourceCurrentAllocatedPartialForestLanguage.ordinary formulas solver actual law rebuilt⟩

private theorem all_actual (fuel : Nat) :
    NodeCallAt formulas solver (bits := bits) fuel ∧ NodeBodyAt formulas solver (bits := bits) fuel ∧
    RowsAt formulas solver (bits := bits) fuel ∧ DescendantsAt formulas solver (bits := bits) fuel ∧
    ChildrenAt formulas solver (bits := bits) fuel ∧ WalkAt formulas solver (bits := bits) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walks : WalkAt formulas solver (bits := bits) fuel := walk_step formulas solver fuel (fun smaller less => (ih smaller less).1)
        (fun smaller less => (ih smaller less).2.2.2.2.2)
      have child : ChildrenAt formulas solver (bits := bits) fuel := children_step formulas solver fuel walks
      have descendAt : DescendantsAt formulas solver (bits := bits) fuel := descendants_step formulas solver fuel child
      have rowsAt : RowsAt formulas solver (bits := bits) fuel := rows_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.2.1)
        (fun smaller less => (ih smaller less).2.2.1)
      have bodyAt : NodeBodyAt formulas solver (bits := bits) fuel := nodeBody_step formulas solver fuel (fun smaller less => (ih smaller less).2.2.1)
      exact ⟨nodeCall_step formulas solver fuel bodyAt,bodyAt,rowsAt,descendAt,child,walks⟩

/-- A successful node call has exact semantic reads and scheduled returned resources. -/
theorem node_call (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.node fuel budget seed).2 →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    ∃ next final, ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.node fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.node fuel budget seed).1) after.checked.native.machine.heap ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  intro g s r e p h m c n budget request before after result inventory memos seed initial frame fits known inherited available room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).1 seed initial frame fits known inherited available room done)

/-- A successful node body has exact semantic reads and scheduled returned resources. -/
theorem node_body (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller (bits+2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Room bits (Schedule.body fuel budget seed).2 →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    ∃ next final, ∃ actual : NodeBody budget request before result after,
      NodeBodyReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.body fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.body fuel budget seed).1) after.checked.native.machine.heap ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  intro g s r e p h m c n budget request before after result inventory memos seed initial frame fits known inherited available room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).2.1 seed initial frame fits known inherited available room done)

/-- A successful ordered row run has exact reads and scheduled returned resources. -/
theorem rows (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values results : List Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Room bits (Schedule.rows fuel budget seed).2 →
    SourceCurrentAllocatedPartialWorker.rows fuel g s r e p h m c n budget inherited values before = .done results after →
    ∃ next final, ∃ actual : Rows budget inherited values before results after,
      RowsReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.rows fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.rows fuel budget seed).1) after.checked.native.machine.heap ∧
      Edges after.checked.native.machine.heap results ∧ RowsLaw formulas solver actual := by
  intro g s r e p h m c n budget inherited values results before after inventory memos seed initial frame fits known inheritedReady resident room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).2.2.1 seed initial frame fits known inheritedReady resident room done)

/-- Successful descendants retain the exact edge law and scheduled returned resources. -/
theorem descendants (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    Room bits (Schedule.descendants fuel budget seed).2 →
    SourceCurrentAllocatedPartialWorker.descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    ∃ next final, ∃ actual : Descendants budget inherited value before result after,
      DescendantsReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.descendants fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.descendants fuel budget seed).1) after.checked.native.machine.heap ∧
      Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver ⟨inherited,value⟩ result := by
  intro g s r e p h m c n budget inherited value result before after inventory memos seed initial frame fits known inheritedReady resident room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).2.2.2.1 seed initial frame fits known inheritedReady resident room done)

/-- Successful children retain the exact forest law and scheduled returned resources. -/
theorem children (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.children fuel budget seed).2 →
    SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n budget combined values before = .done results after →
    ∃ next final, ∃ actual : Children budget combined values before results after,
      ChildrenReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.children fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.children fuel budget seed).1) after.checked.native.machine.heap ∧
      Values after.checked.native.machine.heap results ∧ ChildrenLaw formulas solver actual := by
  intro g s r e p h m c n budget combined values results before after inventory memos seed initial frame fits known inheritedReady available room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).2.2.2.2.1 seed initial frame fits known inheritedReady available room done)

/-- A successful indexed walk retains the exact forest law and scheduled returned resources. -/
theorem walk (fuel : Nat) :
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed),
    Context formulas solver inventory before memos → Frame formulas solver inventory before.checked →
    Fits seed.2 before.checked → Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Room bits (Schedule.walk fuel budget seed).2 →
    SourceCurrentAllocatedPartialWorker.walk fuel g s r e p h m c n budget combined index values before = .done results after →
    ∃ next final, ∃ actual : Walk budget combined index values before results after,
      WalkReads formulas solver actual memos final ∧
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧ Fits (Schedule.walk fuel budget seed).2 after.checked ∧
      Carrier (fun guard => guard ∈ (Schedule.walk fuel budget seed).1) after.checked.native.machine.heap ∧
      Values after.checked.native.machine.heap results ∧ WalkLaw formulas solver actual := by
  intro g s r e p h m c n budget combined index values results before after inventory memos seed initial frame fits known inheritedReady available room done
  simpa only [Returned, and_assoc] using
    ((all_actual formulas solver (bits := bits) fuel).2.2.2.2.2 seed initial frame fits known inheritedReady available room done)

end MicroCFTA.SourceCurrentOuterInitialActual
