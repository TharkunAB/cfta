import MicroCFTA.SourceCurrentOuterInitialPrefix

/-!
# Semantic and scheduled bounds at actual outer node-busy faults

The actual failed call supplies its own reached dispatch. Initial facts
then derive the semantic context and bounds at that exact fault caller.
The current evaluating owner is the complete colliding request. This
result does not exclude the collision or prove successful termination.
-/
namespace MicroCFTA.SourceCurrentOuterInitialBusy
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (NodeValid Reached)
open SourceCurrentOuterPrefixInvariants (Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "forecast" => SourceCurrentOuterInitialPrefix.forecast

variable [DecidableEq (EdgeKey Symbol Guard)] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem node_valid {inventory : Inventory} {before : Caller (bits+2)} {memos : Memos}
    (initial : Context formulas solver inventory before memos) : NodeValid before := by
  refine ⟨initial.sound.valid.nodes.bounded,?_,fun _ _ _ => trivial⟩
  intro key handle present
  obtain ⟨cell,found,linked⟩ := initial.sound.valid.nodes.linked key handle present
  exact ⟨cell,found,linked.2⟩

private theorem same_request {inventory : Inventory} {before : Caller (bits+2)} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (first second : NodeRequest)
    (left : SourceCurrentOuterPrefixInvariants.NodeReady before first)
    (right : SourceCurrentOuterPrefixInvariants.NodeReady before second) (same : first.key = second.key) :
    first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _
    initial.ready.good.operations.constraints first.inherited second.inherited left.1 right.1 (congrArg Prod.fst same)
  have values := InternedFreshProbeKeys.resident_reference_injective _
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent first.value second.value
    left.2.resident right.2.resident (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

variable [DecidableEq Symbol] [DecidableEq Node]

/-- An actual busy failure derives its full semantic fault context and exact evaluating request. -/
theorem busy {g s r e p h m c n budget handle : Nat} {phase : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} {after : Caller (bits+2)} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller phase) memos)
    (frame : Frame formulas solver inventory (caller phase).checked)
    (fits : Fits seed.2 (caller phase).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) (caller phase).checked.native.machine.heap)
    (inputs : Inputs phase) (room : Room bits (forecast budget phase seed).2)
    (failed : SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget phase =
      .failed (.nodeMemo handle .busy) after) :
    ∃ fuel request next final,
      Reached g s r e p h m c n budget phase (.node fuel request after) ∧
      beginNode request after = (handle,.busy,after) ∧
      Post formulas solver next (caller phase) after final ∧ Frame formulas solver next after.checked ∧
      Fits (forecast budget phase seed).2 after.checked ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ (forecast budget phase seed).1) after.checked.native.machine.heap ∧
      SourceCurrentOuterPrefixInvariants.NodeReady after request ∧
      after.nodeResults.cells handle = some ⟨request,.evaluating⟩ := by
  obtain ⟨fuel,request,actual,dispatched⟩ := SourceCurrentOuterExecutionAncestry.failed
    (node_valid formulas solver initial) failed
  obtain ⟨next,final,current,_trace,post,returned,_numeric,_carrier,ready,_below,_subset,_room,numeric,carrier,_fuel⟩ :=
    SourceCurrentOuterInitialPrefix.reached formulas solver seed actual initial frame fits known inputs room
  obtain ⟨_same,linked,owner,present⟩ := SourceCurrentOuterBusyOwners.node_busy request after after handle dispatched
  obtain ⟨cell,found,key⟩ := post.context.sound.valid.nodes.linked request.key handle linked
  have same := Option.some.inj (found.symm.trans present)
  subst cell
  have ownerReady := post.context.sound.nodes handle _ present
  have equal := same_request formulas solver post.context owner request
    ⟨ownerReady.inherited,ownerReady.input⟩ ready key.2
  subst owner
  exact ⟨fuel,request,next,final,actual,dispatched,post,returned,numeric,carrier,ready,present⟩

end MicroCFTA.SourceCurrentOuterInitialBusy
