import MicroCFTA.SourceCurrentSharedOuterPrefixInvariants
import MicroCFTA.SourceCurrentSharedOuterExecutionRuntime

/-!
# Physical input facts at actual shared busy faults

An actual busy failure constructs its own literal prefix and active owners.
The weak initial physical facts derive ready requests at the fault caller.
No Context, Room or future prefix is an input. The ancestor witness retains
its actual activation. This module does not prove operation growth along
that witness, exclude a key collision or prove whole-call completion.
-/
namespace MicroCFTA.SourceCurrentSharedOuterPrefixBusy
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentSharedOuterExecutionAncestry (Reached caller)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentSharedOuterPrefixInvariants
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "NativeGood" => SourceCurrentNativeOperationHeap.Good
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- An actual busy failure derives its own reached dispatch and full physical invariant. -/
theorem busy {g s r e p h m c n budget handle : Nat} {phase : Phase width} {after : Caller width}
    (good : Good (caller phase)) (inputs : Inputs phase)
    (actual : SourceCurrentSharedOuterActiveAncestry.run g s r e p h m c n budget phase = .failed (.nodeMemo handle .busy) after) :
    Good after ∧ ∃ fuel request,
      Reached g s r e p h m c n budget phase (.node fuel request after) ∧
      beginNode request after = (handle,.busy,after) ∧ NodeReady after request := by
  have valid : SourceCurrentSharedOuterExecutionRuntime.NodeValid (caller phase) :=
    FlatMemoThunk.Valid.map _ _ _ _ good.nodes (fun _ _ => trivial)
  obtain ⟨fuel,request,past,busy⟩ := SourceCurrentSharedOuterExecutionRuntime.failed valid actual
  have current := reached past good inputs
  exact ⟨current.1,fuel,request,past,busy,current.2⟩

/-- An initial busy failure derives all active owners and the exact colliding full request. -/
theorem initial_busy {g s r e p h m c n budget handle : Nat} (checked : Checked width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (fuel : Nat) (request : NodeRequest) (good : NativeGood checked)
    (stored : Stored checked.native.machine.heap memo) (probes : InternedFreshOrdinaryProbeHeap.Heap checked.native.machine.heap)
    (ready : EqReady checked.operations.constraints request.inherited) (available : Available checked.native.machine.heap request.value)
    {after : Caller width}
    (actual : nodeCall fuel g s r e p h m c n budget request (SourceCurrentAllocatedPartialState.initial checked memo fourth) =
      .failed (.nodeMemo handle .busy) after) :
    Good after ∧ ∃ next candidate,
      NodeReady after candidate ∧
      Reached g s r e p h m c n budget
        (.node fuel request (SourceCurrentAllocatedPartialState.initial checked memo fourth)) (.node next candidate after) ∧
      beginNode candidate after = (handle,.busy,after) ∧
      ∃ owner, after.nodeResults.cells handle = some ⟨owner,.evaluating⟩ ∧ owner = candidate ∧
        SourceCurrentSharedOuterExecutionRuntime.Ancestor g s r e p h m c n budget
          (.node fuel request (SourceCurrentAllocatedPartialState.initial checked memo fourth)) (.node next candidate after) handle owner ∧
        (∀ other captured, after.nodeResults.cells other = some ⟨captured,.evaluating⟩ → NodeReady after captured ∧
          SourceCurrentSharedOuterExecutionRuntime.Ancestor g s r e p h m c n budget
            (.node fuel request (SourceCurrentAllocatedPartialState.initial checked memo fourth)) (.node next candidate after) other captured) := by
  obtain ⟨next,candidate,past,busy,owner,present,key,earlier,allOwners⟩ :=
    SourceCurrentSharedOuterExecutionRuntime.initial checked memo fourth fuel request actual
  have current := reached past (initial checked memo fourth good stored probes) ⟨ready,available⟩
  have ownerReady := (current.1.nodes.checked handle _ present).1
  exact ⟨current.1,next,candidate,current.2,past,busy,owner,present,same_key current.1 ownerReady current.2 key,
    earlier,fun other captured found =>
      ⟨(current.1.nodes.checked other _ found).1,(allOwners other captured found)⟩⟩

end MicroCFTA.SourceCurrentSharedOuterPrefixBusy
