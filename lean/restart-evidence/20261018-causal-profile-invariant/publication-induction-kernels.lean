import MicroCFTA.SourceCurrentPublicationHeapInduction
namespace MicroCFTA.PublicationHeapInductionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentConstrainedCapSourceHistory (Origin)
open SourceCurrentPublicationHeapInduction (Heap)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def source : Syntax Nat Bool := .binder true (.node [.mk 7 false []])
private def actual := build source [] empty
private def result : Value Nat Bool := match actual with | .done value _ => value | .pending .. => .empty
private def reader := actual.state
private def stored := (reader.nodeRecords (muKey result result)).getD .empty
private def entry : Interned InternedBinderProtocol.NodeKey :=
  match stored with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private theorem actual_done : build source [] empty = .done result reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source result reader actual_done
private theorem installed : reader.nodeRecords (muKey result result) = some (.mu entry result result result) := by cbv
private theorem stored_shape : stored = .mu entry result result result := by cbv
private theorem invariant : Heap (Origin (Symbol := Nat) (Guard := Bool)) reader :=
  SourceCurrentPublicationHeapInduction.closed (Origin (Symbol := Nat) (Guard := Bool)) source
    (by intro event _ _ _ _ _; exact event.origin)
private theorem writer : Origin entry result result result := invariant _ _ _ _ _ installed
private theorem depth_gap : result.depth = 0 ∧ stored.depth = 1 ∧ result.free = [] := by cbv
private theorem returned : InternedNestedConstruction.finish true stored = result := by
  rw [stored_shape]
  cbv

private theorem checked_witness :
    build source [] empty = .done result reader ∧ Ready reader ∧
    Heap (Origin (Symbol := Nat) (Guard := Bool)) reader ∧
    reader.nodeRecords (muKey result result) = some (.mu entry result result result) ∧
    Origin entry result result result ∧ stored = .mu entry result result result ∧
    result.depth = 0 ∧ stored.depth = 1 ∧ result.free = [] ∧
    InternedNestedConstruction.finish true stored = result :=
  ⟨actual_done,ready,invariant,installed,writer,stored_shape,depth_gap.1,depth_gap.2.1,depth_gap.2.2,returned⟩

theorem smart_unused_origin :
    build source [] empty = .done result reader ∧ Ready reader ∧
    Heap (Origin (Symbol := Nat) (Guard := Bool)) reader ∧
    reader.nodeRecords (muKey result result) = some (.mu entry result result result) ∧
    Origin entry result result result ∧ stored = .mu entry result result result ∧
    result.depth = 0 ∧ stored.depth = 1 ∧ result.free = [] ∧
    InternedNestedConstruction.finish true stored = result := checked_witness

end MicroCFTA.PublicationHeapInductionKernels
