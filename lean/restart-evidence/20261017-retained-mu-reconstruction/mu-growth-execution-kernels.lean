import MicroCFTA.SourceCurrentNativeMuGrowthExecution
import MicroCFTA.InternedFreshOrdinaryReplay
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.MuGrowthExecutionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open SourceCurrentNativeMuGrowthHistory (Path)
open SourceCurrentNativeMuPublication (History)
private def inner : Syntax Nat Bool := .binder false (.node [.mk 1 false [.var 1]])
private def expression : Syntax Nat Bool := .binder false (.node [.mk 0 true [inner,.var 0]])
private def built := build expression [] empty
private def original : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem actual : built = .done original heap := by cbv
private theorem nested_proof :
    build expression [] empty = .done original heap ∧ Nonempty (Path empty heap) ∧
      Grows empty heap ∧ Nonempty (History empty heap) ∧
      build expression [] heap = .done original heap ∧ Nonempty (Path heap heap) := by
  have path : Path empty heap := SourceCurrentNativeMuGrowthExecution.closed_path expression
  have context : SourceCurrentConstrainedCapSourceHistory.Context heap [] :=
    SourceCurrentConstrainedCapSourceHistory.empty_context.build expression
  have warm : build expression [] heap = .done original heap :=
    InternedFreshOrdinaryReplay.empty_replay expression original heap heap actual (grows_refl heap)
  refine ⟨actual,⟨path⟩,path.growth,⟨path.history⟩,warm,?_⟩
  simpa only [warm,Outcome.state] using SourceCurrentNativeMuGrowthExecution.build_path expression [] heap context
/-- Actual nested completion and exact warm replay both produce their own growth paths. -/
theorem nested :
    build expression [] empty = .done original heap ∧ Nonempty (Path empty heap) ∧
      Grows empty heap ∧ Nonempty (History empty heap) ∧
      build expression [] heap = .done original heap ∧ Nonempty (Path heap heap) := nested_proof

private def reservedKey : InternedBinderProtocol.NodeKey :=
  muKey (Value.reference .depth : Value Nat Bool) (.reference (.uninterned 0))
private def reservedHeap : State Nat Bool :=
  {empty with nodes := (Cache.intern (empty (Symbol := Nat) (Guard := Bool)).nodes reservedKey).2}
private theorem pending_proof :
    build (.binder false (.var 0)) [] reservedHeap = .pending reservedKey reservedHeap ∧
      Nonempty (Path reservedHeap reservedHeap) ∧ Grows reservedHeap reservedHeap ∧
      Nonempty (History reservedHeap reservedHeap) := by
  have actual : build (.binder false (.var 0)) [] reservedHeap = .pending reservedKey reservedHeap := by
    simp only [build,Outcome.bind,InternedNestedConstruction.work,withoutSelfReference]
    rfl
  have context : SourceCurrentConstrainedCapSourceHistory.Context reservedHeap [] :=
    SourceCurrentConstrainedCapSourceHistory.empty_context.reserve reservedKey
  obtain ⟨path⟩ := SourceCurrentNativeMuGrowthExecution.build_path (.binder false (.var 0)) [] reservedHeap context
  have same : Path reservedHeap reservedHeap := by simpa only [actual,Outcome.state] using path
  exact ⟨actual,⟨same⟩,same.growth,⟨same.history⟩⟩
/-- An actual pending reserved owner has a growth path without a successful return premise. -/
theorem pending :
    build (.binder false (.var 0)) [] reservedHeap = .pending reservedKey reservedHeap ∧
      Nonempty (Path reservedHeap reservedHeap) ∧ Grows reservedHeap reservedHeap ∧
      Nonempty (History reservedHeap reservedHeap) := pending_proof
end MicroCFTA.MuGrowthExecutionKernels
#check @MicroCFTA.MuGrowthExecutionKernels.nested
#print MicroCFTA.MuGrowthExecutionKernels.nested
#print axioms MicroCFTA.MuGrowthExecutionKernels.nested
#check @MicroCFTA.MuGrowthExecutionKernels.pending
#print MicroCFTA.MuGrowthExecutionKernels.pending
#print axioms MicroCFTA.MuGrowthExecutionKernels.pending
