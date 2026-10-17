import MicroCFTA.SourceCurrentNativeMuGrowthExecution
import MicroCFTA.SourceCurrentNativeMuGrowthWriters
import MicroCFTA.SourceCurrentStoredReconstructionReplay

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

namespace MicroCFTA.GrowthReconstructionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0, .binder false (.node [.mk 1 true [.var 1]])]])
private def built := build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry, body, depth, ordinary)
  | _ => (⟨0, .node []⟩, .empty, .empty, .empty)
private def entry := (fields root).1
private def body := (fields root).2.1
private def depth := (fields root).2.2.1
private def ordinary := (fields root).2.2.2
private def key := muKey depth ordinary
private def bodyEnvironment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .interned entry.identity then some (.reference .depth) else none
private def ordinaryEnvironment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned (ordinaryLevel depth) then some (.reference .depth) else none
private theorem actual : built = .done root heap := by cbv
private theorem present : heap.nodeRecords key = some (.mu entry body depth ordinary) := by cbv
private theorem ready : Ready heap := SourceEqualityRequiredCache.constructed expression root heap actual

private theorem connected_proof :
    ∃ left middle right after,
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnvironment heap = .done left middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnvironment middle = .done right after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      SourceCurrentNativeMuGrowthWriters.Written empty after key (.mu entry body depth ordinary) ∧
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnvironment after = .done left after ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnvironment after = .done right after := by
  let path := SourceCurrentNativeMuGrowthExecution.closed_path expression
  have written := SourceCurrentNativeMuGrowthWriters.from_empty path key entry body depth ordinary present
  obtain ⟨left, middle, right, after, bodyDone, ordinaryDone, first, second, leftAvailable, rightAvailable,
    _, _, _, _, _, bodyWarm, ordinaryWarm⟩ :=
    SourceCurrentStoredReconstructionReplay.mu key entry body depth ordinary (.reference .depth) heap ready present
      (InternedNestedProvenance.depth_available heap) path.history
  exact ⟨left, middle, right, after, bodyDone, ordinaryDone, first, second, leftAvailable, rightAvailable,
    written.later (first.trans second).growth, bodyWarm, ordinaryWarm⟩

/-- A source-built nested Mu retains its actual writer at the common reconstruction and replay heap. -/
theorem connected :
    ∃ left middle right after,
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnvironment heap = .done left middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnvironment middle = .done right after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      SourceCurrentNativeMuGrowthWriters.Written empty after key (.mu entry body depth ordinary) ∧
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnvironment after = .done left after ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnvironment after = .done right after := connected_proof

end MicroCFTA.GrowthReconstructionKernels
#check @MicroCFTA.GrowthReconstructionKernels.connected
#print MicroCFTA.GrowthReconstructionKernels.connected
#print axioms MicroCFTA.GrowthReconstructionKernels.connected
