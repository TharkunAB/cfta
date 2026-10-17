import MicroCFTA.SourceCurrentStoredAlphaNodeReconstruction
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
namespace MicroCFTA.StoredAlphaNodeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredAlphaNodeReconstruction
private def captures : List (Value Nat Bool) := [.reference (.uninterned 0),.reference (.uninterned 1)]
private def expression : Syntax Nat Bool := .node [.mk 0 true [
  .node [.mk 7 false [.var 0]],.node [.mk 7 false [.var 1]]]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Nat Bool := ((children root)[0]?).getD .empty
private def right : Value Nat Bool := ((children root)[1]?).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × List (EdgeValue Nat Bool) × Nat × List Reference
  | .node entry rows level free => (entry,rows,level,free)
  | _ => (⟨0,.node []⟩,[],0,[])
private def firstRows := (fields left).2.1
private def secondRows := (fields right).2.1
private def firstRow : EdgeValue Nat Bool := match firstRows with | row::_ => row | [] => .mk ⟨0,⟨0,[],false⟩⟩ []
private def secondRow : EdgeValue Nat Bool := match secondRows with | row::_ => row | [] => .mk ⟨0,⟨0,[],false⟩⟩ []
private def firstEnv : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 0 then some (.reference .depth) else none
private def secondEnv : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned 1 then some (.reference .depth) else none
private theorem actual : built = .done root heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  simp only [captures,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact InternedNestedProvenance.ordinary_available empty 0
  · exact InternedNestedProvenance.ordinary_available empty 1
private theorem semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap :=
  SourceRecursiveIntersectionSemanticHeap.source expression captures empty SourceRecursiveIntersectionSemanticHeap.empty_heap inputs
private theorem ready : Ready heap := by
  have context := SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures inputs
  refine ⟨semantic,InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid
    InternedRecordCoherence.empty_correct.2 root heap actual,?_⟩
  exact (InternedOpenDepthExecution.build_depth expression captures empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedOpenDepthReadback.empty_heap).heap
private theorem leftShape : left = .node (fields left).1 firstRows (fields left).2.2.1 (fields left).2.2.2 := by cbv
private theorem rightShape : right = .node (fields right).1 secondRows (fields right).2.2.1 (fields right).2.2.2 := by cbv
private theorem rootsAvailable : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.build_verified expression captures empty InternedNestedFacts.empty_facts inputs).result root heap actual
  exact ⟨available.children left (by cbv; exact .head _),available.children right (by cbv; exact .tail _ (.head _))⟩
private theorem firstRowsEq : firstRows = [firstRow] := by cbv
private theorem secondRowsEq : secondRows = [secondRow] := by cbv
private theorem related : RowsAlpha firstEnv secondEnv firstRows secondRows := by
  constructor
  · intro row member
    rw [firstRowsEq] at member
    cases List.mem_singleton.mp member
    refine ⟨secondRow,by rw [secondRowsEq]; exact .head _,by cbv,by cbv,?_⟩
    cbv
  · intro row member
    rw [secondRowsEq] at member
    cases List.mem_singleton.mp member
    refine ⟨firstRow,by rw [firstRowsEq]; exact .head _,by cbv,by cbv,?_⟩
    cbv
private theorem produced_proof :
    left ≠ right ∧ left.free ≠ [] ∧ right.free ≠ [] ∧
    ∃ value middle after,
      InternedFreshOrdinaryStoredSubstitution.execute left firstEnv heap = .done value middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute right secondEnv middle = .done value after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after value := by
  have leftAvailable := rootsAvailable.1
  have rightAvailable := rootsAvailable.2
  rw [leftShape] at leftAvailable
  rw [rightShape] at rightAvailable
  obtain ⟨value,middle,after,firstDone,secondDone,firstKept,secondKept,output⟩ :=
    SourceCurrentStoredAlphaNodeReconstruction.complete (fields left).1 (fields right).1 firstRows secondRows
      (fields left).2.2.1 (fields right).2.2.1 (fields left).2.2.2 (fields right).2.2.2
      firstEnv secondEnv heap ready leftAvailable rightAvailable
      (by intro name result found; dsimp only [firstEnv] at found; split at found
          · cases found; exact InternedNestedProvenance.depth_available heap
          · cases found)
      (by intro name result found; dsimp only [secondEnv] at found; split at found
          · cases found; exact InternedNestedProvenance.depth_available heap
          · cases found)
      (by cbv) (by cbv) related
  rw [← leftShape] at firstDone
  rw [← rightShape] at secondDone
  refine ⟨?_,by decide +kernel,by decide +kernel,value,middle,after,firstDone,secondDone,firstKept,secondKept,output⟩
  intro same
  have different : left.free ≠ right.free := by decide +kernel
  exact different (congrArg Value.free same)
/-- Two distinct source-built open roots reconstruct one exact value under their own replacement maps. -/
theorem produced :
    left ≠ right ∧ left.free ≠ [] ∧ right.free ≠ [] ∧
    ∃ value middle after,
      InternedFreshOrdinaryStoredSubstitution.execute left firstEnv heap = .done value middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute right secondEnv middle = .done value after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after value := produced_proof
end MicroCFTA.StoredAlphaNodeKernels
#check @MicroCFTA.StoredAlphaNodeKernels.produced
#print MicroCFTA.StoredAlphaNodeKernels.produced
#print axioms MicroCFTA.StoredAlphaNodeKernels.produced
