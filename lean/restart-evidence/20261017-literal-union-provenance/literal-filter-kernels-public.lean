import MicroCFTA.SourceCurrentLiteralFilterParts
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

namespace MicroCFTA.LiteralFilterKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)

private def captures : List (Value Nat Bool) := [.reference (.uninterned 0)]
private def nodeA : Syntax Nat Bool := .node [.mk 1 false []]
private def nodeB : Syntax Nat Bool := .node [.mk 2 true []]
private def expression : Syntax Nat Bool := .node [.mk 9 true [
  .union [.var 0,nodeA,nodeB], .union [.union [nodeA,nodeB],.var 0]]]
private def built := build expression captures empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def first : Value Nat Bool := ((children root)[0]?).getD .empty
private def second : Value Nat Bool := ((children root)[1]?).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × List (Value Nat Bool) × Nat × List Reference
  | .union entry rows level free => (entry,rows,level,free)
  | _ => (⟨0,.union []⟩,[],0,[])
private theorem actual : built = .done root heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  have same : value = .reference (.uninterned 0) := List.mem_singleton.mp member
  cases same
  exact InternedNestedProvenance.ordinary_available empty 0
private theorem ready : Ready heap := by
  have context := SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures inputs
  refine ⟨SourceRecursiveIntersectionSemanticHeap.source expression captures empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs,
    InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid
      InternedRecordCoherence.empty_correct.2 root heap actual,?_⟩
  exact (InternedOpenDepthExecution.build_depth expression captures empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedOpenDepthReadback.empty_heap).heap
private theorem available : Available heap first ∧ Available heap second := by
  have result := (InternedFreshOrdinaryFacts.build_verified expression captures empty InternedNestedFacts.empty_facts inputs).result root heap actual
  exact ⟨result.children first (by cbv; exact .head _), result.children second (by cbv; exact .tail _ (.head _))⟩
private def bare : Value Nat Bool := .reference (.uninterned 0)
private def a : Value Nat Bool := ((fields first).2.1)[1]?.getD .empty
private def b : Value Nat Bool := ((fields first).2.1)[2]?.getD .empty
private def ab : Value Nat Bool := ((fields second).2.1)[0]?.getD .empty
private theorem aAvailable : Available heap a :=
  available.1.children a (List.mem_of_getElem? (show (children first)[1]? = some a by cbv))
private theorem bAvailable : Available heap b :=
  available.1.children b (List.mem_of_getElem? (show (children first)[2]? = some b by cbv))
private theorem abAvailable : Available heap ab :=
  available.2.children ab (List.mem_of_getElem? (show (children second)[0]? = some ab by cbv))
private theorem bareAvailable : Available heap bare := InternedNestedProvenance.ordinary_available heap 0
private theorem firstInputs : Values heap [bare,a,b] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact bareAvailable
  · exact aAvailable
  · exact bAvailable
private theorem secondInputs : Values heap [ab,bare] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact abAvailable
  · exact bareAvailable
private theorem groupedInputs : Values heap [a,b] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact aAvailable
  · exact bAvailable
private theorem firstWarm : run (makeUnion [bare,a,b]) heap = (first,heap) := by cbv
private theorem secondWarm : run (makeUnion [ab,bare]) heap = (second,heap) := by cbv
private theorem groupedWarm : run (makeUnion [a,b]) heap = (ab,heap) := by cbv
private theorem parts : SourceCurrentLiteralRootParts.SameParts first second := by
  constructor
  · intro atom
    have firstParts := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts [bare,a,b] firstInputs atom
    have secondParts := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts [ab,bare] secondInputs atom
    have grouped := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts [a,b] groupedInputs atom
    rw [firstWarm] at firstParts
    rw [secondWarm] at secondParts
    rw [groupedWarm] at grouped
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_and_right,exists_or,exists_eq_left] at firstParts secondParts grouped
    exact firstParts.trans (or_comm.trans ((or_congr grouped Iff.rfl).symm.trans secondParts.symm))
  · intro row
    have firstParts := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live [bare,a,b] firstInputs row
    have secondParts := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live [ab,bare] secondInputs row
    have grouped := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live [a,b] groupedInputs row
    rw [firstWarm] at firstParts
    rw [secondWarm] at secondParts
    rw [groupedWarm] at grouped
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_and_right,exists_or,exists_eq_left] at firstParts secondParts grouped
    exact firstParts.trans (or_comm.trans ((or_congr grouped Iff.rfl).symm.trans secondParts.symm))

/-- Actual grouped source unions lose self while bare self remains unchanged, with exact full row parts retained. -/
theorem grouped_self_filter :
    build expression captures empty = .done root heap ∧ Ready heap ∧ first ≠ second ∧
    SourceCurrentLiteralRootParts.SameParts first second ∧
    SourceCurrentLiteralRootParts.Literal first bare ∧
    SourceCurrentLiteralRootParts.SameParts
      (run (withoutSelfReference (.uninterned 0) first) heap).1
      (run (withoutSelfReference (.uninterned 0) second) heap).1 ∧
    ¬ SourceCurrentLiteralRootParts.Literal (run (withoutSelfReference (.uninterned 0) first) heap).1 bare ∧
    run (withoutSelfReference (.uninterned 0) bare) heap = (bare,heap) := by
  have filtered := SourceCurrentLiteralFilterParts.congr heap heap ready.semantic.1.normal ready.semantic.1.normal
    (.uninterned 0) first second available.1 available.2 parts.1 parts.2
  have firstSelf : SourceCurrentLiteralRootParts.Literal first bare := by
    have exposed := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts [bare,a,b] firstInputs bare
    rw [firstWarm] at exposed
    exact exposed.mpr ⟨bare,List.mem_cons_self,by constructor⟩
  refine ⟨actual,ready,?_,parts,firstSelf,filtered,?_,rfl⟩
  · intro same
    have ids := congrArg Value.referenceOf same
    cbv at ids
    contradiction
  · intro present
    have condition := (SourceCurrentLiteralFilterParts.literal heap ready.semantic.1.normal (.uninterned 0)
      first available.1 bare).mp present
    rcases condition.2 with impossible | different
    · have distinct : first ≠ bare := by intro same; have ids := congrArg Value.referenceOf same; cbv at ids; contradiction
      exact distinct impossible
    · exact different rfl

end MicroCFTA.LiteralFilterKernels

#check @MicroCFTA.LiteralFilterKernels.grouped_self_filter
#print axioms MicroCFTA.LiteralFilterKernels.grouped_self_filter
