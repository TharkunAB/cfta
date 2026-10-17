import MicroCFTA.SourceCurrentLiteralUnionParts
import MicroCFTA.SourceEqualityRequiredCache
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
namespace MicroCFTA.LiteralUnionPartsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentLiteralRootParts (Literal Row)
private def captures : List (Value Nat Bool) := [.reference (.uninterned 0),.reference (.uninterned 1)]
private def expression : Syntax Nat Bool := .node [.mk 9 true [
  .binder false (.var 1),.var 1,.node [.mk 5 false []],.node [.mk 6 true []]]]
private def built := build expression captures empty
private def source : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def mu : Value Nat Bool := ((children source)[0]?).getD .empty
private def first : Value Nat Bool := ((children source)[2]?).getD .empty
private def second : Value Nat Bool := ((children source)[3]?).getD .empty
private def mixed : List (Value Nat Bool) := [.empty,mu,.reference (.uninterned 1),first,mu]
private def ordinary : List (Value Nat Bool) := [first,second,first]
private def normalized := run (makeUnion mixed) heap
private def merged := run (makeUnion ordinary) heap
private theorem actual : built = .done source heap := by cbv
private theorem inputs : Values (empty : State Nat Bool) captures := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact InternedNestedProvenance.ordinary_available empty 0
  · have same : value = .reference (.uninterned 1) := List.mem_singleton.mp member
    cases same
    exact InternedNestedProvenance.ordinary_available empty 1
private theorem ready : Ready heap := by
  have context := SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures inputs
  refine ⟨SourceRecursiveIntersectionSemanticHeap.source expression captures empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs,
    InternedFreshOrdinaryCoverage.build_covered expression captures empty empty_valid
      InternedRecordCoherence.empty_correct.2 source heap actual,?_⟩
  exact (InternedOpenDepthExecution.build_depth expression captures empty context
    InternedFreshOrdinaryDepthHeap.empty_heap InternedOpenDepthReadback.empty_heap).heap
private theorem available : Available heap mu ∧ Available heap first ∧ Available heap second := by
  have output := (InternedFreshOrdinaryFacts.build_verified expression captures empty InternedNestedFacts.empty_facts inputs).result source heap actual
  exact ⟨output.children mu (by cbv; exact .head _),
    output.children first (by cbv; exact .tail _ (.tail _ (.head _))),
    output.children second (by cbv; exact .tail _ (.tail _ (.tail _ (.head _))))⟩
private theorem mixedAvailable : Values heap mixed := by
  intro value member
  simp only [mixed,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact empty_available heap
  · exact available.1
  · exact InternedNestedProvenance.ordinary_available heap 1
  · exact available.2.1
  · exact available.1
private theorem ordinaryAvailable : Values heap ordinary := by
  intro value member
  simp only [ordinary,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact available.2.1
  · exact available.2.2
  · exact available.2.1

private def rowA : EdgeValue Nat Bool := .mk ⟨0,⟨5,[],false⟩⟩ []
private def rowB : EdgeValue Nat Bool := .mk ⟨1,⟨6,[],true⟩⟩ []
private theorem muShape : ∃ entry, mu = .mu entry (.reference (.uninterned 0))
    (.reference (.uninterned 0)) (.reference (.uninterned 0)) := by
  refine ⟨⟨0,muKey (.reference (.uninterned 0) : Value Nat Bool) (.reference (.uninterned 0))⟩,?_⟩
  cbv
private theorem firstShape : ∃ entry, first = .node entry [rowA] 0 [] := by
  refine ⟨⟨1,.node [0]⟩,?_⟩
  cbv
private theorem secondShape : ∃ entry, second = .node entry [rowB] 0 [] := by
  refine ⟨⟨2,.node [1]⟩,?_⟩
  cbv
private theorem muLiteral : Literal mu mu := by
  obtain ⟨entry,shape⟩ := muShape
  rw [shape]
  constructor
private theorem firstRow : Row first rowA := by
  obtain ⟨entry,shape⟩ := firstShape
  rw [shape]
  exact (SourceCurrentLiteralRootParts.row_node entry [rowA] 0 [] rowA).mpr List.mem_cons_self
private theorem secondRow : Row second rowB := by
  obtain ⟨entry,shape⟩ := secondShape
  rw [shape]
  exact (SourceCurrentLiteralRootParts.row_node entry [rowB] 0 [] rowB).mpr List.mem_cons_self
private theorem capturedMissing : ¬ ∃ value ∈ mixed, Literal value (.reference (.uninterned 0)) := by
  rintro ⟨value,present,part⟩
  simp only [mixed,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl
  · cases part
  · obtain ⟨entry,shape⟩ := muShape
    rw [shape] at part
    cases part
  · cases part
  · obtain ⟨entry,shape⟩ := firstShape
    rw [shape] at part
    cases part
  · obtain ⟨entry,shape⟩ := muShape
    rw [shape] at part
    cases part
private theorem ordinaryMissing (atom : Value Nat Bool) : ¬ ∃ value ∈ ordinary, Literal value atom := by
  rintro ⟨value,present,part⟩
  simp only [ordinary,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  · obtain ⟨entry,shape⟩ := firstShape
    rw [shape] at part
    cases part
  · obtain ⟨entry,shape⟩ := secondShape
    rw [shape] at part
    cases part
  · obtain ⟨entry,shape⟩ := firstShape
    rw [shape] at part
    cases part
private theorem mixed_and_ordinary_proof :
    build expression captures empty = .done source heap ∧ Ready heap ∧
    Values heap mixed ∧ Values heap ordinary ∧
    run (makeUnion mixed) heap = normalized ∧ run (makeUnion ordinary) heap = merged ∧
    (∀ atom, Literal normalized.1 atom ↔ ∃ value ∈ mixed, Literal value atom) ∧
    (∀ row, Row normalized.1 row ↔ ∃ value ∈ mixed, Row value row) ∧
    Literal normalized.1 mu ∧ Literal normalized.1 (.reference (.uninterned 1)) ∧
    ¬ Literal normalized.1 (.reference (.uninterned 0)) ∧ Row normalized.1 rowA ∧
    Row merged.1 rowA ∧ Row merged.1 rowB ∧ (∀ atom, ¬ Literal merged.1 atom) ∧
    rowA.entry.key.constraint = false ∧ rowB.entry.key.constraint = true := by
  have literal := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts mixed mixedAvailable
  have rows := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live mixed mixedAvailable
  have otherLiteral := SourceCurrentLiteralUnionParts.literal heap ready.semantic.1.normal.facts ordinary ordinaryAvailable
  have otherRows := SourceCurrentLiteralUnionParts.row heap ready.semantic.1.normal.facts ready.semantic.1.normal.live ordinary ordinaryAvailable
  refine ⟨actual,ready,mixedAvailable,ordinaryAvailable,rfl,rfl,literal,rows,?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · exact (literal mu).mpr ⟨mu,by exact List.mem_cons_of_mem _ List.mem_cons_self,muLiteral⟩
  · apply (literal (.reference (.uninterned 1))).mpr
    refine ⟨.reference (.uninterned 1),?_,?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · constructor
  · exact fun found => capturedMissing ((literal _).mp found)
  · exact (rows rowA).mpr ⟨first,by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),firstRow⟩
  · exact (otherRows rowA).mpr ⟨first,List.mem_cons_self,firstRow⟩
  · exact (otherRows rowB).mpr ⟨second,List.mem_cons_of_mem _ List.mem_cons_self,secondRow⟩
  · exact fun atom found => ordinaryMissing atom ((otherLiteral atom).mp found)
/-- Actual mixed and ordinary union calls retain complete literals and guarded rows while a Mu-exposed reference remains nonliteral. -/
theorem mixed_and_ordinary :
    build expression captures empty = .done source heap ∧ Ready heap ∧
    Values heap mixed ∧ Values heap ordinary ∧
    run (makeUnion mixed) heap = normalized ∧ run (makeUnion ordinary) heap = merged ∧
    (∀ atom, Literal normalized.1 atom ↔ ∃ value ∈ mixed, Literal value atom) ∧
    (∀ row, Row normalized.1 row ↔ ∃ value ∈ mixed, Row value row) ∧
    Literal normalized.1 mu ∧ Literal normalized.1 (.reference (.uninterned 1)) ∧
    ¬ Literal normalized.1 (.reference (.uninterned 0)) ∧ Row normalized.1 rowA ∧
    Row merged.1 rowA ∧ Row merged.1 rowB ∧ (∀ atom, ¬ Literal merged.1 atom) ∧
    rowA.entry.key.constraint = false ∧ rowB.entry.key.constraint = true := mixed_and_ordinary_proof
end MicroCFTA.LiteralUnionPartsKernels
#check @MicroCFTA.LiteralUnionPartsKernels.mixed_and_ordinary
#print MicroCFTA.LiteralUnionPartsKernels.mixed_and_ordinary
#print axioms MicroCFTA.LiteralUnionPartsKernels.mixed_and_ordinary
