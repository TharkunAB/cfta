import MicroCFTA.SourceCurrentOpenObservationConstructors
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
namespace MicroCFTA.ObservationConstructorsKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentOpenObservations
open Productivity Language
private def expression : Syntax Nat Bool := .binder false (.node [.mk 1 false [.var 0]])
private def built := build expression [] empty
private def muValue : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem actual : built = .done muValue heap := by cbv
private theorem ready : SourceEqualityRequiredCache.Ready heap :=
  SourceEqualityRequiredCache.constructed expression muValue heap actual
private theorem available : Available heap muValue :=
  (InternedFreshOrdinaryFacts.build_verified expression [] empty InternedNestedFacts.empty_facts
    (by intro _ member; cases member)).result muValue heap actual
private def firstCall := run (InternedConstructorTemplates.makeEdge 7 false [muValue,.reference .depth]) heap
private def firstRow := firstCall.1
private def secondCall := run (InternedConstructorTemplates.makeEdge 8 true [muValue]) firstCall.2
private def secondRow := secondCall.1
private def current := secondCall.2
private def firstRows := [firstRow,secondRow,firstRow]
private def secondRows := [secondRow,firstRow]
private def values : List (Value Nat Bool) := [muValue,muValue,.empty,.reference .depth]
private theorem row_match (row : EdgeValue Nat Bool) :
    RowMatch (fun left right => Same 1 current [left] [right]) row row := by
  refine ⟨rfl,rfl,?_⟩
  have all (children : List (Value Nat Bool)) : All₂ (fun left right => Same 1 current [left] [right]) children children := by
    induction children with
    | nil => exact .nil
    | cons child children ih => exact .cons (Same.refl 1 current [child]) ih
  exact all row.children
private theorem normalization_proof :
    build expression [] empty = .done muValue heap ∧
    firstRow.entry.key.constraint = false ∧
    Same 2 current [(run (InternedConstructorTemplates.makeNode firstRows) current).1]
      [(run (InternedConstructorTemplates.makeNode secondRows) current).1] ∧
    Same 2 current [(run (InternedConstructorTemplates.makeUnion values) current).1] values ∧
    ReferenceOrigin current [(run (InternedConstructorTemplates.makeUnion values) current).1] .depth := by
  have firstInputs : Values heap [muValue,.reference .depth] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact available
    · cases List.mem_singleton.mp later
      exact InternedNestedProvenance.depth_available heap
  have first := SourceEqualityRequiredCache.edge 7 false [muValue,.reference .depth] heap ready firstInputs
  have secondInputs : Values firstCall.2 [muValue] := by
    intro value member
    cases List.mem_singleton.mp member
    exact first.1.available muValue available
  have second := SourceEqualityRequiredCache.edge 8 true [muValue] firstCall.2 first.1.ready secondInputs
  have currentReady : SourceEqualityRequiredCache.Ready current := second.1.ready
  have resident1 : EdgeResident current firstRow := edge_grows firstCall.2 current second.1.growth firstRow first.2.1
  have resident2 : EdgeResident current secondRow := second.2.1
  have firstResident : Edges current firstRows := by
    intro row member
    simp only [firstRows,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact resident1
    · exact resident2
    · exact resident1
  have secondResident : Edges current secondRows := by
    intro row member
    simp only [secondRows,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact resident2
    · exact resident1
  have surviveFirst : surviving firstRows = firstRows := by cbv
  have surviveSecond : surviving secondRows = secondRows := by cbv
  have nodeSame := SourceCurrentOpenObservationConstructors.makeNode 1 current current current firstRows secondRows
    currentReady.semantic.1.normal.facts currentReady.semantic.1.normal.facts firstResident secondResident
    (by
      intro row member
      rw [surviveFirst] at member
      rw [surviveSecond]
      refine ⟨row,?_,row_match row⟩
      simp only [firstRows,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [secondRows])
    (by
      intro row member
      rw [surviveSecond] at member
      rw [surviveFirst]
      refine ⟨row,?_,row_match row⟩
      simp only [secondRows,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> simp [firstRows])
  have allAvailable : Values current values := by
    intro value member
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact second.1.available muValue (first.1.available muValue available)
    · exact second.1.available muValue (first.1.available muValue available)
    · exact InternedProbeProvenance.empty_available current
    · exact InternedNestedProvenance.depth_available current
  have unionSame := SourceCurrentOpenObservationConstructors.makeUnion_normalize 2 current current
    currentReady.semantic.1.normal.facts currentReady.semantic.1.normal.live values allAvailable
  have refHere : ReferenceOrigin current values .depth := .seed (by simp [values])
  exact ⟨actual,by cbv,nodeSame,unionSame,(unionSame.1 .depth).mpr refHere⟩
/-- Actual duplicate and reordered rows and a Mu/reference union retain one common-view observation. -/
theorem normalization :
    build expression [] empty = .done muValue heap ∧
    firstRow.entry.key.constraint = false ∧
    Same 2 current [(run (InternedConstructorTemplates.makeNode firstRows) current).1]
      [(run (InternedConstructorTemplates.makeNode secondRows) current).1] ∧
    Same 2 current [(run (InternedConstructorTemplates.makeUnion values) current).1] values ∧
    ReferenceOrigin current [(run (InternedConstructorTemplates.makeUnion values) current).1] .depth := normalization_proof

private def leafEdge := run (InternedConstructorTemplates.makeEdge (0:Nat) true []) (empty : State Nat Bool)
private def leafCall := run (InternedConstructorTemplates.makeNode [leafEdge.1]) leafEdge.2
private def deadEdge := run (InternedConstructorTemplates.makeEdge 1 true [.empty]) leafCall.2
private def liveEdge := run (InternedConstructorTemplates.makeEdge 1 true [leafCall.1]) deadEdge.2
private def boundaryView := liveEdge.2
private def deadParent := (run (InternedConstructorTemplates.makeNode [deadEdge.1]) boundaryView).1
private def liveParent := (run (InternedConstructorTemplates.makeNode [liveEdge.1]) boundaryView).1
private theorem no_reference (value : Value Nat Bool) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (name : InternedBinderProtocol.Reference) : ¬ ReferenceOrigin boundaryView [value] name := by
  have different : ∀ name, value ≠ .reference name := by cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary]
  have terminal : MergedFreshOrdinaryGraph.successors boundaryView value = [] := by
    cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary,MergedFreshOrdinaryGraph.successors]
  rw [reference_expand boundaryView value different name,terminal,reference_seeds]
  rintro ⟨_,h,_⟩
  cases h
private theorem empty_boundary_proof :
    Same 0 boundaryView [.empty] [leafCall.1] ∧
      surviving [deadEdge.1] = [] ∧ surviving [liveEdge.1] = [liveEdge.1] ∧
      ¬ Same 1 boundaryView [deadParent] [liveParent] := by
  have same : Same 0 boundaryView [.empty] [leafCall.1] :=
    fun name => iff_of_false (no_reference .empty trivial name) (no_reference leafCall.1 (by cbv) name)
  refine ⟨same,by cbv,by cbv,?_⟩
  intro related
  have origin : MergedFreshOrdinaryGraph.Origin boundaryView [liveParent] liveEdge.1 := by
    refine ⟨liveParent,.seed List.mem_cons_self,?_⟩
    cbv
    exact .head _
  obtain ⟨row,present,_⟩ := related.2.2 liveEdge.1 origin
  have emptyParent : deadParent = .empty := by cbv
  rw [emptyParent] at present
  exact MergedFreshOrdinaryGraph.origin_empty boundaryView row present
/-- Depth-zero observations do not justify removal of the actual node survival premise. -/
theorem empty_boundary :
    Same 0 boundaryView [.empty] [leafCall.1] ∧
      surviving [deadEdge.1] = [] ∧ surviving [liveEdge.1] = [liveEdge.1] ∧
      ¬ Same 1 boundaryView [deadParent] [liveParent] := empty_boundary_proof
end MicroCFTA.ObservationConstructorsKernels
#check @MicroCFTA.ObservationConstructorsKernels.normalization
#print MicroCFTA.ObservationConstructorsKernels.normalization
#print axioms MicroCFTA.ObservationConstructorsKernels.normalization
#check @MicroCFTA.ObservationConstructorsKernels.empty_boundary
#print MicroCFTA.ObservationConstructorsKernels.empty_boundary
#print axioms MicroCFTA.ObservationConstructorsKernels.empty_boundary
