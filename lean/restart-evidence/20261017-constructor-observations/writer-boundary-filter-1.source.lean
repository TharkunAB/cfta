import MicroCFTA.SourceCurrentOpenObservationLists
import MicroCFTA.SourceCurrentOpenObservationConstructors
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
import MicroCFTA.SourceCurrentStoredReconstruction

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

namespace MicroCFTA.WriterFilterBoundary
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenObservations
open SourceCurrentOpenObservationConstructors
open SourceCurrentOpenObservationLists

private def name : Reference := .uninterned 0
private def expression : Syntax Nat Bool := .node [.mk 9 false
  [.node [.mk 0 false [.var 0]], .node [.mk 1 true [.var 0]],
   .binder false .empty, .binder false (.var 1)]]
private def inputs : List (Value Nat Bool) := [.reference name]
private def children : Value Nat Bool → List (Value Nat Bool)
  | .node _ (.mk _ values :: _) _ _ => values
  | _ => []
private def built := build expression inputs empty
private def source : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def a : Value Nat Bool := (children source)[0]?.getD Value.empty
private def b : Value Nat Bool := (children source)[1]?.getD Value.empty
private def closedMu : Value Nat Bool := (children source)[2]?.getD Value.empty
private def openMu : Value Nat Bool := (children source)[3]?.getD Value.empty
private def ab := run (makeUnion [a,b]) heap
private def firstRoots := [.reference name,a,b,closedMu]
private def first := run (makeUnion firstRoots) ab.2
private def secondRoots := [openMu,ab.1,closedMu]
private def second := run (makeUnion secondRoots) first.2
private def firstFiltered := run (withoutSelfReference name first.1) second.2
private def secondFiltered := run (withoutSelfReference name second.1) firstFiltered.2
private theorem built_done : built = .done source heap := by cbv
private theorem empty_ready : Ready (empty : State Nat Bool) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty (by rw [build])
private theorem inputs_available : Values (empty : State Nat Bool) inputs := by
  intro value member
  simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at member
  subst value
  apply reference_available
  all_goals intro identity impossible; simp [Value.free] at impossible

private theorem source_ready : Ready heap := by
  let context := SourceRecursiveIntersectionSemanticHeap.context empty empty_ready.semantic inputs inputs_available
  have actual : build expression inputs empty = .done source heap := built_done
  refine ⟨?_,?_,?_⟩
  · simpa only [actual,Outcome.state] using
      SourceRecursiveIntersectionSemanticHeap.source expression inputs empty empty_ready.semantic inputs_available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs empty context.normal.facts.coherent.valid
      empty_ready.covered source heap built_done
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs empty context empty_ready.semantic.2 empty_ready.depth).heap

private theorem source_available : Available heap source :=
  (InternedFreshOrdinaryFacts.build_verified expression inputs empty empty_ready.semantic.1.normal.facts inputs_available).result
    source heap built_done

private theorem child_available (state : State Nat Bool) (value : Value Nat Bool) (available : Available state value) :
    Values state (children value) := by
  cases value <;> try (intro child impossible; cases impossible)
  case node entry rows level free =>
    cases rows with
    | nil => intro child impossible; cases impossible
    | cons row rest =>
        cases row with
        | mk edge values =>
            intro child member
            exact available.children child (List.mem_flatMap.mpr ⟨.mk edge values,List.mem_cons_self,member⟩)
private theorem source_member (index : Nat) (value : Value Nat Bool)
    (found : (children source)[index]? = some value) : Available heap value :=
  child_available heap source source_available value (List.mem_of_getElem? found)
private theorem a_available : Available heap a := source_member 0 a (by cbv)
private theorem b_available : Available heap b := source_member 1 b (by cbv)
private theorem closed_available : Available heap closedMu := source_member 2 closedMu (by cbv)
private theorem open_available : Available heap openMu := source_member 3 openMu (by cbv)
private theorem name_available : Available heap (.reference name) := by
  apply reference_available
  intro identity member
  simp [Value.free,name] at member
private theorem ab_data : Keeps heap ab.2 ∧ Available ab.2 ab.1 :=
  SourceEqualityNativeDemandHeapPrimitives.union [a,b] heap source_ready (by
    intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact a_available
    · exact b_available)
private theorem first_available : Values ab.2 firstRoots := by
  intro value member
  simp only [firstRoots,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ab_data.1.available _ name_available
  · exact ab_data.1.available _ a_available
  · exact ab_data.1.available _ b_available
  · exact ab_data.1.available _ closed_available
private theorem first_data : Keeps ab.2 first.2 ∧ Available first.2 first.1 :=
  SourceEqualityNativeDemandHeapPrimitives.union firstRoots ab.2 ab_data.1.ready first_available
private theorem second_available : Values first.2 secondRoots := by
  intro value member
  simp only [secondRoots,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact first_data.1.available _ (ab_data.1.available _ open_available)
  · exact first_data.1.available _ ab_data.2
  · exact first_data.1.available _ (ab_data.1.available _ closed_available)
private theorem second_data : Keeps first.2 second.2 ∧ Available second.2 second.1 :=
  SourceEqualityNativeDemandHeapPrimitives.union secondRoots first.2 first_data.1.ready second_available

private theorem closed_same (depth : Nat) (view : State Nat Bool) : Same depth view [closedMu] [Value.empty] := by
  exact SourceCurrentOpenObservations.unfold depth view _ _ _ _ .empty view (by cbv)
private theorem open_same (depth : Nat) (view : State Nat Bool) : Same depth view [openMu] [.reference name] := by
  exact SourceCurrentOpenObservations.unfold depth view _ _ _ _ (.reference name) view (by cbv)
private theorem before_same (depth : Nat) (view : State Nat Bool) : Same depth view [first.1] [second.1] := by
  have firstNormalized := makeUnion_normalize depth ab.2 view ab_data.1.ready.semantic.1.normal.facts
    ab_data.1.ready.semantic.1.normal.live firstRoots first_available
  have secondNormalized := makeUnion_normalize depth first.2 view first_data.1.ready.semantic.1.normal.facts
    first_data.1.ready.semantic.1.normal.live secondRoots second_available
  have merged := (makeUnion_normalize depth heap view source_ready.semantic.1.normal.facts
    source_ready.semantic.1.normal.live [a,b] (by
      intro value member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact a_available
      · exact b_available)).symm
  have front := SourceCurrentOpenObservationLists.append depth view _ _ _ _ (open_same depth view).symm merged
  have roots : Same depth view firstRoots secondRoots :=
    SourceCurrentOpenObservationLists.append depth view _ _ _ _ front (Same.refl depth view [closedMu])
  exact firstNormalized.trans (roots.trans secondNormalized.symm)

private theorem empty_no_reference (view : State Nat Bool) (other : Reference) :
    ¬ ReferenceOrigin view [Value.empty] other := by
  rw [reference_expand view .empty (by intro marker impossible; cases impossible) other]
  change ¬ ReferenceOrigin view [] other
  rw [reference_seeds]
  rintro ⟨_,impossible,_⟩; cases impossible
private theorem node_no_reference (view : State Nat Bool) (entry : Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Nat Bool)) (level : Nat) (free : List Reference) (other : Reference) :
    ¬ ReferenceOrigin view [.node entry rows level free] other := by
  rw [reference_expand view _ (by intro marker impossible; cases impossible) other]
  change ¬ ReferenceOrigin view [] other
  rw [reference_seeds]
  rintro ⟨_,impossible,_⟩; cases impossible
private theorem filtered_first : firstFiltered = run (makeUnion [a,b,closedMu]) second.2 := by cbv
private theorem filtered_second : secondFiltered = (second.1,firstFiltered.2) := by cbv
private theorem remaining_available : Values second.2 [a,b,closedMu] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have kept := ab_data.1.trans (first_data.1.trans second_data.1)
  rcases member with rfl | rfl | rfl
  · exact kept.available _ a_available
  · exact kept.available _ b_available
  · exact kept.available _ closed_available
private theorem after_not_same (view : State Nat Bool) :
    ¬ Same 0 view [firstFiltered.1] [secondFiltered.1] := by
  intro same
  have secondReference : ReferenceOrigin view [second.1] name := by
    have normalized := makeUnion_normalize 0 first.2 view first_data.1.ready.semantic.1.normal.facts
      first_data.1.ready.semantic.1.normal.live secondRoots second_available
    apply (normalized name).mpr
    apply (reference_seeds view secondRoots name).mpr
    exact ⟨openMu,by simp [secondRoots],(open_same 0 view name).mpr ((reference_exact view name name).mpr rfl)⟩
  have firstReference := (same name).mpr (by simpa only [filtered_second] using secondReference)
  rw [filtered_first] at firstReference
  have normalized := makeUnion_normalize 0 second.2 view second_data.1.ready.semantic.1.normal.facts
    second_data.1.ready.semantic.1.normal.live [a,b,closedMu] remaining_available
  have roots := (normalized name).mp firstReference
  obtain ⟨value,member,actual⟩ := (reference_seeds view [a,b,closedMu] name).mp roots
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact node_no_reference view _ _ _ _ name actual
  · exact node_no_reference view _ _ _ _ name actual
  · exact empty_no_reference view name ((closed_same 0 view name).mp actual)

/-- Root observations and aggregate metadata do not make actual self filtering congruent. -/
theorem actual_filter_boundary (view : State Nat Bool) (depth : Nat) :
    build expression inputs empty = .done source heap ∧ Ready second.2 ∧
    Available second.2 first.1 ∧ Available second.2 second.1 ∧
    Same depth view [first.1] [second.1] ∧
    first.1.referenceOf ≠ .empty ∧ second.1.referenceOf ≠ .empty ∧
    first.1.free = second.1.free ∧
    InternedDeepFreeDepth.deepNames first.1 = InternedDeepFreeDepth.deepNames second.1 ∧
    first.1.depth = second.1.depth ∧
    (∀ marker, first.1 ≠ .reference marker ∧ second.1 ≠ .reference marker) ∧
    ¬ Same 0 view [firstFiltered.1] [secondFiltered.1] := by
  refine ⟨built_done,second_data.1.ready,second_data.1.available _ first_data.2,second_data.2,
    before_same depth view,?_,?_,?_,?_,?_,?_,after_not_same view⟩
  all_goals cbv <;> simp

#check @actual_filter_boundary
#print axioms actual_filter_boundary
end MicroCFTA.WriterFilterBoundary
