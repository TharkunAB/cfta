import MicroCFTA.SourceCurrentStoredMuRetainedAlignment

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MuRetainedAlignmentKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedFreshOrdinaryContext
open SourceCurrentStoredMuRetainedAlignment

private def rows : List (EdgeSyntax Nat Bool) :=
  [.mk 7 true [.binder true (.node [.mk 8 false [.var 1,.var 0]]),.var 0],
   .mk 7 false [.empty,.var 0]]
private def first := buildEdges rows [.reference (.uninterned 0)] empty
private def firstValues := match first with | .done values _ => values | .pending .. => []
private def firstHeap := first.state
private def second := buildEdges rows [.reference (.uninterned 9)] firstHeap
private def secondValues := match second with | .done values _ => values | .pending .. => []
private def secondHeap := second.state

private theorem firstActual : first = .done firstValues firstHeap := by cbv
private theorem secondActual : second = .done secondValues secondHeap := by cbv
private theorem firstContext : Context (empty : State Nat Bool) [.reference (.uninterned 0)] :=
  empty_context.local (.uninterned 0) (InternedNestedProvenance.ordinary_available _ _)
private theorem secondContext : Context firstHeap [.reference (.uninterned 9)] := by
  have reached : Context firstHeap [.reference (.uninterned 0)] := by
    exact firstContext.edges rows
  refine ⟨reached.normal,?_,reached.profiles,reached.freeNames⟩
  intro value member
  cases List.mem_singleton.mp member
  exact InternedNestedProvenance.ordinary_available _ _

/-- Two initial source executions retain a used nested Mu and the same live and dead row occurrences. -/
theorem nested_used_and_dead_row :
    first = .done firstValues firstHeap ∧ second = .done secondValues secondHeap ∧
    ∃ (left : RowCall rows [.reference (.uninterned 0)] empty firstValues firstHeap secondHeap 0 7 true
        [.binder true (.node [.mk 8 false [.var 1,.var 0]]),.var 0])
      (right : RowCall rows [.reference (.uninterned 9)] firstHeap secondValues secondHeap secondHeap 0 7 true
        [.binder true (.node [.mk 8 false [.var 1,.var 0]]),.var 0])
      (deadLeft : RowCall rows [.reference (.uninterned 0)] empty firstValues firstHeap secondHeap 1 7 false [.empty,.var 0])
      (deadRight : RowCall rows [.reference (.uninterned 9)] firstHeap secondValues secondHeap secondHeap 1 7 false [.empty,.var 0]),
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) left.values right.values ∧
      left.output.children.any (fun value => value.referenceOf == .empty) = false ∧
      right.output.children.any (fun value => value.referenceOf == .empty) = false ∧
      deadLeft.output.children.any (fun value => value.referenceOf == .empty) = true ∧
      deadRight.output.children.any (fun value => value.referenceOf == .empty) = true ∧
      (match left.values[0]? with | some (.mu ..) => true | _ => false) = true := by
  have checked := InternedFreshOrdinaryFacts.buildEdges_verified rows _ firstHeap secondContext.normal.facts secondContext.inputs
  have growth : Grows firstHeap secondHeap := checked.growth
  obtain ⟨left,right,paired,survival⟩ := paired_rows rows [] (.uninterned 0) (.uninterned 9)
    empty firstHeap firstHeap secondHeap secondHeap firstContext secondContext firstValues secondValues
    firstActual secondActual growth (grows_refl _) 0 7 true _ rfl
  obtain ⟨deadLeft,deadRight,_,deadSurvival⟩ := paired_rows rows [] (.uninterned 0) (.uninterned 9)
    empty firstHeap firstHeap secondHeap secondHeap firstContext secondContext firstValues secondValues
    firstActual secondActual growth (grows_refl _) 1 7 false _ rfl
  have live : left.output.children.any (fun value => value.referenceOf == .empty) = false := by
    have known : ((firstValues[0]?).map (fun row => row.children.any (fun value => value.referenceOf == .empty))).getD false = false := by cbv
    simpa only [left.selected,Option.map_some,Option.getD_some] using known
  have dead : deadLeft.output.children.any (fun value => value.referenceOf == .empty) = true := by
    have known : ((firstValues[1]?).map (fun row => row.children.any (fun value => value.referenceOf == .empty))).getD false = true := by cbv
    simpa only [deadLeft.selected,Option.map_some,Option.getD_some] using known
  have nested : (match left.values[0]? with | some (.mu ..) => true | _ => false) = true := by
    have known : ((firstValues[0]?).map (fun row => match row.children[0]? with | some (.mu ..) => true | _ => false)).getD false = true := by cbv
    simpa only [left.selected,Option.map_some,Option.getD_some,left.children_eq] using known
  exact ⟨firstActual,secondActual,left,right,deadLeft,deadRight,paired,live,survival ▸ live,dead,deadSurvival ▸ dead,nested⟩

end MicroCFTA.MuRetainedAlignmentKernels

#check @MicroCFTA.MuRetainedAlignmentKernels.nested_used_and_dead_row
#print axioms MicroCFTA.MuRetainedAlignmentKernels.nested_used_and_dead_row
