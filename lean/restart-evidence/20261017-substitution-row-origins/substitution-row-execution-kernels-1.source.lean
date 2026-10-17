import MicroCFTA.SourceCurrentSubstitutionRowExecution
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
namespace MicroCFTA.SubstitutionRowExecutionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open InternedStoredSubstitution (encode encodeEdges)
open InternedFreshOrdinaryConstruction
open SourceCurrentSubstitutionRowExecution
open InternedBinderProtocol (Reference)
local notation "Node" => Value Nat Bool
local notation "Edge" => EdgeValue Nat Bool
private def firstName : Reference := .uninterned 0
private def secondName : Reference := .uninterned 1
private def context : List Node := [.reference firstName,.reference secondName]
private def expression : Syntax Nat Bool := .node [.mk 10 true [
  .node [.mk 11 false []],.node [.mk 12 true []],.node [.mk 13 false [.var 0,.var 1]]]]
private def built := build expression context empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def before := built.state
private def left : Node := ((children root)[0]?).getD .empty
private def right : Node := ((children root)[1]?).getD .empty
private def original : Node := ((children root)[2]?).getD .empty
private def originals : List Edge := nodeEdges original
private def fallback : Edge := .mk ⟨0,⟨0,[],false⟩⟩ []
private def sourceRow : Edge := (originals[0]?).getD fallback
private def inputs : List Node := [right,left]
private def rebuilt := buildEdges (encodeEdges context [] originals) inputs before
private def outputs : List Edge := match rebuilt with | .done rows _ => rows | .pending .. => []
private def after := rebuilt.state
private def output : Edge := (outputs[0]?).getD fallback
private theorem constructed : built = .done root before := by cbv
private theorem rowDone : rebuilt = .done outputs after := by cbv
private theorem sourceFound : originals[0]? = some sourceRow := by cbv
private theorem outputFound : outputs[0]? = some output := by cbv
private theorem sourceChildren : sourceRow.children = [.reference firstName,.reference secondName] := by cbv
private theorem outputChildren : output.children = inputs := by cbv
private theorem contextInputs : InternedNestedProvenance.Values (empty : State Nat Bool) context := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact InternedNestedProvenance.ordinary_available empty 0
  · cases List.mem_singleton.mp member
    exact InternedNestedProvenance.ordinary_available empty 1
private theorem facts : InternedNestedFacts.Facts before := by
  simpa only [constructed,Outcome.state] using
    (InternedFreshOrdinaryFacts.build_verified expression context empty InternedNestedFacts.empty_facts contextInputs).facts
private theorem rootAvailable : Available before root :=
  (InternedFreshOrdinaryFacts.build_verified expression context empty InternedNestedFacts.empty_facts contextInputs).result
    root before constructed
private theorem inputsAvailable : InternedNestedProvenance.Values before inputs := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact rootAvailable.children right (by cbv; exact .tail _ (.head _))
  · cases List.mem_singleton.mp member
    exact rootAvailable.children left (by cbv; exact .head _)

private theorem ordered_proof :
    build expression context empty = .done root before ∧
    buildEdges (encodeEdges context [] originals) inputs before = .done outputs after ∧
    sourceRow.children = [.reference firstName,.reference secondName] ∧ output.children = [right,left] ∧
    right ≠ .reference firstName ∧ left ≠ .reference secondName ∧
    ∃ middle next originalChild childBefore childAfter,
      ChildTrace context [] inputs sourceRow.children before inputs middle ∧
      run (makeEdge sourceRow.entry.key.symbol sourceRow.entry.key.constraint inputs) middle = (output,next) ∧
      output.entry.key.symbol = sourceRow.entry.key.symbol ∧
      output.entry.key.constraint = sourceRow.entry.key.constraint ∧
      sourceRow.children[1]? = some originalChild ∧ originalChild = .reference secondName ∧
      ChildTrace context [] inputs (sourceRow.children.take 1) before (inputs.take 1) childBefore ∧
      build (encode context [] originalChild) inputs childBefore = .done left childAfter ∧
      ChildTrace context [] inputs (sourceRow.children.drop 2) childAfter (inputs.drop 2) middle := by
  obtain ⟨row,current,middle,next,values,found,earlier,trace,made,_later,symbol,guard,children,_arity⟩ :=
    rows_indexed context [] inputs originals before outputs after facts inputsAvailable rowDone 0 output outputFound
  have sameRow : row = sourceRow := Option.some.inj (found.symm.trans sourceFound)
  subst row
  have sameCurrent : current = before := by
    have same : Outcome.done ([] : List Edge) before = .done [] current := by
      simpa only [List.take_zero,encodeEdges,buildEdges] using earlier
    exact (Outcome.done.inj same).2.symm
  subst current
  have sameValues : values = inputs := children.symm.trans outputChildren
  subst values
  obtain ⟨originalChild,childBefore,childAfter,childFound,first,called,rest⟩ := trace.indexed 1 left rfl
  have sameChild : originalChild = .reference secondName := by
    simpa only [sourceChildren,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] using childFound.symm
  refine ⟨constructed,rowDone,sourceChildren,outputChildren,?_,?_,middle,next,originalChild,childBefore,childAfter,
    trace,made,symbol,guard,childFound,sameChild,first,called,rest⟩
  · cbv
    intro impossible
    cases impossible
  · cbv
    intro impossible
    cases impossible

/-- Two changed children retain their original order, full row fields, and exact intermediate build heaps. -/
theorem ordered :
    build expression context empty = .done root before ∧
    buildEdges (encodeEdges context [] originals) inputs before = .done outputs after ∧
    sourceRow.children = [.reference firstName,.reference secondName] ∧ output.children = [right,left] ∧
    right ≠ .reference firstName ∧ left ≠ .reference secondName ∧
    ∃ middle next originalChild childBefore childAfter,
      ChildTrace context [] inputs sourceRow.children before inputs middle ∧
      run (makeEdge sourceRow.entry.key.symbol sourceRow.entry.key.constraint inputs) middle = (output,next) ∧
      output.entry.key.symbol = sourceRow.entry.key.symbol ∧
      output.entry.key.constraint = sourceRow.entry.key.constraint ∧
      sourceRow.children[1]? = some originalChild ∧ originalChild = .reference secondName ∧
      ChildTrace context [] inputs (sourceRow.children.take 1) before (inputs.take 1) childBefore ∧
      build (encode context [] originalChild) inputs childBefore = .done left childAfter ∧
      ChildTrace context [] inputs (sourceRow.children.drop 2) childAfter (inputs.drop 2) middle := ordered_proof
end MicroCFTA.SubstitutionRowExecutionKernels
#check @MicroCFTA.SubstitutionRowExecutionKernels.ordered
#print MicroCFTA.SubstitutionRowExecutionKernels.ordered
#print axioms MicroCFTA.SubstitutionRowExecutionKernels.ordered
