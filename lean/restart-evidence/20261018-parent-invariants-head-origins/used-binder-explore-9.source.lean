import MicroCFTA.SourceCurrentStoredNormalizedPlans
import MicroCFTA.SourceCurrentStoredProbeCompatibility
import MicroCFTA.SourceCurrentNestedSourceInertBinder

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.UsedBinderExplore
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)

private def output (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def source : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.union [.var 1,.var 2],.var 0]])
private def firstInputs : List (Value Nat Bool) := [.reference .depth,.reference .depth]
private def secondInputs : List (Value Nat Bool) := [.reference .depth,.reference (.uninterned 0)]
private def firstCall := build source firstInputs empty
private def first := output firstCall
private def middle := firstCall.state
private def secondCall := build source secondInputs middle
private def second := output secondCall
private def reader := secondCall.state
private theorem firstDone : build source firstInputs empty = .done first middle := by cbv
private theorem secondDone : build source secondInputs middle = .done second reader := by cbv

private def parts : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def firstEntry := (parts first).1
private def firstBody := (parts first).2.1
private def secondEntry := (parts second).1
private def secondBody := (parts second).2.1
private def firstDepth := (parts first).2.2.1
private def firstOrdinary := (parts first).2.2.2
private def secondDepth := (parts second).2.2.1
private def secondOrdinary := (parts second).2.2.2
private theorem firstShape : first = .mu firstEntry firstBody firstDepth firstOrdinary := by cbv
private theorem secondShape : second = .mu secondEntry secondBody secondDepth secondOrdinary := by cbv
private def nodeParts : Value Nat Bool → Interned NodeKey × List (EdgeValue Nat Bool) × Nat × List Reference
  | .node entry rows depth free => (entry,rows,depth,free)
  | _ => (⟨0,.node []⟩,[],0,[])
private def firstRows := (nodeParts firstBody).2.1
private def secondRows := (nodeParts secondBody).2.1
private def defaultRow : EdgeValue Nat Bool := .mk ⟨0,⟨0,[],false⟩⟩ []
private def firstRow := firstRows.headD defaultRow
private def secondRow := secondRows.headD defaultRow
private theorem firstBodyShape : firstBody = .node (nodeParts firstBody).1 firstRows
    (nodeParts firstBody).2.2.1 (nodeParts firstBody).2.2.2 := by cbv
private theorem secondBodyShape : secondBody = .node (nodeParts secondBody).1 secondRows
    (nodeParts secondBody).2.2.1 (nodeParts secondBody).2.2.2 := by cbv
private theorem firstRowsShape : firstRows = [firstRow] := by cbv
private theorem secondRowsShape : secondRows = [secondRow] := by cbv
private def environment : InternedStoredSubstitution.Environment Nat Bool := fun _ => some .empty

private theorem not_related :
    ¬ SourceCurrentStoredNormalizedPlans.Related [] [] [] [] environment environment first second := by
  intro related
  rw [SourceCurrentStoredNormalizedPlans.Related.eq_def] at related
  have opened : first.free.isEmpty = false := by cbv
  simp only [opened,Bool.false_eq_true,ite_false] at related
  rw [firstShape,secondShape] at related
  have bodies := related.2 (.empty : Value Nat Bool)
  change SourceCurrentStoredNormalizedPlans.Related [.interned firstEntry.identity]
    [.interned secondEntry.identity] [.empty] [.empty] environment environment firstBody secondBody at bodies
  rw [SourceCurrentStoredNormalizedPlans.Related.eq_def] at bodies
  have openedBody : firstBody.free.isEmpty = false := by cbv
  simp only [openedBody,Bool.false_eq_true,ite_false] at bodies
  rw [firstBodyShape,secondBodyShape] at bodies
  have rows := bodies.2
  change SourceCurrentStoredNormalizedPlans.RowsRelated _ _ _ _ _ _ firstRows secondRows at rows
  rw [firstRowsShape,secondRowsShape,SourceCurrentStoredNormalizedPlans.RowsRelated.eq_def] at rows
  obtain ⟨row,present,matched⟩ := rows.1 firstRow List.mem_cons_self
  have same : row = secondRow := List.mem_singleton.mp present
  subst row
  have firstRowShape : firstRow = .mk firstRow.entry firstRow.children := by cases firstRow; rfl
  have secondRowShape : secondRow = .mk secondRow.entry secondRow.children := by cases secondRow; rfl
  rw [firstRowShape,secondRowShape,SourceCurrentStoredNormalizedPlans.RowRelated.eq_def] at matched
  have children := matched.2.2
  rw [SourceCurrentStoredNormalizedPlans.ManyRelated.eq_def] at children
  have child := children.1
  rw [SourceCurrentStoredNormalizedPlans.Related.eq_def] at child
  change (if false then _ else _ ∧ False) at child
  exact child.2

private theorem used :
    (match first with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match second with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) := by cbv

end MicroCFTA.UsedBinderExplore
