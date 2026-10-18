import MicroCFTA.SourceCurrentStoredNormalizedPlans
import MicroCFTA.SourceCurrentStoredProbeCompatibility
import MicroCFTA.SourceCurrentNestedSourceInertBinder

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.UsedBinderBoundary
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
private def unionChild := secondRow.children.headD .empty
private theorem firstChildrenShape : firstRow.children = [.reference .depth,.reference (.interned firstEntry.identity)] := by cbv
private theorem secondChildrenShape : secondRow.children = [unionChild,.reference (.interned secondEntry.identity)] := by cbv
private def unionParts : Value Nat Bool → Interned NodeKey × List (Value Nat Bool) × Nat × List Reference
  | .union entry members depth free => (entry,members,depth,free)
  | _ => (⟨0,.node []⟩,[],0,[])
private theorem unionShape : unionChild = .union (unionParts unionChild).1 (unionParts unionChild).2.1
    (unionParts unionChild).2.2.1 (unionParts unionChild).2.2.2 := by cbv
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
  rw [firstChildrenShape,secondChildrenShape] at children
  have child := children.1
  rw [SourceCurrentStoredNormalizedPlans.Related.eq_def] at child
  rw [unionShape] at child
  change (if false then _ else _ ∧ False) at child
  exact child.2

private theorem used :
    (match first with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match second with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) := by cbv

private theorem sourceKeeps (expression : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before after : State Nat Bool) (ready : Ready before) (available : Values before inputs)
    (value : Value Nat Bool) (actual : build expression inputs before = .done value after) : Keeps before after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  have checked := build_verified expression inputs before ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before ready.semantic.1.normal.facts.coherent.valid
      ready.covered value after actual
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs before context ready.semantic.2 ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history
private theorem initialReady : Ready (empty (Symbol := Nat) (Guard := Bool)) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty (by cbv)
private theorem firstAvailable : Values (empty (Symbol := Nat) (Guard := Bool)) firstInputs := by
  intro value member
  have same : value = .reference .depth := by simpa [firstInputs] using member
  rw [same]
  exact InternedNestedProvenance.depth_available _
private theorem secondAvailable : Values middle secondInputs := by
  intro value member
  simp only [secondInputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact InternedNestedProvenance.depth_available _
  · exact InternedNestedProvenance.ordinary_available _ _
private theorem firstKept : Keeps empty middle := sourceKeeps source firstInputs empty middle initialReady firstAvailable first firstDone
private theorem secondKept : Keeps middle reader := sourceKeeps source secondInputs middle reader firstKept.ready secondAvailable second secondDone
private noncomputable def fullHistory : History empty reader := by
  let firstHistory := Classical.choice (SourceCurrentNativeMuPublication.build_history source firstInputs empty
    ⟨SourceRecursiveIntersectionSemanticHeap.context _ initialReady.semantic _ firstAvailable,initialReady.semantic.2⟩)
  let secondHistory := Classical.choice (SourceCurrentNativeMuPublication.build_history source secondInputs middle
    ⟨SourceRecursiveIntersectionSemanticHeap.context _ firstKept.ready.semantic _ secondAvailable,firstKept.ready.semantic.2⟩)
  exact .trans (by simpa only [firstDone,Outcome.state] using firstHistory)
    (by simpa only [secondDone,Outcome.state] using secondHistory)
private theorem boundary_proof :
    build source firstInputs empty = .done first middle ∧
    build source secondInputs middle = .done second reader ∧
    build source firstInputs reader = .done first reader ∧
    build source secondInputs reader = .done second reader ∧
    Ready reader ∧ Nonempty (History empty reader) ∧
    SourceCurrentStoredMuBinderChildLineage.Paired environment environment firstInputs secondInputs ∧
    InternedStoredSubstitution.Replacements reader environment ∧
    (match first with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match second with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    ¬ SourceCurrentStoredNormalizedPlans.Related [] [] [] [] environment environment first second := by
  have firstWarm := InternedFreshOrdinaryReplay.build_replay source firstInputs empty reader first middle
    empty_valid firstDone secondKept.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay source secondInputs middle reader second reader
    firstKept.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  refine ⟨firstDone,secondDone,firstWarm,secondWarm,secondKept.ready,⟨fullHistory⟩,?_,?_,used.1,used.2,not_related⟩
  · exact .cons rfl (.cons rfl .nil)
  · intro name value found
    have same : value = .empty := (Option.some.inj found).symm
    rw [same]
    exact empty_available _

/-- Actual used source binders refute an unrestricted structural-plan strengthening of lexical compatibility. -/
theorem structural_boundary :
    build source firstInputs empty = .done first middle ∧
    build source secondInputs middle = .done second reader ∧
    build source firstInputs reader = .done first reader ∧
    build source secondInputs reader = .done second reader ∧
    Ready reader ∧ Nonempty (History empty reader) ∧
    SourceCurrentStoredMuBinderChildLineage.Paired environment environment firstInputs secondInputs ∧
    InternedStoredSubstitution.Replacements reader environment ∧
    (match first with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match second with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    ¬ SourceCurrentStoredNormalizedPlans.Related [] [] [] [] environment environment first second := boundary_proof

end MicroCFTA.UsedBinderBoundary

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.UsedBinderBoundary.structural_boundary
#print MicroCFTA.UsedBinderBoundary.structural_boundary
#print axioms MicroCFTA.UsedBinderBoundary.structural_boundary
