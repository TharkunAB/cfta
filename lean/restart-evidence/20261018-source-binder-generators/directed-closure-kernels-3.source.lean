import MicroCFTA.SourceCurrentDirectedClosure
import MicroCFTA.SourceCurrentSourceDirectedCases
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.DirectedClosureKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentSourceDirectedCases (Below)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open SourceCurrentDirectedClosure (Closure)
open SourceCurrentOpenObservations (RowMatch)
open MergedFreshOrdinaryGraph (Origin successors)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def nested : Syntax Nat Bool := .binder true (.node [.mk 7 true [],.mk 9 false [.var 0]])
private def leaf : Syntax Nat Bool := .node [.mk 3 false []]
private def extra : Syntax Nat Bool := .node [.mk 4 true []]
private def source : Syntax Nat Bool := .node [.mk 0 false
  [nested,leaf,extra,.union [nested,leaf],.union [.union [nested,leaf],extra]]]
private def built := build source [] empty
private def root := value built
private def reader := built.state
private def capture : Value Nat Bool := (children root)[0]?.getD .empty
private def ordinary : Value Nat Bool := (children root)[1]?.getD .empty
private def added : Value Nat Bool := (children root)[2]?.getD .empty
private def middle : Value Nat Bool := (children root)[3]?.getD .empty
private def last : Value Nat Bool := (children root)[4]?.getD .empty
private def muFields : Value Nat Bool → Interned InternedBinderProtocol.NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private theorem capture_shape : capture = .mu (muFields capture).1 (muFields capture).2.1
    (muFields capture).2.2.1 (muFields capture).2.2.2 := by cbv
private theorem capture_distinct : capture ≠ middle := by
  intro equal
  have same := congrArg Value.referenceOf equal
  cbv at same
  cases same
private theorem last_distinct : middle ≠ last := by
  intro equal
  have same := congrArg Value.referenceOf equal
  cbv at same
  cases same
private theorem built_done : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader built_done
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro supplied member; cases member)).result root reader built_done
private theorem children_available (index : Nat) :
    Available reader ((children root)[index]?.getD .empty) := by
  cases found : (children root)[index]? with
  | none => simpa only [found,Option.getD_none] using empty_available reader
  | some child =>
      simpa only [found,Option.getD_some] using root_available.children child (List.mem_of_getElem? found)
private theorem first_made : run (makeUnion [capture,.empty,ordinary,capture]) reader = (middle,reader) := by cbv
private theorem second_made : run (makeUnion [middle,added,middle]) reader = (last,reader) := by cbv
private theorem first_below : Below capture middle := by
  have result := SourceCurrentSourceDirectedCases.union_member [capture,.empty,ordinary,capture] reader
    ready.semantic.1.normal (by
      intro value member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact children_available 0
      · exact empty_available reader
      · exact children_available 1
      · exact children_available 0) capture List.mem_cons_self
  simpa only [first_made] using result
private theorem second_below : Below middle last := by
  have result := SourceCurrentSourceDirectedCases.union_member [middle,added,middle] reader
    ready.semantic.1.normal (by
      intro value member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      · exact children_available 3
      · exact children_available 2
      · exact children_available 3) middle List.mem_cons_self
  simpa only [second_made] using result
private def paired (first second : Value Nat Bool) : Prop := Below first second ∨ first = second
private theorem equal_directed : Directed reader (Eq (α := Value Nat Bool)) := by
  intro first second same
  cases same
  exact SourceCurrentSourceDirectedCases.equal reader Eq (fun _ => rfl) first
private theorem alternatives : Directed reader paired :=
  SourceCurrentDirectedClosure.or_directed reader Below Eq
    (SourceCurrentSourceDirectedCases.below_directed reader) equal_directed
private theorem chained : Closure paired capture last :=
  .step (Or.inl first_below) (.step (Or.inl second_below) (.refl last))
private def unfoldedRun := InternedFreshOrdinaryStoredSubstitution.unfold capture reader
private def unfolded := value unfoldedRun
private def row : EdgeValue Nat Bool := (nodeEdges unfolded)[1]?.getD (.mk ⟨0,⟨0,[],false⟩⟩ [])
private theorem unfolded_done :
    InternedFreshOrdinaryStoredSubstitution.unfold capture reader = .done unfolded unfoldedRun.state := by cbv
private theorem row_origin : Origin reader [capture] row := by
  refine ⟨unfolded,.step (.seed List.mem_cons_self) ?_,?_⟩
  · show unfolded ∈ successors reader capture
    rw [capture_shape,successors,← capture_shape,unfolded_done]
    exact List.mem_cons_self
  · exact List.mem_of_getElem? (show (nodeEdges unfolded)[1]? = some row by cbv)
private theorem row_fields : row.entry.key.symbol = 9 ∧ row.entry.key.constraint = false ∧ row.children = [capture] := by cbv

/-- Two actual union calls validate finite closure and preserve a recursive full row. -/
theorem witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    Available reader capture ∧ Available reader middle ∧ Available reader last ∧
    (∃ entry body depth ordinary, capture = .mu entry body depth ordinary ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
    run (makeUnion [capture,.empty,ordinary,capture]) reader = (middle,reader) ∧
    run (makeUnion [middle,added,middle]) reader = (last,reader) ∧
    capture ≠ middle ∧ middle ≠ last ∧
    Below capture middle ∧ Below middle last ∧ Closure paired capture last ∧
    Directed reader (Closure paired) ∧
    InternedFreshOrdinaryStoredSubstitution.unfold capture reader = .done unfolded unfoldedRun.state ∧
    Origin reader [capture] row ∧ row.entry.key.symbol = 9 ∧ row.entry.key.constraint = false ∧
    row.children = [capture] ∧
    ∃ other, Origin reader [last] other ∧ RowMatch (Mutual (Closure paired)) row other := by
  refine ⟨built_done,ready,children_available 0,children_available 3,children_available 4,?_,
    first_made,second_made,capture_distinct,last_distinct,first_below,second_below,chained,
    SourceCurrentDirectedClosure.directed reader paired alternatives,unfolded_done,row_origin,
    row_fields.1,row_fields.2.1,row_fields.2.2,?_⟩
  · exact ⟨(muFields capture).1,(muFields capture).2.1,(muFields capture).2.2.1,
      (muFields capture).2.2.2,by cbv,by cbv⟩
  · exact (SourceCurrentDirectedClosure.directed reader paired alternatives).row reader (Closure paired) chained row row_origin

end MicroCFTA.DirectedClosureKernels
