import MicroCFTA.SourceCurrentPublicationNodeRowSurvival
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.InternedStoredShallowCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.PublicationSurvivalKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (NodeKey Reference)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentPublicationNodeRowSurvival (Paired)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def expressions : List (EdgeSyntax Nat Bool) := [
  .mk 0 false [.var 0,
    .binder false (.node [.mk 1 true [.var 0,.var 1]]),
    .node [.mk 2 true []]]]
private def expression : Syntax Nat Bool := .node expressions
private def source : Syntax Nat Bool := .binder false expression
private def depthCall := callback expression [] .depth (empty (Symbol := Nat) (Guard := Bool))
private def ordinaryCall := callback expression [] (.uninterned (ordinaryLevel (value depthCall))) depthCall.state
private def key := muKey (value depthCall) (value ordinaryCall)
private def reserved := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := reserved.2}
private def bodyCall := callback expression [] (.interned reserved.1.identity) allocated
private def event : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := expression
  environment := []
  before := empty
  afterDepth := depthCall.state
  cut := ordinaryCall.state
  afterBody := bodyCall.state
  depth := value depthCall
  ordinary := value ordinaryCall
  body := value bodyCall
  context := SourceCurrentConstrainedCapSourceHistory.empty_context
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def reader := event.after
private def selectedRow : EdgeValue Nat Bool :=
  match InternedEdgeResidency.nodeEdges event.body with
  | row :: _ => row
  | [] => .mk ⟨0,⟨0,[],false⟩⟩ []
private def nested := (selectedRow.children[1]?).getD .empty
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)

private theorem actual : build source [] empty = .done event.result reader := event.build_done
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source event.result reader actual
private theorem selected : selectedRow ∈ InternedEdgeResidency.nodeEdges event.body := by
  cbv
  exact List.mem_cons_self
private theorem nested_used : ∃ entry body depth ordinary,
    selectedRow.children[1]? = some (.mu entry body depth ordinary) ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by
  refine ⟨(fields nested).1,(fields nested).2.1,(fields nested).2.2.1,(fields nested).2.2.2,?_,?_⟩
  · cbv
  · cbv

private theorem witness :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    reader.nodeRecords event.key = some event.candidate ∧ event.result = event.candidate ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    (∃ entry body depth ordinary, selectedRow.children[1]? = some (.mu entry body depth ordinary) ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression ∧ event.body ≠ event.ordinary ∧
    selectedRow ∈ InternedEdgeResidency.nodeEdges event.body ∧
    selectedRow.entry.key.symbol = 0 ∧ selectedRow.entry.key.constraint = false ∧ selectedRow.children.length = 3 ∧
    Paired expressions event.environment (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity)
      event.afterDepth event.cut event.allocated event.afterBody event.afterBody event.ordinary event.body selectedRow := by
  refine ⟨actual,ready,?_,?_,?_,nested_used,?_,?_,selected,?_,?_,?_,?_⟩
  · cbv
  · cbv
  · cbv
  · cbv
    intro impossible
    cases impossible
  · intro same
    have ids := congrArg Value.referenceOf same
    cbv at ids
    cases ids
  · cbv
  · cbv
  · cbv
  · exact SourceCurrentPublicationNodeRowSurvival.publication event expressions rfl selectedRow selected

/-- An actual nested-used publication retains both surviving row schedules at the same source position. -/
theorem nested_used_row :
    build source [] empty = .done event.result reader ∧ Ready reader ∧
    reader.nodeRecords event.key = some event.candidate ∧ event.result = event.candidate ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    (∃ entry body depth ordinary, selectedRow.children[1]? = some (.mu entry body depth ordinary) ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression ∧ event.body ≠ event.ordinary ∧
    selectedRow ∈ InternedEdgeResidency.nodeEdges event.body ∧
    selectedRow.entry.key.symbol = 0 ∧ selectedRow.entry.key.constraint = false ∧ selectedRow.children.length = 3 ∧
    Paired expressions event.environment (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity)
      event.afterDepth event.cut event.allocated event.afterBody event.afterBody event.ordinary event.body selectedRow := witness

end MicroCFTA.PublicationSurvivalKernels
