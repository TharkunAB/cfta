import MicroCFTA.SourceCurrentSourceChildDepth
import MicroCFTA.SourceCurrentNativeMuGrowthExecution
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment

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

namespace MicroCFTA.BinderChildDepthKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open InternedBinderProtocol (Reference)

private def nested : Syntax Nat Bool :=
  .binder true (.node [.mk 7 true [], .mk 9 false [.var 0]])

private def nestedUsed : Bool :=
  match build nested [] (empty (Symbol := Nat) (Guard := Bool)) with
  | .done (.mu _ _ depth ordinary) _ => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary
  | _ => false

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def expressions : List (EdgeSyntax Nat Bool) :=
  [.mk 8 false [.var 0,nested],.mk 2 true []]
private def expression : Syntax Nat Bool := .node expressions
private def requester : Syntax Nat Bool :=
  .node [.mk 2 true [],.mk 8 false [.var 0,nested],.mk 8 false [.var 0,nested]]
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

private def nodeCall := buildEdges expressions (.reference (.interned event.entry.identity) :: event.environment) event.allocated
private def nodeRows : List (EdgeValue Nat Bool) :=
  match nodeCall with | .done rows _ => rows | .pending .. => []
private theorem nodeRowsDone : nodeCall = .done nodeRows nodeCall.state := by cbv
private theorem nodeDone : build (.node expressions)
    (.reference (.interned event.entry.identity) :: event.environment) event.allocated =
      .done event.body event.afterBody := by cbv
private theorem nodeContext : SourceCurrentConstrainedCapSourceHistory.Context event.allocated
    (.reference (.interned event.entry.identity) :: event.environment) := by
  obtain ⟨_,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  exact bodyContext.local _ ((InternedConstructionProvenance.reserve_available event.key event.cut
    cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2)
private def unionExpressions : List (Syntax Nat Bool) := [.union [nested,.empty],nested,.empty]
private def unionCall := build (.union unionExpressions) [] (empty (Symbol := Nat) (Guard := Bool))
private def unionRaw := value unionCall
private theorem unionDone : unionCall = .done unionRaw unionCall.state := by cbv
private def manyCall := buildMany unionExpressions [] (empty (Symbol := Nat) (Guard := Bool))
private def unionMembers : List (Value Nat Bool) :=
  match manyCall with | .done members _ => members | .pending .. => []
private theorem unionMembersDone : manyCall = .done unionMembers manyCall.state := by cbv

private theorem checked :
    event.body.depth = 1 ∧
    (∃ rows middle,
      buildEdges expressions (.reference (.interned event.entry.identity) :: event.environment) event.allocated =
        .done rows middle ∧
      run (makeNode rows) middle = (event.body,event.afterBody) ∧
      surviving rows ≠ [] ∧
      ∀ row ∈ surviving rows, ∀ child ∈ row.children, child.depth ≤ event.body.depth) ∧
    unionRaw = value (build nested [] (empty (Symbol := Nat) (Guard := Bool))) ∧ unionRaw.depth = 1 ∧
    (∃ members middle,
      buildMany unionExpressions [] (empty (Symbol := Nat) (Guard := Bool)) = .done members middle ∧
      run (makeUnion members) middle = (unionRaw,unionCall.state) ∧
      members.map Value.depth = [1,1,0] ∧ ∀ member ∈ members, member.depth ≤ unionRaw.depth) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · cbv
  · obtain ⟨rows,middle,built,made,_context,bounded⟩ := SourceCurrentSourceChildDepth.node expressions _
      event.allocated event.afterBody nodeContext event.body nodeDone
    have same : rows = nodeRows := (Outcome.done.inj (built.symm.trans nodeRowsDone)).1
    refine ⟨rows,middle,built,made,?_,bounded⟩
    rw [same]
    intro impossible
    have count := congrArg List.length impossible
    cbv at count
  · cbv
  · cbv
  · obtain ⟨members,middle,built,made,_context,bounded⟩ := SourceCurrentSourceChildDepth.union unionExpressions []
      empty unionCall.state SourceCurrentConstrainedCapSourceHistory.empty_context unionRaw unionDone
    have same : members = unionMembers := (Outcome.done.inj (built.symm.trans unionMembersDone)).1
    refine ⟨members,middle,built,made,?_,bounded⟩
    rw [same]
    cbv

/-- Actual nested used-Mu source calls satisfy retained node and collapsed union depth bounds. -/
theorem constructors :
    event.body.depth = 1 ∧
    (∃ rows middle,
      buildEdges expressions (.reference (.interned event.entry.identity) :: event.environment) event.allocated =
        .done rows middle ∧
      run (makeNode rows) middle = (event.body,event.afterBody) ∧
      surviving rows ≠ [] ∧
      ∀ row ∈ surviving rows, ∀ child ∈ row.children, child.depth ≤ event.body.depth) ∧
    unionRaw = value (build nested [] (empty (Symbol := Nat) (Guard := Bool))) ∧ unionRaw.depth = 1 ∧
    (∃ members middle,
      buildMany unionExpressions [] (empty (Symbol := Nat) (Guard := Bool)) = .done members middle ∧
      run (makeUnion members) middle = (unionRaw,unionCall.state) ∧
      members.map Value.depth = [1,1,0] ∧ ∀ member ∈ members, member.depth ≤ unionRaw.depth) := checked

end MicroCFTA.BinderChildDepthKernels

#check @MicroCFTA.BinderChildDepthKernels.constructors
#print MicroCFTA.BinderChildDepthKernels.constructors
#print axioms MicroCFTA.BinderChildDepthKernels.constructors
