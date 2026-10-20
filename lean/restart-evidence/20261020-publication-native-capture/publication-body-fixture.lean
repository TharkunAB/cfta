import MicroCFTA.SourceCurrentPublicationBodySourceRows

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.PublicationBodySourceRowsFixture
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentConstrainedCapSourceHistory (Context)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool

private def source : Syntax Nat Bool := .binder true (.node [.mk 7 false [.var 0]])
private def outcomeValue (actual : Outcome Nat Bool Node) : Node :=
  match actual with | .done value _ => value | .pending .. => .empty
private def actualRun := build source [] empty
private def selected : Node := outcomeValue actualRun
private def final : Heap := actualRun.state
private def entry := match selected with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def body : Node := match selected with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match selected with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match selected with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def key := muKey depth ordinary
private def row : EdgeValue Nat Bool := match body with
  | .node _ (first :: _) _ _ => first
  | _ => (run (makeEdge 0 false []) (empty : Heap)).1

private theorem built : build source [] empty = .done selected final := by cbv
private theorem shape : selected = .mu entry body depth ordinary := by cbv
private theorem present : final.nodeRecords key = some (.mu entry body depth ordinary) := by cbv
private theorem used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by cbv
private theorem selected_row : (nodeEdges body)[0]? = some row := by cbv
private theorem body_row : RowAt body row := by
  cases shape : body with
  | node entry rows level free =>
      exact .node (index := 0) (by simpa only [shape,nodeEdges] using selected_row)
  | empty | reference | union | mu =>
      have impossible := selected_row
      simp only [shape,nodeEdges,List.getElem?_nil] at impossible
      cases impossible

private theorem rooted : SourceCurrentCompletedBuildRootedWriters.Written source [] empty final key
    (.mu entry body depth ordinary) :=
  SourceCurrentCompletedBuildRootedWriters.build_writer source [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context
    (by intro key entry body depth ordinary impossible; cases impossible)
    selected final built key entry body depth ordinary present

private def Claim : Prop :=
  build source [] empty = .done selected final ∧ selected = .mu entry body depth ordinary ∧
  final.nodeRecords key = some (.mu entry body depth ordinary) ∧
  InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
  (nodeEdges body)[0]? = some row ∧
  ∃ event : Publication (Symbol := Nat) (Guard := Bool),
    Reached source [] (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path empty event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after final ∧ Extends event.after.nodes.issued final.nodes.issued ∧
    ∃ raw rawAfter,
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached source [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧
      RowAt raw row ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter row

private theorem checked_witness : Claim :=
  ⟨built,shape,present,used,selected_row,
    SourceCurrentPublicationBodySourceRows.written_body_origin rooted row body_row⟩

/-- An actual used Mu derives its selected publication and the same body's historical raw source row. -/
theorem witness :
  build source [] empty = .done selected final ∧ selected = .mu entry body depth ordinary ∧
  final.nodeRecords key = some (.mu entry body depth ordinary) ∧
  InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
  (nodeEdges body)[0]? = some row ∧
  ∃ event : Publication (Symbol := Nat) (Guard := Bool),
    Reached source [] (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path empty event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after final ∧ Extends event.after.nodes.issued final.nodes.issued ∧
    ∃ raw rawAfter,
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached source [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧
      RowAt raw row ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter row := checked_witness

end MicroCFTA.PublicationBodySourceRowsFixture
