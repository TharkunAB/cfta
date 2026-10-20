import MicroCFTA.SourceCurrentSelectedBinderChildResume

/-!
# A cold selected writer and a different warm requester

The first binder stores one body. The second binder repeats that source
body under a union and reuses the exact complete Mu. The selected child
keeps its full row and physical index through the historical raw callback.
-/
namespace MicroCFTA.SelectedBinderResumeFixture
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinarySourceHistory (Reached)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentRootedRowChildOrigins (Origin)
open SourceCurrentSelectedBinderChildResume (selected_body_child_or_prior)
open InternedEdgeResidency (nodeEdges)
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 10000000
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool
local notation "Row" => EdgeValue Nat Bool

private def leafSource : Syntax Nat Bool := .node [.mk 17 true []]
private def firstBody : Syntax Nat Bool := .node [.mk 5 false [leafSource,.var 0]]
private def secondBody : Syntax Nat Bool := .union [firstBody,firstBody]
private def firstSource : Syntax Nat Bool := .binder false firstBody
private def secondSource : Syntax Nat Bool := .binder false secondBody
private def source : Syntax Nat Bool := .union [firstSource,secondSource]
private def outcomeValue (actual : Outcome Nat Bool Node) : Node :=
  match actual with | .done value _ => value | .pending .. => .empty
private def firstRun := build firstSource [] (empty : Heap)
private def selected : Node := outcomeValue firstRun
private def firstAfter : Heap := firstRun.state
private def entry := match selected with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def body : Node := match selected with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match selected with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match selected with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def key : NodeKey := muKey depth ordinary
private def child : Node := .reference (.interned entry.identity)
private def parentRow : Row := (nodeEdges body)[0]?.getD
  (run (makeEdge 0 false []) (empty : Heap)).1

private theorem first_done : build firstSource [] (empty : Heap) = .done selected firstAfter := by cbv
private theorem second_warm : build secondSource [] firstAfter = .done selected firstAfter := by cbv
private theorem whole_done : build source [] (empty : Heap) = .done selected firstAfter := by cbv
private theorem distinct_sources : firstSource ≠ secondSource := by
  intro same
  change Syntax.binder false (.node [.mk 5 false [leafSource,.var 0]]) =
    Syntax.binder false (.union [firstBody,firstBody]) at same
  cases same
private theorem shape : selected = .mu entry body depth ordinary := by cbv
private theorem present : firstAfter.nodeRecords key = some (.mu entry body depth ordinary) := by cbv
private theorem warm_key : firstAfter.nodes.table key = some entry := by cbv
private theorem warm_depth : callback secondBody [] .depth firstAfter = .done depth firstAfter := by cbv
private theorem warm_ordinary : callback secondBody [] (.uninterned (ordinaryLevel depth)) firstAfter =
    .done ordinary firstAfter := by cbv
private theorem used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by cbv
private theorem row_fields : parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false := by cbv
private theorem inside : RowAt body parentRow := by cbv; exact .node (index := 0) rfl
private theorem selected_child : parentRow.children[1]? = some child := by cbv
private theorem context : Context (empty : Heap) [] := SourceCurrentConstrainedCapSourceHistory.empty_context
private theorem warm_context : Context firstAfter [] := by
  simpa only [first_done,Outcome.state] using context.build firstSource

private def Resumed : Prop :=
  ∃ event : Publication (Symbol := Nat) (Guard := Bool),
    Reached source [] (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path (empty : Heap) event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after firstAfter ∧ Extends event.after.nodes.issued firstAfter.nodes.issued ∧
    ∃ raw rawAfter,
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached source [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧ RowAt raw parentRow ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter parentRow ∧
      Origin source [] event.expression parentRow 1 child

private theorem resumed : Resumed := by
  rcases selected_body_child_or_prior source [] (empty : Heap) context selected firstAfter whole_done
      key entry body depth ordinary present parentRow inside 1 child selected_child with initial | found
  · cases initial
  · exact found

private theorem warm_prior : firstAfter.nodeRecords key = some (.mu entry body depth ordinary) := by
  rcases selected_body_child_or_prior secondSource [] firstAfter warm_context selected firstAfter second_warm
      key entry body depth ordinary present parentRow inside 1 child selected_child with initial | found
  · exact initial
  · obtain ⟨event,_site,keySame,_entrySame,_bodySame,_depthSame,_ordinarySame,missing,
      ⟨earlier⟩,⟨depthPath⟩,⟨ordinaryPath⟩,⟨bodyPath⟩,_growth,_issued,_rest⟩ := found
    have growth : Grows firstAfter event.afterBody :=
      grows_trans earlier.growth (grows_trans depthPath.growth (grows_trans ordinaryPath.growth
        (grows_trans (SourceCurrentNativeMuGrowthHistory.reserve_growth event) bodyPath.growth)))
    have retained := growth.nodeRecords key (.mu entry body depth ordinary) present
    rw [keySame,missing] at retained
    cases retained

private theorem checked_witness :
    Context (empty : Heap) [] ∧ firstSource ≠ secondSource ∧
    build firstSource [] (empty : Heap) = .done selected firstAfter ∧
    build secondSource [] firstAfter = .done selected firstAfter ∧
    build source [] (empty : Heap) = .done selected firstAfter ∧
    selected = .mu entry body depth ordinary ∧
    firstAfter.nodes.table key = some entry ∧
    firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∧
    callback secondBody [] .depth firstAfter = .done depth firstAfter ∧
    callback secondBody [] (.uninterned (ordinaryLevel depth)) firstAfter = .done ordinary firstAfter ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false ∧
    RowAt body parentRow ∧ parentRow.children[1]? = some child ∧
    child = .reference (.interned entry.identity) ∧
    firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∧ Resumed := by
  exact ⟨context,distinct_sources,first_done,second_warm,whole_done,shape,warm_key,present,
    warm_depth,warm_ordinary,used,row_fields.1,row_fields.2,inside,selected_child,rfl,warm_prior,resumed⟩

/-- An actual different-syntax warm request retains one selected used Mu and resumes its exact body child. -/
theorem actual_selected_resume :
    Context (empty : Heap) [] ∧ firstSource ≠ secondSource ∧
    build firstSource [] (empty : Heap) = .done selected firstAfter ∧
    build secondSource [] firstAfter = .done selected firstAfter ∧
    build source [] (empty : Heap) = .done selected firstAfter ∧
    selected = .mu entry body depth ordinary ∧
    firstAfter.nodes.table key = some entry ∧
    firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∧
    callback secondBody [] .depth firstAfter = .done depth firstAfter ∧
    callback secondBody [] (.uninterned (ordinaryLevel depth)) firstAfter = .done ordinary firstAfter ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    parentRow.entry.key.symbol = 5 ∧ parentRow.entry.key.constraint = false ∧
    RowAt body parentRow ∧ parentRow.children[1]? = some child ∧
    child = .reference (.interned entry.identity) ∧
    firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∧
  ∃ event : Publication (Symbol := Nat) (Guard := Bool),
    Reached source [] (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path (empty : Heap) event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after firstAfter ∧ Extends event.after.nodes.issued firstAfter.nodes.issued ∧
    ∃ raw rawAfter,
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached source [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧ RowAt raw parentRow ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter parentRow ∧
      Origin source [] event.expression parentRow 1 child := checked_witness

end MicroCFTA.SelectedBinderResumeFixture
