import MicroCFTA.SourceCurrentNativeOriginalBinderResume
import MicroCFTA.SourceCurrentNativePublicationRawSuffix
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# An actual warm binder inside an original source callback

The first box child publishes a nullary tagged Mu. The second child is a
raw outer Mu whose union body requests that same nested syntax again.
The callback retains the first full payload at the warm nested key.
-/
noncomputable section
namespace MicroCFTA.OriginalBinderFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction (build buildMany ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
private instance : DecidableEq FullSyntax.Formula := fun first second =>
  decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option cbv.maxSteps 100000000
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def nestedBody : Syntax Symbol Guard := .node [.mk ("tag17",.top) top []]
private def nested : Syntax Symbol Guard := .binder false nestedBody
private def outerBody : Syntax Symbol Guard := .union [.var 0,nested]
private def outer : Syntax Symbol Guard := .binder false outerBody
private def original : Syntax Symbol Guard := .node [.mk ("box",.top) top [nested,outer]]
private def valueOf (actual : Outcome Symbol Guard Node) : Node := match actual with
  | .done value _ => value | .pending .. => .empty
private def firstRun := build nested [] (empty : Heap)
private def firstMu : Node := valueOf firstRun
private def firstHeap : Heap := firstRun.state
private def firstEntry : Interned NodeKey := match firstMu with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def firstBody : Node := match firstMu with | .mu _ body _ _ => body | _ => .empty
private def firstDepth : Node := match firstMu with | .mu _ _ depth _ => depth | _ => .empty
private def firstOrdinary : Node := match firstMu with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def row : Row := (InternedEdgeResidency.nodeEdges firstBody)[0]?.getD
  (run (makeEdge ("missing",.top) top []) (empty : Heap)).1
private theorem first_done : build nested [] (empty : Heap) = .done firstMu firstHeap := by cbv
private theorem first_context : Context firstHeap [] := by
  simpa only [first_done,Outcome.state] using
    (show Context (empty : Heap) [] from SourceCurrentConstrainedCapSourceHistory.empty_context).build nested
private def depthRun := callback outerBody [] .depth firstHeap
private def depth : Node := valueOf depthRun
private def afterDepth : Heap := depthRun.state
private def ordinaryRun := callback outerBody [] (.uninterned (ordinaryLevel depth)) afterDepth
private def ordinary : Node := valueOf ordinaryRun
private def cut : Heap := ordinaryRun.state
private def reserved := Cache.intern cut.nodes (muKey depth ordinary)
private def allocated : Heap := {cut with nodes := reserved.2}
private def bodyRun := callback outerBody [] (.interned reserved.1.identity) allocated
private def storedBody : Node := valueOf bodyRun
private def afterBody : Heap := bodyRun.state
private def event : @Publication Symbol Guard _ :=
  ⟨false,outerBody,[],firstHeap,afterDepth,cut,afterBody,depth,ordinary,storedBody,
    first_context,by cbv,by cbv,by cbv,by cbv⟩
private def sourceRun := build original [] (empty : Heap)
private def root : Node := valueOf sourceRun
private def sourceHeap : Heap := sourceRun.state
private def inputs : List Node := [.reference (.interned event.entry.identity)]
private def rawRun := build outerBody inputs event.allocated
private def callbackRaw : Node := valueOf rawRun
private def callbackAfter : Heap := rawRun.state
private theorem source_done : build original [] (empty : Heap) = .done root sourceHeap := by cbv
private theorem outer_done : build outer [] firstHeap = .done event.candidate event.after := by cbv
private theorem raw_done : build outerBody inputs event.allocated = .done callbackRaw callbackAfter := by cbv
private theorem raw_filter : run (withoutSelfReference (.interned event.entry.identity) callbackRaw) callbackAfter =
    (event.body,event.afterBody) := by cbv
private theorem nested_warm : build nested inputs event.allocated = .done firstMu event.allocated := by cbv
private theorem warm_depth : callback nestedBody inputs .depth event.allocated = .done firstDepth event.allocated := by cbv
private theorem warm_ordinary : callback nestedBody inputs (.uninterned (ordinaryLevel firstDepth)) event.allocated =
    .done firstOrdinary event.allocated := by cbv
private theorem warm_key : event.allocated.nodes.table (muKey firstDepth firstOrdinary) = some firstEntry := by cbv
private theorem warm_record : event.allocated.nodeRecords (muKey firstDepth firstOrdinary) =
    some (.mu firstEntry firstBody firstDepth firstOrdinary) := by cbv
private theorem first_shape : firstMu = .mu firstEntry firstBody firstDepth firstOrdinary := by cbv
private theorem outer_shape : event.body = firstMu := by cbv
private theorem row_fields : row.entry.key.symbol = ("tag17",.top) ∧ row.entry.key.constraint = top ∧ row.children = [] := by
  constructor
  · cbv
  constructor <;> cbv
private theorem first_inside : RowAt firstMu row := by cbv; exact .mu (.node (index := 0) rfl)
private theorem first_body_inside : RowAt firstBody row := by cbv; exact .node (index := 0) rfl
private theorem first_is_prior : firstHeap.nodeRecords (muKey firstDepth firstOrdinary) =
    some (.mu firstEntry firstBody firstDepth firstOrdinary) := by cbv



private theorem raw_context : Context event.allocated inputs := by
  obtain ⟨_,cutContext,allocatedContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut
      cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  exact allocatedContext.local (.interned event.entry.identity) argument
private theorem callback_reached : InternedFreshOrdinarySourceHistory.Reached original [] outerBody inputs event.allocated := by
  have reached : InternedFreshOrdinarySourceHistory.Reached original [] outer [] firstHeap :=
    (InternedFreshOrdinarySourceHistory.reached_initial original [] firstHeap).node (symbol := ("box",.top)) (guard := top) (children := [nested,outer])
      (by simp [original]) (by simp)
  let crossing : InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard :=
    ⟨event.smart,event.expression,event.environment,event.before,.interned event.entry.identity,
      event.allocated,event.context.base,
      .fresh event.depth event.ordinary event.afterDepth event.cut
        event.depthDone event.ordinaryDone event.missing⟩
  exact reached.enter crossing
private theorem callback_suffix : Grows event.allocated callbackAfter ∧
    Extends event.allocated.nodes.issued callbackAfter.nodes.issued := by
  obtain ⟨path⟩ := SourceCurrentNativeMuIssuedHistory.build_path outerBody inputs event.allocated raw_context
  have path : SourceCurrentNativeMuIssuedHistory.Path event.allocated callbackAfter := by
    simpa only [raw_done,Outcome.state] using path
  exact ⟨path.growth,path.issued⟩
private def wrapperWork := (makeEdge ("box",.top) top [firstMu,event.candidate]).bind
  (fun edge => makeNode [edge])
private theorem wrapper_done : run wrapperWork event.after = (root,sourceHeap) := by cbv
private theorem enclosing_suffix : Grows event.after sourceHeap ∧
    Extends event.after.nodes.issued sourceHeap.nodes.issued := by
  have context : Context event.after [] := by
    simpa only [outer_done,Outcome.state] using first_context.build outer
  have valid := context.base.normal.facts.coherent.valid
  constructor
  · simpa only [wrapper_done] using (run_correct wrapperWork event.after valid).2
  · simpa only [wrapper_done] using run_issued_extends wrapperWork event.after valid
private theorem terminal_source : SourceRow nested inputs event.allocated firstMu event.allocated row :=
  SourceCurrentBuildStructuralRowOrigins.build_row_origin nested inputs event.allocated firstMu
    event.allocated raw_context nested_warm row first_inside
private theorem union_source : SourceRow outerBody inputs event.allocated callbackRaw callbackAfter row := by
  exact SourceRow.union (index := 1) (values := [.reference (.interned event.entry.identity),firstMu])
    (middle := event.allocated) (by cbv) (by cbv) rfl rfl (by cbv) raw_context nested_warm
    (by cbv) terminal_source
private theorem resumed :
    SourceCurrentCompletedBuildRootedWriters.Written original [] empty sourceHeap
      (muKey firstDepth firstOrdinary) (.mu firstEntry firstBody firstDepth firstOrdinary) ∧
    SourceCurrentNativeCapturedMuStoredRows.Stored original [] empty sourceHeap
      (muKey firstDepth firstOrdinary) firstEntry firstBody firstDepth firstOrdinary := by
  obtain ⟨chosenDepth,chosenAfterDepth,chosenOrdinary,chosenCut,chosenEntry,chosenBody,
    depthDone,ordinaryDone,_requested,_selected,_present,returned,_inside,_growth,_issued,written,stored⟩ :=
    SourceCurrentNativeOriginalBinderResume.resume original root sourceHeap source_done
      event callbackRaw callbackAfter raw_context raw_done raw_filter enclosing_suffix.1 enclosing_suffix.2
      false nestedBody inputs event.allocated firstMu event.allocated row terminal_source
      callback_suffix.1 callback_suffix.2
  change firstMu = Value.mu chosenEntry chosenBody chosenDepth chosenOrdinary at returned
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Value.mu.inj (first_shape.symm.trans returned)
  have afterSame := (Outcome.done.inj (depthDone.symm.trans warm_depth)).2
  subst chosenAfterDepth
  have cutSame := (Outcome.done.inj (ordinaryDone.symm.trans warm_ordinary)).2
  subst chosenCut
  exact ⟨written,stored⟩


private theorem checked_witness :
    ∃ (bodySyntax program : Syntax Symbol Guard) (first root : Node)
      (firstHeap sourceHeap : Heap) (event : @Publication Symbol Guard _) (raw : Node) (rawAfter : Heap)
      (inputs : List Node) (row : Row) (entry : Interned NodeKey) (body depth ordinary : Node),
      bodySyntax = .node [.mk ("tag17",.top) SourceEqualityConstraintConstructors.top []] ∧
      program = .node [.mk ("box",.top) SourceEqualityConstraintConstructors.top
        [.binder false bodySyntax,.binder false (.union [.var 0,.binder false bodySyntax])]] ∧
      build (.binder false bodySyntax) [] empty = .done first firstHeap ∧
      build program [] empty = .done root sourceHeap ∧
      first = .mu entry body depth ordinary ∧
      firstHeap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      event.smart = false ∧ event.expression = .union [.var 0,.binder false bodySyntax] ∧
      event.environment = [] ∧ event.before = firstHeap ∧ event.body = first ∧
      build (.binder false event.expression) [] firstHeap = .done event.candidate event.after ∧
      inputs = [.reference (.interned event.entry.identity)] ∧ Context event.allocated inputs ∧
      InternedFreshOrdinarySourceHistory.Reached program [] event.expression inputs event.allocated ∧
      build event.expression inputs event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      buildMany [.var 0] inputs event.allocated = .done [.reference (.interned event.entry.identity)] event.allocated ∧
      build (.binder false bodySyntax) inputs event.allocated = .done first event.allocated ∧
      buildMany [] inputs event.allocated = .done [] event.allocated ∧
      callback bodySyntax inputs .depth event.allocated = .done depth event.allocated ∧
      callback bodySyntax inputs (.uninterned (ordinaryLevel depth)) event.allocated = .done ordinary event.allocated ∧
      event.allocated.nodes.table (muKey depth ordinary) = some entry ∧
      event.allocated.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      SourceRow (.binder false bodySyntax) inputs event.allocated first event.allocated row ∧
      SourceRow event.expression inputs event.allocated raw rawAfter row ∧
      RowAt body row ∧ row.entry.key.symbol = ("tag17",.top) ∧
      row.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧ row.children = [] ∧
      Grows event.allocated rawAfter ∧ Extends event.allocated.nodes.issued rawAfter.nodes.issued ∧
      Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued ∧
      SourceCurrentCompletedBuildRootedWriters.Written program [] empty sourceHeap
        (muKey depth ordinary) (.mu entry body depth ordinary) ∧
      SourceCurrentNativeCapturedMuStoredRows.Stored program [] empty sourceHeap
        (muKey depth ordinary) entry body depth ordinary := by
  refine ⟨nestedBody,original,firstMu,root,firstHeap,sourceHeap,event,callbackRaw,callbackAfter,
    inputs,row,firstEntry,firstBody,firstDepth,firstOrdinary,rfl,rfl,first_done,source_done,
    first_shape,first_is_prior,rfl,rfl,rfl,rfl,outer_shape,outer_done,rfl,raw_context,callback_reached,
    raw_done,raw_filter,?_,nested_warm,?_,warm_depth,warm_ordinary,warm_key,warm_record,
    terminal_source,union_source,first_body_inside,row_fields.1,row_fields.2.1,row_fields.2.2,
    callback_suffix.1,callback_suffix.2,enclosing_suffix.1,enclosing_suffix.2,resumed.1,resumed.2⟩
  · cbv
  · rfl

/-- An actual warm nested binder retains its earlier full payload and original stored-row writer. -/
theorem actual_warm_binder :
    ∃ (bodySyntax program : Syntax Symbol Guard) (first root : Node)
      (firstHeap sourceHeap : Heap) (event : @Publication Symbol Guard _) (raw : Node) (rawAfter : Heap)
      (inputs : List Node) (row : Row) (entry : Interned NodeKey) (body depth ordinary : Node),
      bodySyntax = .node [.mk ("tag17",.top) SourceEqualityConstraintConstructors.top []] ∧
      program = .node [.mk ("box",.top) SourceEqualityConstraintConstructors.top
        [.binder false bodySyntax,.binder false (.union [.var 0,.binder false bodySyntax])]] ∧
      build (.binder false bodySyntax) [] empty = .done first firstHeap ∧
      build program [] empty = .done root sourceHeap ∧
      first = .mu entry body depth ordinary ∧
      firstHeap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      event.smart = false ∧ event.expression = .union [.var 0,.binder false bodySyntax] ∧
      event.environment = [] ∧ event.before = firstHeap ∧ event.body = first ∧
      build (.binder false event.expression) [] firstHeap = .done event.candidate event.after ∧
      inputs = [.reference (.interned event.entry.identity)] ∧ Context event.allocated inputs ∧
      InternedFreshOrdinarySourceHistory.Reached program [] event.expression inputs event.allocated ∧
      build event.expression inputs event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      buildMany [.var 0] inputs event.allocated = .done [.reference (.interned event.entry.identity)] event.allocated ∧
      build (.binder false bodySyntax) inputs event.allocated = .done first event.allocated ∧
      buildMany [] inputs event.allocated = .done [] event.allocated ∧
      callback bodySyntax inputs .depth event.allocated = .done depth event.allocated ∧
      callback bodySyntax inputs (.uninterned (ordinaryLevel depth)) event.allocated = .done ordinary event.allocated ∧
      event.allocated.nodes.table (muKey depth ordinary) = some entry ∧
      event.allocated.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      SourceRow (.binder false bodySyntax) inputs event.allocated first event.allocated row ∧
      SourceRow event.expression inputs event.allocated raw rawAfter row ∧
      RowAt body row ∧ row.entry.key.symbol = ("tag17",.top) ∧
      row.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧ row.children = [] ∧
      Grows event.allocated rawAfter ∧ Extends event.allocated.nodes.issued rawAfter.nodes.issued ∧
      Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued ∧
      SourceCurrentCompletedBuildRootedWriters.Written program [] empty sourceHeap
        (muKey depth ordinary) (.mu entry body depth ordinary) ∧
      SourceCurrentNativeCapturedMuStoredRows.Stored program [] empty sourceHeap
        (muKey depth ordinary) entry body depth ordinary := checked_witness

end MicroCFTA.OriginalBinderFixture
