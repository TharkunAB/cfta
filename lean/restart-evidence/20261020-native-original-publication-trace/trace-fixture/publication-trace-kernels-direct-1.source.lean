import MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
import MicroCFTA.SourceCurrentBuildStructuralRowOrigins
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentNativePublicationRawSuffix
import MicroCFTA.SourceEqualityPCSNativeEdge
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# An actual warm binder inside an original source callback

The first box child publishes a nullary tagged Mu. The second child is a
raw outer Mu whose union body requests that same nested syntax again.
The callback retains the first full payload at the warm nested key.
-/
noncomputable section
namespace MicroCFTA.OriginalPublicationTraceFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeOriginalPublicationTrace (events)
open InternedFreshOrdinarySourceHistory (Reached)
open InternedEdgeResidency (nodeEdges)
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
private theorem warm_request : request false firstDepth firstOrdinary (callback nestedBody inputs) event.allocated =
    .done firstMu event.allocated := by cbv
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
      (by simp) (by simp)
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




private theorem outer_record : sourceHeap.nodeRecords event.key = some event.candidate := by cbv
private theorem first_key : firstEntry.key = muKey firstDepth firstOrdinary := by cbv
private theorem publication_body_available (published : @Publication Symbol Guard _) :
    Available published.afterBody published.body := by
  obtain ⟨_,cutContext,allocatedContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts published
  have argument : Available published.allocated (.reference (.interned published.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available published.key published.cut
      cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  have inputs := allocatedContext.local (.interned published.entry.identity) argument
  exact (InternedFreshOrdinaryFacts.callback_verified published.expression published.environment
    (.interned published.entry.identity) published.allocated inputs.base.normal.facts
      inputs.base.inputs).result published.body published.afterBody published.bodyDone
private theorem earlier_inner_cell (published : @Publication Symbol Guard _)
    (same : event.candidate = published.candidate) :
    published.afterBody.nodeRecords (muKey firstDepth firstOrdinary) = some firstMu := by
  have bodySame := (Value.mu.inj same).2.1
  have available : Available published.afterBody firstMu := by
    rw [← outer_shape,bodySame]
    exact publication_body_available published
  rw [first_shape] at available
  have present := available.resident firstEntry rfl
  rw [first_key] at present
  simpa only [first_shape] using present


private theorem checked_witness :
    ∃ (bodySyntax original : Syntax Symbol Guard) (first sourceRoot : Node)
      (firstHeap sourceHeap : Heap) (outerEvent : @Publication Symbol Guard _)
      (firstEntry : Interned NodeKey) (firstBody firstDepth firstOrdinary : Node) (tagRow : Row),
      bodySyntax = .node [.mk ("tag17",.top) SourceEqualityConstraintConstructors.top []] ∧
      original = .node [.mk ("box",.top) SourceEqualityConstraintConstructors.top
        [.binder false bodySyntax,.binder false (.union [.var 0,.binder false bodySyntax])]] ∧
      build (.binder false bodySyntax) [] empty = .done first firstHeap ∧
      build original [] empty = .done sourceRoot sourceHeap ∧
      first = Value.mu firstEntry firstBody firstDepth firstOrdinary ∧
      firstHeap.nodeRecords (muKey firstDepth firstOrdinary) = some first ∧
      outerEvent.smart = false ∧ outerEvent.expression = .union [.var 0,.binder false bodySyntax] ∧
      outerEvent.environment = [] ∧ outerEvent.before = firstHeap ∧ outerEvent.body = first ∧
      build (.binder false outerEvent.expression) [] firstHeap = .done outerEvent.candidate outerEvent.after ∧
      build (.binder false bodySyntax) [.reference (.interned outerEvent.entry.identity)] outerEvent.allocated =
        .done first outerEvent.allocated ∧
      sourceHeap.nodeRecords outerEvent.key = some outerEvent.candidate ∧
      RowAt firstBody tagRow ∧ tagRow.entry.key.symbol = ("tag17",.top) ∧
      tagRow.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧ tagRow.children = [] ∧
    ∃ path : Path empty sourceHeap,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original [] (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path empty event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ key entry body depth ordinary,
          outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
          ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
            Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
            key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
            earlier.afterBody.nodeRecords earlier.key = none ∧
            Nonempty (Path empty earlier.before) ∧
            Nonempty (Path earlier.before earlier.afterDepth) ∧
            Nonempty (Path earlier.afterDepth earlier.cut) ∧
            Nonempty (Path earlier.allocated earlier.afterBody) ∧
            Grows earlier.after outer.afterBody ∧
            Extends earlier.after.nodes.issued outer.afterBody.nodes.issued) ∧
      ∃ outerIndex : Nat, ∃ outer, ∃ earlierIndex : Nat, ∃ earlier,
        earlierIndex < outerIndex ∧ (events path)[outerIndex]? = some outer ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate ∧
        muKey firstDepth firstOrdinary = earlier.key ∧
        Value.mu firstEntry firstBody firstDepth firstOrdinary = earlier.candidate ∧
        outer.afterBody.nodeRecords (muKey firstDepth firstOrdinary) = some first ∧
        outer.afterBody.nodeRecords outer.key = none ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty outer.before) ∧
        Nonempty (Path outer.before outer.afterDepth) ∧
        Nonempty (Path outer.afterDepth outer.cut) ∧
        Nonempty (Path outer.allocated outer.afterBody) ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows outer.after sourceHeap ∧ Extends outer.after.nodes.issued sourceHeap.nodes.issued ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued := by
  obtain ⟨path,sites,finalWriters,precompletion⟩ :=
    SourceCurrentNativeOriginalPublicationTrace.build_trace_writers original [] (empty : Heap)
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key entry body depth ordinary impossible; cases impossible) root sourceHeap source_done
  obtain ⟨outerIndex,outer,outerLookup,outerReached,outerKey,outerValue,outerMissing,
    outerPrefix,outerDepth,outerOrdinary,outerBody,outerGrowth,outerIssued⟩ :=
    finalWriters event.key event.entry event.body event.depth event.ordinary outer_record
  have innerHere := earlier_inner_cell outer outerValue
  have innerFull : outer.afterBody.nodeRecords (muKey firstDepth firstOrdinary) =
      some (Value.mu firstEntry firstBody firstDepth firstOrdinary) := by
    simpa only [first_shape] using innerHere
  obtain ⟨earlierIndex,earlier,less,earlierLookup,earlierReached,earlierKey,earlierValue,earlierMissing,
    earlierPrefix,earlierDepth,earlierOrdinary,earlierBody,earlierGrowth,earlierIssued⟩ :=
    precompletion outerIndex outer outerLookup (muKey firstDepth firstOrdinary)
      firstEntry firstBody firstDepth firstOrdinary innerFull
  refine ⟨nestedBody,original,firstMu,root,firstHeap,sourceHeap,event,firstEntry,firstBody,firstDepth,
    firstOrdinary,row,rfl,rfl,first_done,source_done,first_shape,?_,rfl,rfl,rfl,rfl,outer_shape,outer_done,
    nested_warm,outer_record,first_body_inside,row_fields.1,row_fields.2.1,row_fields.2.2,
    path,sites,finalWriters,precompletion,outerIndex,outer,earlierIndex,earlier,less,outerLookup,
    earlierLookup,outerReached,earlierReached,outerKey,outerValue,earlierKey,earlierValue,innerHere,
    outerMissing,earlierMissing,outerPrefix,outerDepth,outerOrdinary,outerBody,earlierPrefix,
    earlierDepth,earlierOrdinary,earlierBody,outerGrowth,outerIssued,earlierGrowth,earlierIssued⟩
  simpa only [first_shape] using first_is_prior

/-- One actual source trace contains a strict earlier inner writer before the selected outer publication. -/
theorem actual_strict_publication_order :
    ∃ (bodySyntax original : Syntax Symbol Guard) (first sourceRoot : Node)
      (firstHeap sourceHeap : Heap) (outerEvent : @Publication Symbol Guard _)
      (firstEntry : Interned NodeKey) (firstBody firstDepth firstOrdinary : Node) (tagRow : Row),
      bodySyntax = .node [.mk ("tag17",.top) SourceEqualityConstraintConstructors.top []] ∧
      original = .node [.mk ("box",.top) SourceEqualityConstraintConstructors.top
        [.binder false bodySyntax,.binder false (.union [.var 0,.binder false bodySyntax])]] ∧
      build (.binder false bodySyntax) [] empty = .done first firstHeap ∧
      build original [] empty = .done sourceRoot sourceHeap ∧
      first = Value.mu firstEntry firstBody firstDepth firstOrdinary ∧
      firstHeap.nodeRecords (muKey firstDepth firstOrdinary) = some first ∧
      outerEvent.smart = false ∧ outerEvent.expression = .union [.var 0,.binder false bodySyntax] ∧
      outerEvent.environment = [] ∧ outerEvent.before = firstHeap ∧ outerEvent.body = first ∧
      build (.binder false outerEvent.expression) [] firstHeap = .done outerEvent.candidate outerEvent.after ∧
      build (.binder false bodySyntax) [.reference (.interned outerEvent.entry.identity)] outerEvent.allocated =
        .done first outerEvent.allocated ∧
      sourceHeap.nodeRecords outerEvent.key = some outerEvent.candidate ∧
      RowAt firstBody tagRow ∧ tagRow.entry.key.symbol = ("tag17",.top) ∧
      tagRow.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧ tagRow.children = [] ∧
    ∃ path : Path empty sourceHeap,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original [] (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path empty event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ key entry body depth ordinary,
          outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
          ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
            Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
            key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
            earlier.afterBody.nodeRecords earlier.key = none ∧
            Nonempty (Path empty earlier.before) ∧
            Nonempty (Path earlier.before earlier.afterDepth) ∧
            Nonempty (Path earlier.afterDepth earlier.cut) ∧
            Nonempty (Path earlier.allocated earlier.afterBody) ∧
            Grows earlier.after outer.afterBody ∧
            Extends earlier.after.nodes.issued outer.afterBody.nodes.issued) ∧
      ∃ outerIndex : Nat, ∃ outer, ∃ earlierIndex : Nat, ∃ earlier,
        earlierIndex < outerIndex ∧ (events path)[outerIndex]? = some outer ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate ∧
        muKey firstDepth firstOrdinary = earlier.key ∧
        Value.mu firstEntry firstBody firstDepth firstOrdinary = earlier.candidate ∧
        outer.afterBody.nodeRecords (muKey firstDepth firstOrdinary) = some first ∧
        outer.afterBody.nodeRecords outer.key = none ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty outer.before) ∧
        Nonempty (Path outer.before outer.afterDepth) ∧
        Nonempty (Path outer.afterDepth outer.cut) ∧
        Nonempty (Path outer.allocated outer.afterBody) ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows outer.after sourceHeap ∧ Extends outer.after.nodes.issued sourceHeap.nodes.issued ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued := checked_witness

end MicroCFTA.OriginalPublicationTraceFixture
