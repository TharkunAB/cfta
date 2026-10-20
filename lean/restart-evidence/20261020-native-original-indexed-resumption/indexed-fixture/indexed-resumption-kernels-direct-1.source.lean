import MicroCFTA.SourceCurrentNativeOriginalIndexedResumption
import MicroCFTA.SourceCurrentNativeOriginalUnionDescent
import MicroCFTA.SourceCurrentNativePublicationRawSuffix
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# Indexed resumption of an actual warm source binder

The source family is the prior box with a nested Mu and an outer Mu.
The consumer retains one publication path. The selected callback row
forces a binder terminal and a strictly earlier indexed writer.
-/
noncomputable section
namespace MicroCFTA.OriginalIndexedResumptionFixture
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
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open InternedEdgeResidency (nodeEdges)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeCapturedMuStoredRows (Stored)
open SourceCurrentNativeOriginalObservedResume (SyntaxBound)
open SourceCurrentNativeOriginalUnionDescent (UnionDescent)
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
private theorem outer_inside : RowAt event.body row := by
  rw [outer_shape]
  exact first_inside

private theorem no_node_binder_path {symbol : Symbol} {guard : Guard}
    {captures inputs : List Node} {smart : Bool} {body : Syntax Symbol Guard}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path (.node [.mk symbol guard []]) inputs
      (.binder smart body) captures crossings) : False := by
  cases path with
  | node edge member nested =>
    simp only [List.mem_singleton,InternedNestedConstruction.EdgeSyntax.mk.injEq] at edge
    obtain ⟨rfl,rfl,rfl⟩ := edge
    cases member
private theorem nested_binder_path {captures inputs : List Node} {smart : Bool} {body : Syntax Symbol Guard}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path nested inputs (.binder smart body) captures crossings) :
    body = nestedBody := by
  generalize sourceSame : nested = source at path
  cases path with
  | here => exact (Syntax.binder.inj sourceSame).2.symm
  | node => cases sourceSame
  | union => cases sourceSame
  | binder crossing tail =>
    have bodySame : crossing.body = nestedBody := (Syntax.binder.inj sourceSame).2.symm
    rw [bodySame] at tail
    exact (no_node_binder_path tail).elim
private theorem outer_binder_path {captures inputs : List Node} {smart : Bool} {body : Syntax Symbol Guard}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path outer inputs (.binder smart body) captures crossings) :
    body = nestedBody ∨ body = outerBody := by
  generalize sourceSame : outer = source at path
  cases path with
  | here => exact .inr (Syntax.binder.inj sourceSame).2.symm
  | node => cases sourceSame
  | union => cases sourceSame
  | binder crossing tail =>
    have bodySame : crossing.body = outerBody := (Syntax.binder.inj sourceSame).2.symm
    rw [bodySame] at tail
    cases tail with
    | union member tail =>
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · cases tail
      · exact .inl (nested_binder_path tail)
private theorem recovered_body {captures : List Node} {smart : Bool} {body : Syntax Symbol Guard} {state : Heap}
    (reached : Reached original [] (.binder smart body) captures state) :
    body = nestedBody ∨ body = outerBody := by
  obtain ⟨crossings,path,_⟩ := reached
  cases path with
  | node edge member tail =>
    simp only [List.mem_singleton,InternedNestedConstruction.EdgeSyntax.mk.injEq] at edge
    obtain ⟨rfl,rfl,rfl⟩ := edge
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact .inl (nested_binder_path tail)
    · exact outer_binder_path tail
private theorem node_filter_not_mu {expressions : List (InternedNestedConstruction.EdgeSyntax Symbol Guard)}
    {inputs : List Node} {before after last : Heap} {raw value : Node} {row : Row}
    {entry : Interned NodeKey} {body depth ordinary : Node} {own : Reference}
    (source : SourceRow (.node expressions) inputs before raw after row)
    (filtered : run (withoutSelfReference own raw) after = (value,last))
    (same : value = .mu entry body depth ordinary) : False := by
  cases source with
  | node built made selected call output =>
    cases raw <;> try { simp [InternedEdgeResidency.nodeEdges] at selected }
    case node rawEntry rows level free =>
      have sameRaw := congrArg Prod.fst filtered
      change Value.node rawEntry rows level free = value at sameRaw
      cases sameRaw.trans same
private theorem fixed_outer_expression (selected : @Publication Symbol Guard _)
    (raw : Node) (after : Heap) (selectedRow : Row)
    (reached : Reached original [] (.binder selected.smart selected.expression) selected.environment selected.before)
    (source : SourceRow selected.expression (.reference (.interned selected.entry.identity) :: selected.environment)
      selected.allocated raw after selectedRow)
    (filtered : run (withoutSelfReference (.interned selected.entry.identity) raw) after =
      (selected.body,selected.afterBody))
    (bodySame : event.body = selected.body) : selected.expression = outerBody := by
  rcases recovered_body reached with nodeCase | unionCase
  · have bodyShape := bodySame.symm.trans (outer_shape.trans first_shape)
    rw [nodeCase] at source
    exact (node_filter_not_mu source filtered bodyShape).elim
  · exact unionCase
private theorem descent_stop {first target : Syntax Symbol Guard}
    (nonunion : ∀ members, first ≠ Syntax.union members)
    (route : UnionDescent first target) : target = first := by
  cases route with
  | refl => rfl
  | member found nested => exact (nonunion _ rfl).elim
private theorem forced_terminal {target : Syntax Symbol Guard}
    (route : UnionDescent outerBody target)
    (nonunion : ∀ members, target ≠ Syntax.union members)
    (kind : (∃ expressions, target = Syntax.node expressions) ∨
      ∃ smart body, target = Syntax.binder smart body) : target = nested := by
  cases route with
  | refl => exact (nonunion _ rfl).elim
  | @member members member terminal index found tail =>
    cases index with
    | zero =>
      have same : member = Syntax.var 0 := (Option.some.inj found).symm
      subst member
      have targetSame := descent_stop (by intro members impossible; cases impossible) tail
      rcases kind with ⟨expressions,equal⟩ | ⟨smart,body,equal⟩ <;> cases targetSame.symm.trans equal
    | succ index =>
      cases index with
      | zero =>
        have same : member = nested := (Option.some.inj found).symm
        subst member
        exact descent_stop (by intro members impossible; cases impossible) tail
      | succ index => simp at found


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
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∃ raw rawAfter,
          build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated = .done raw rawAfter ∧
          run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter = (outer.body,outer.afterBody) ∧
          Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment) ∧
          Reached original [] outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated ∧
          ∀ row, RowAt outer.body row → RowAt raw row ∧
            SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
              outer.allocated raw rawAfter row ∧
            ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression outer.expression ∧
      UnionDescent outer.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < index ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued ∧
        ∃ earlierRaw earlierRawAfter,
          build earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated = .done earlierRaw earlierRawAfter ∧
          run (withoutSelfReference (.interned earlier.entry.identity) earlierRaw) earlierRawAfter =
            (earlier.body,earlier.afterBody) ∧
          Context earlier.allocated (.reference (.interned earlier.entry.identity) :: earlier.environment) ∧
          Reached original [] earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated ∧
          RowAt earlierRaw row ∧
          SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated earlierRaw earlierRawAfter row ∧
          ∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧
            SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
              earlier.allocated earlierRaw earlierRawAfter storedRow))) ∧
      ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _, ∃ raw rawAfter,
        (events path)[outerIndex]? = some outer ∧
        Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
        outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate ∧
        outer.afterBody.nodeRecords outer.key = none ∧
        Nonempty (Path empty outer.before) ∧
        Nonempty (Path outer.before outer.afterDepth) ∧
        Nonempty (Path outer.afterDepth outer.cut) ∧
        Nonempty (Path outer.allocated outer.afterBody) ∧
        Grows outer.after sourceHeap ∧ Extends outer.after.nodes.issued sourceHeap.nodes.issued ∧
        build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter = (outer.body,outer.afterBody) ∧
        Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment) ∧
        Reached original [] outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated ∧
        RowAt raw tagRow ∧
        SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated raw rawAfter tagRow ∧
        ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter tagRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression outer.expression ∧
      UnionDescent outer.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      terminalExpression = Syntax.binder false bodySyntax ∧
      (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody tagRow ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < outerIndex ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued ∧
        ∃ earlierRaw earlierRawAfter,
          build earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated = .done earlierRaw earlierRawAfter ∧
          run (withoutSelfReference (.interned earlier.entry.identity) earlierRaw) earlierRawAfter =
            (earlier.body,earlier.afterBody) ∧
          Context earlier.allocated (.reference (.interned earlier.entry.identity) :: earlier.environment) ∧
          Reached original [] earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated ∧
          RowAt earlierRaw tagRow ∧
          SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated earlierRaw earlierRawAfter tagRow ∧
          ∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧
            SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
              earlier.allocated earlierRaw earlierRawAfter storedRow) := by
  obtain ⟨path,sites,finalWriters,precompletion,resumptions⟩ :=
    SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions original root sourceHeap source_done
  obtain ⟨outerIndex,selectedEvent,outerLookup,rooted,keySame,fullSame,missing,
    prefix,depthPath,ordinaryPath,bodyPath,growth,issued⟩ :=
    finalWriters event.key event.entry event.body event.depth event.ordinary outer_record
  have bodySame := (Value.mu.inj fullSame).2.1
  have selectedInside : RowAt selectedEvent.body row := by
    rw [← bodySame]
    exact outer_inside
  obtain ⟨observedRaw,observedAfter,built,filtered,context,reached,rows⟩ :=
    resumptions outerIndex selectedEvent outerLookup
  obtain ⟨rawRow,source,terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,terminalDone,kind,nonunion,terminalContext,terminalReached,bound,route,
    suffix,suffixIssued,choice⟩ := rows row selectedInside
  have outerExpression := fixed_outer_expression selectedEvent observedRaw observedAfter row rooted source filtered bodySame
  have actualRoute : UnionDescent outerBody terminalExpression := by simpa only [outerExpression] using route
  have targetSame := forced_terminal actualRoute nonunion kind
  have binderFacts := choice.resolve_left (by
    rintro ⟨expressions,rows,middle,sourceIndex,outputIndex,symbol,guard,children,equal,_⟩
    cases targetSame.symm.trans equal)
  refine ⟨nestedBody,original,firstMu,root,firstHeap,sourceHeap,event,firstEntry,firstBody,firstDepth,
    firstOrdinary,row,rfl,rfl,first_done,source_done,first_shape,?_,rfl,rfl,rfl,rfl,outer_shape,outer_done,
    nested_warm,outer_record,first_body_inside,row_fields.1,row_fields.2.1,row_fields.2.2,
    path,sites,finalWriters,precompletion,resumptions,
    outerIndex,selectedEvent,observedRaw,observedAfter,outerLookup,rooted,keySame,fullSame,missing,
    prefix,depthPath,ordinaryPath,bodyPath,growth,issued,built,filtered,context,reached,rawRow,source,
    terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,terminalSource,
    terminalDone,kind,nonunion,terminalContext,terminalReached,bound,route,suffix,suffixIssued,
    targetSame,binderFacts⟩
  simpa only [first_shape] using first_is_prior

/-- The same returned terminal resumes at a strict earlier indexed writer and its actual raw callback. -/
theorem actual_indexed_binder_resumption :
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
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∃ raw rawAfter,
          build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated = .done raw rawAfter ∧
          run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter = (outer.body,outer.afterBody) ∧
          Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment) ∧
          Reached original [] outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated ∧
          ∀ row, RowAt outer.body row → RowAt raw row ∧
            SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
              outer.allocated raw rawAfter row ∧
            ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression outer.expression ∧
      UnionDescent outer.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < index ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued ∧
        ∃ earlierRaw earlierRawAfter,
          build earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated = .done earlierRaw earlierRawAfter ∧
          run (withoutSelfReference (.interned earlier.entry.identity) earlierRaw) earlierRawAfter =
            (earlier.body,earlier.afterBody) ∧
          Context earlier.allocated (.reference (.interned earlier.entry.identity) :: earlier.environment) ∧
          Reached original [] earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated ∧
          RowAt earlierRaw row ∧
          SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated earlierRaw earlierRawAfter row ∧
          ∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧
            SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
              earlier.allocated earlierRaw earlierRawAfter storedRow))) ∧
      ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _, ∃ raw rawAfter,
        (events path)[outerIndex]? = some outer ∧
        Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
        outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate ∧
        outer.afterBody.nodeRecords outer.key = none ∧
        Nonempty (Path empty outer.before) ∧
        Nonempty (Path outer.before outer.afterDepth) ∧
        Nonempty (Path outer.afterDepth outer.cut) ∧
        Nonempty (Path outer.allocated outer.afterBody) ∧
        Grows outer.after sourceHeap ∧ Extends outer.after.nodes.issued sourceHeap.nodes.issued ∧
        build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter = (outer.body,outer.afterBody) ∧
        Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment) ∧
        Reached original [] outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated ∧
        RowAt raw tagRow ∧
        SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
          outer.allocated raw rawAfter tagRow ∧
        ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter tagRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression outer.expression ∧
      UnionDescent outer.expression terminalExpression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      terminalExpression = Syntax.binder false bodySyntax ∧
      (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody tagRow ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < outerIndex ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued ∧
        ∃ earlierRaw earlierRawAfter,
          build earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated = .done earlierRaw earlierRawAfter ∧
          run (withoutSelfReference (.interned earlier.entry.identity) earlierRaw) earlierRawAfter =
            (earlier.body,earlier.afterBody) ∧
          Context earlier.allocated (.reference (.interned earlier.entry.identity) :: earlier.environment) ∧
          Reached original [] earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated ∧
          RowAt earlierRaw tagRow ∧
          SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
            earlier.allocated earlierRaw earlierRawAfter tagRow ∧
          ∀ storedRow, RowAt storedBody storedRow → RowAt earlierRaw storedRow ∧
            SourceRow earlier.expression (.reference (.interned earlier.entry.identity) :: earlier.environment)
              earlier.allocated earlierRaw earlierRawAfter storedRow) := checked_witness

end MicroCFTA.OriginalIndexedResumptionFixture
