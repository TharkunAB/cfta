import MicroCFTA.SourceCurrentWarmBuildRowOrigins
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# One actual warm source build retains its entry Mu row

This fixture reuses the earlier nested and outer binder source family.
The initial completed nested build supplies the warm heap and Context.
The new consumer fixes one path for every returned writer and row.
-/
noncomputable section
namespace MicroCFTA.WarmBuildRowFixture
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
open SourceCurrentWarmBuildRowOrigins (RowOrigin)
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
set_option Elab.async false
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
private def inputs : List Node := [.reference (.interned event.entry.identity)]
private theorem outer_done : build outer [] firstHeap = .done event.candidate event.after := by cbv
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


private theorem first_key : firstHeap.nodes.table (muKey firstDepth firstOrdinary) = some firstEntry := by cbv
private theorem first_probes : firstOrdinary = firstDepth := by cbv
private theorem first_callback : callback nestedBody [] .depth firstHeap = .done firstDepth firstHeap := by cbv
private theorem target_missing : firstHeap.nodeRecords event.key = none := by cbv
private theorem target_selected : event.after.nodeRecords event.key = some event.candidate := by cbv
private theorem outer_inside : RowAt event.body row := by rw [outer_shape]; exact first_inside
private def bodyEntry : Interned NodeKey := match firstBody with
  | .node entry .. => entry | _ => ⟨0,.empty⟩
private theorem first_records : firstHeap.nodeRecords =
    keepFirst (keepFirst (fun _ => none) bodyEntry.key firstBody) firstEntry.key firstMu := by cbv
private theorem first_body_node : ∃ entry edges depth free,
    firstBody = Value.node entry edges depth free := by
  cbv
  exact ⟨_,_,_,_,rfl⟩
private theorem only_first_full (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (found : firstHeap.nodeRecords key = some (.mu entry body depth ordinary)) :
    Value.mu entry body depth ordinary = firstMu := by
  rw [first_records] at found
  rcases InternedRecordCoherence.record_cases _ _ _ _ _ found with earlier | ⟨_same,full⟩
  · rcases InternedRecordCoherence.record_cases _ _ _ _ _ earlier with absent | ⟨_same,notMu⟩
    · cases absent
    · obtain ⟨_,_,_,_,bodyShape⟩ := first_body_node
      rw [bodyShape] at notMu
      cases notMu
  · exact full

private theorem event_before {before after : Heap} (path : Path before after)
    (selected : @Publication Symbol Guard _) (present : selected ∈ events path) : Grows before selected.before := by
  induction path with
  | refl | retain => simp only [events,List.not_mem_nil] at present
  | trans first next firstIH nextIH =>
    rcases List.mem_append.mp present with here | later
    · exact firstIH here
    · exact grows_trans first.growth (nextIH later)
  | publication own depth ordinary body depthIH ordinaryIH bodyIH =>
    simp only [events,List.mem_append,List.mem_singleton] at present
    rcases present with ((inDepth | inOrdinary) | inBody) | same
    · exact depthIH inDepth
    · exact grows_trans depth.growth (ordinaryIH inOrdinary)
    · exact grows_trans depth.growth (grows_trans ordinary.growth
        (grows_trans (SourceCurrentNativeMuGrowthHistory.reserve_growth own) (bodyIH inBody)))
    · cases same
      exact grows_refl _

private theorem constant_callback (inputs : List Node) (name : Reference) :
    callback nestedBody inputs name firstHeap = .done firstDepth firstHeap := by cbv
private theorem callback_later (inputs : List Node) (name : Reference) (state : Heap)
    (growth : Grows firstHeap state) : callback nestedBody inputs name state = .done firstDepth state := by
  exact InternedFreshOrdinaryReplay.callback_replays nestedBody inputs name firstHeap state firstDepth firstHeap
    first_context.base.normal.facts.coherent.valid (constant_callback inputs name) growth

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
private theorem event_expression {after : Heap} (path : Path firstHeap after)
    (selected : @Publication Symbol Guard _) (index : Nat)
    (found : (events path)[index]? = some selected)
    (reached : Reached outer [] (.binder selected.smart selected.expression) selected.environment selected.before) :
    selected.expression = outerBody := by
  obtain ⟨crossings,active,_⟩ := reached
  rcases outer_binder_path active with nodeCase | unionCase
  · have growth := event_before path selected (List.mem_of_getElem? found)
    have depthDone := selected.depthDone
    rw [nodeCase] at depthDone
    have depthSame := Outcome.done.inj (depthDone.symm.trans
      (callback_later selected.environment .depth selected.before growth))
    have ordinaryDone := selected.ordinaryDone
    rw [nodeCase,depthSame.1,depthSame.2] at ordinaryDone
    have ordinarySame := Outcome.done.inj (ordinaryDone.symm.trans
      (callback_later selected.environment (.uninterned (ordinaryLevel firstDepth)) selected.before growth))
    have present := growth.nodes (muKey firstDepth firstDepth) firstEntry (by simpa only [first_probes] using first_key)
    have missing := selected.missing
    rw [depthSame.1,ordinarySame.1,ordinarySame.2] at missing
    rw [missing] at present
    cases present
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


private theorem publication_allocated (selected : @Publication Symbol Guard _) :
    Grows selected.before selected.allocated := by
  have depthGrowth : Grows selected.before selected.afterDepth := by
    simpa only [selected.depthDone,Outcome.state] using
      (InternedFreshOrdinaryActiveOrigins.callback_growing selected.expression selected.environment .depth
        selected.before selected.context.base.normal.facts.coherent.valid).2
  have afterContext := (SourceCurrentNativeMuPublicationCallbacks.contexts selected).1
  have ordinaryGrowth : Grows selected.afterDepth selected.cut := by
    simpa only [selected.ordinaryDone,Outcome.state] using
      (InternedFreshOrdinaryActiveOrigins.callback_growing selected.expression selected.environment
        (.uninterned (ordinaryLevel selected.depth)) selected.afterDepth
        afterContext.base.normal.facts.coherent.valid).2
  exact grows_trans depthGrowth (grows_trans ordinaryGrowth
    (SourceCurrentNativeMuGrowthHistory.reserve_growth selected))

private theorem checked_witness :
    build nested [] (empty : Heap) = .done firstMu firstHeap ∧ Context firstHeap [] ∧
    firstMu = .mu firstEntry firstBody firstDepth firstOrdinary ∧
    firstHeap.nodeRecords (muKey firstDepth firstOrdinary) = some (.mu firstEntry firstBody firstDepth firstOrdinary) ∧
    firstHeap.nodeRecords event.key = none ∧
    build outer [] firstHeap = .done event.candidate event.after ∧
    event.after.nodeRecords event.key = some event.candidate ∧
    row.entry.key.symbol = ("tag17",.top) ∧ row.entry.key.constraint = top ∧ row.children = [] ∧
    RowAt event.body row ∧
    event.allocated.nodes.table (muKey firstDepth firstOrdinary) = some firstEntry ∧
    event.allocated.nodeRecords (muKey firstDepth firstOrdinary) = some (.mu firstEntry firstBody firstDepth firstOrdinary) ∧
    request false firstDepth firstOrdinary (callback nestedBody inputs) event.allocated = .done firstMu event.allocated ∧
    (let original := outer
     let initial : List Node := []
     let before := firstHeap
     let after := event.after
    ∃ path : Path before after,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original initial (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        after.nodeRecords key = some (.mu entry body depth ordinary) →
        before.nodeRecords key = some (.mu entry body depth ordinary) ∨
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original initial (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path before event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ key entry body depth ordinary,
          outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
          before.nodeRecords key = some (.mu entry body depth ordinary) ∨
          ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
            Reached original initial (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
            key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
            earlier.afterBody.nodeRecords earlier.key = none ∧
            Nonempty (Path before earlier.before) ∧
            Nonempty (Path earlier.before earlier.afterDepth) ∧
            Nonempty (Path earlier.afterDepth earlier.cut) ∧
            Nonempty (Path earlier.allocated earlier.afterBody) ∧
            Grows earlier.after outer.afterBody ∧
            Extends earlier.after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ row, RowAt outer.body row → RowOrigin original initial before path index outer row) ∧
      ∃ targetIndex : Nat, ∃ selected : @Publication Symbol Guard _,
        (events path)[targetIndex]? = some selected ∧
        Reached original initial (.binder selected.smart selected.expression) selected.environment selected.before ∧
        event.key = selected.key ∧ event.candidate = selected.candidate ∧
        selected.afterBody.nodeRecords selected.key = none ∧
        Nonempty (Path before selected.before) ∧ Nonempty (Path selected.before selected.afterDepth) ∧
        Nonempty (Path selected.afterDepth selected.cut) ∧ Nonempty (Path selected.allocated selected.afterBody) ∧
        Grows selected.after after ∧ Extends selected.after.nodes.issued after.nodes.issued ∧
        ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
          producerIndex ≤ targetIndex ∧ (events path)[producerIndex]? = some producer ∧
          producer.expression = outerBody ∧
          ∃ raw rawAfter,
            build producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
              producer.allocated = .done raw rawAfter ∧
            run (withoutSelfReference (.interned producer.entry.identity) raw) rawAfter = (producer.body,producer.afterBody) ∧
            Context producer.allocated (.reference (.interned producer.entry.identity) :: producer.environment) ∧
            Reached original initial producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
              producer.allocated ∧ RowAt raw row ∧
            SourceRow producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
              producer.allocated raw rawAfter row ∧
          ∃ terminalExpression terminalInputs terminalStart terminalValue terminalStop,
            SourceRow terminalExpression terminalInputs terminalStart terminalValue terminalStop row ∧
            build terminalExpression terminalInputs terminalStart = .done terminalValue terminalStop ∧
            Context terminalStart terminalInputs ∧ Reached original initial terminalExpression terminalInputs terminalStart ∧
            Grows producer.allocated terminalStart ∧
            Extends producer.allocated.nodes.issued terminalStart.nodes.issued ∧
            terminalInputs = (.reference (.interned producer.entry.identity) :: producer.environment) ∧
            SyntaxBound terminalExpression producer.expression ∧
            UnionDescent producer.expression terminalExpression ∧
            Grows terminalStop rawAfter ∧ Extends terminalStop.nodes.issued rawAfter.nodes.issued ∧
            Grows rawAfter producer.afterBody ∧ Extends rawAfter.nodes.issued producer.afterBody.nodes.issued ∧
            Grows terminalStop selected.afterBody ∧ Extends terminalStop.nodes.issued selected.afterBody.nodes.issued ∧
          ∃ smart body tDepth tAfterDepth tOrdinary tCut tEntry tBody,
            terminalExpression = .binder smart body ∧ terminalExpression = nested ∧
            smart = false ∧ body = nestedBody ∧
            callback body terminalInputs .depth terminalStart = .done tDepth tAfterDepth ∧
            callback body terminalInputs (.uninterned (ordinaryLevel tDepth)) tAfterDepth = .done tOrdinary tCut ∧
            request smart tDepth tOrdinary (callback body terminalInputs) tCut = .done terminalValue terminalStop ∧
            terminalStop.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary) ∧
            terminalValue = finish smart (.mu tEntry tBody tDepth tOrdinary) ∧ RowAt tBody row ∧
            before.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary) ∧
            Value.mu tEntry tBody tDepth tOrdinary = firstMu ∧
            Grows before tCut ∧
            tCut.nodes.table (muKey tDepth tOrdinary) = some tEntry ∧
            tCut.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary) ∧
            terminalStop = tCut ∧ terminalValue = firstMu ∧
            request smart tDepth tOrdinary (callback body terminalInputs) tCut = .done firstMu tCut) := by
  obtain ⟨path,sites,writers,precompletion,origins⟩ :=
    SourceCurrentWarmBuildRowOrigins.build_row_origins outer [] firstHeap first_context event.candidate event.after outer_done
  have selected : event.after.nodeRecords event.key = some (.mu event.entry event.body event.depth event.ordinary) := target_selected
  rcases writers event.key event.entry event.body event.depth event.ordinary selected with old | selectedWriter
  · rw [target_missing] at old
    cases old
  · obtain ⟨targetIndex,selected,lookup,selectedReached,keySame,fullSame,missing,
      initialPath,depthPath,ordinaryPath,bodyPath,growth,issued⟩ := selectedWriter
    have bodySame : event.body = selected.body := (Value.mu.inj fullSame).2.1
    have inside : RowAt selected.body row := bodySame ▸ outer_inside
    obtain ⟨producerIndex,producer,less,producerLookup,raw,rawAfter,built,filtered,rawContext,rawReached,
      rawRow,rawSource,terminalExpression,terminalInputs,terminalStart,terminalValue,terminalStop,
      terminalSource,terminalBuilt,terminalContext,terminalReached,entryGrowth,entryIssued,inputsSame,
      small,route,suffix,suffixIssued,filterGrowth,filterIssued,toOuter,toOuterIssued,choice⟩ :=
      origins targetIndex selected lookup row inside
    have producerBody := event_expression path producer producerIndex producerLookup (sites _ _ producerLookup)
    have routeOuter : UnionDescent outerBody terminalExpression := producerBody ▸ route
    rcases choice with node | capture | binder
    · obtain ⟨expressions,rows,middle,sourceIndex,outputIndex,symbol,guard,children,same,rest⟩ := node
      have nonunion : ∀ members, terminalExpression ≠ Syntax.union members := by
        intro members impossible
        cases same.symm.trans impossible
      have terminalSame := forced_terminal routeOuter nonunion (.inl ⟨expressions,same⟩)
      cases terminalSame.symm.trans same
    · obtain ⟨slot,captured,crossings,originalSlot,same,found,inside,active,offset,initialFound⟩ := capture
      simp only [List.getElem?_nil] at initialFound
      cases initialFound
    · obtain ⟨smart,body,tDepth,tAfterDepth,tOrdinary,tCut,tEntry,tBody,same,depthDone,ordinaryDone,
        requested,present,returned,storedRow,prior⟩ := binder
      have nonunion : ∀ members, terminalExpression ≠ Syntax.union members := by
        intro members impossible
        cases same.symm.trans impossible
      have terminalSame := forced_terminal routeOuter nonunion (.inr ⟨smart,body,same⟩)
      have shape := Syntax.binder.inj (terminalSame.symm.trans same)
      have smartSame : smart = false := shape.1.symm
      have bodyShape : body = nestedBody := shape.2.symm
      have priorSame := only_first_full _ tEntry tBody tDepth tOrdinary prior
      have payload := Value.mu.inj (priorSame.trans first_shape)
      have sourceGrowth := grows_trans (event_before path producer (List.mem_of_getElem? producerLookup))
        (grows_trans (publication_allocated producer) entryGrowth)
      have depthGrowth : Grows terminalStart tAfterDepth := by
        simpa only [depthDone,Outcome.state] using
          (InternedFreshOrdinaryActiveOrigins.callback_growing body terminalInputs .depth terminalStart
            terminalContext.base.normal.facts.coherent.valid).2
      have afterContext : Context tAfterDepth terminalInputs := by
        simpa only [depthDone,Outcome.state] using
          terminalContext.callback body .depth (InternedNestedProvenance.depth_available terminalStart)
      have ordinaryGrowth : Grows tAfterDepth tCut := by
        simpa only [ordinaryDone,Outcome.state] using
          (InternedFreshOrdinaryActiveOrigins.callback_growing body terminalInputs
            (.uninterned (ordinaryLevel tDepth)) tAfterDepth afterContext.base.normal.facts.coherent.valid).2
      have toCut := grows_trans sourceGrowth (grows_trans depthGrowth ordinaryGrowth)
      have cutKey : tCut.nodes.table (muKey tDepth tOrdinary) = some tEntry := by
        simpa only [payload.1,payload.2.2.1,payload.2.2.2] using
          toCut.nodes _ _ first_key
      have cutRecord : tCut.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary) := by
        simpa only [payload.1,payload.2.1,payload.2.2.1,payload.2.2.2] using
          toCut.nodeRecords _ _ first_is_prior
      have warm : request smart tDepth tOrdinary (callback body terminalInputs) tCut =
          .done (finish smart (.mu tEntry tBody tDepth tOrdinary)) tCut := by
        simp only [request,cutKey,cutRecord]
      have warmSame := Outcome.done.inj (requested.symm.trans warm)
      have valueSame : terminalValue = firstMu := by
        simpa only [smartSame,finish,Bool.false_eq_true,ite_false] using returned.trans (congrArg (finish smart) priorSame)
      have warmResult : request smart tDepth tOrdinary (callback body terminalInputs) tCut = .done firstMu tCut := by
        simpa only [warmSame.2,valueSame] using requested
      exact ⟨first_done,first_context,first_shape,first_is_prior,target_missing,outer_done,target_selected,
        row_fields.1,row_fields.2.1,row_fields.2.2,outer_inside,warm_key,warm_record,warm_request,
        path,sites,writers,precompletion,origins,targetIndex,selected,lookup,selectedReached,keySame,fullSame,
        missing,initialPath,depthPath,ordinaryPath,bodyPath,growth,issued,
        producerIndex,producer,less,producerLookup,producerBody,raw,rawAfter,built,filtered,rawContext,rawReached,
        rawRow,rawSource,terminalExpression,terminalInputs,terminalStart,terminalValue,terminalStop,terminalSource,
        terminalBuilt,terminalContext,terminalReached,entryGrowth,entryIssued,inputsSame,small,route,suffix,suffixIssued,
        filterGrowth,filterIssued,toOuter,toOuterIssued,smart,body,tDepth,tAfterDepth,tOrdinary,tCut,tEntry,tBody,
        same,terminalSame,smartSame,bodyShape,depthDone,ordinaryDone,requested,present,returned,storedRow,prior,
        priorSame,toCut,cutKey,cutRecord,warmSame.2,valueSame,warmResult⟩

/-- One actual warm build retains the same indexed entry Mu row and cache hit. -/
theorem actual_warm_entry_row :
    build nested [] (empty : Heap) = .done firstMu firstHeap ∧ Context firstHeap [] ∧
    firstMu = .mu firstEntry firstBody firstDepth firstOrdinary ∧
    firstHeap.nodeRecords (muKey firstDepth firstOrdinary) = some (.mu firstEntry firstBody firstDepth firstOrdinary) ∧
    firstHeap.nodeRecords event.key = none ∧
    build outer [] firstHeap = .done event.candidate event.after ∧
    event.after.nodeRecords event.key = some event.candidate ∧
    row.entry.key.symbol = ("tag17",.top) ∧ row.entry.key.constraint = top ∧ row.children = [] ∧
    RowAt event.body row ∧
    event.allocated.nodes.table (muKey firstDepth firstOrdinary) = some firstEntry ∧
    event.allocated.nodeRecords (muKey firstDepth firstOrdinary) = some (.mu firstEntry firstBody firstDepth firstOrdinary) ∧
    request false firstDepth firstOrdinary (callback nestedBody inputs) event.allocated = .done firstMu event.allocated ∧
    (let original := outer
     let initial : List Node := []
     let before := firstHeap
     let after := event.after
    ∃ path : Path before after,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original initial (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        after.nodeRecords key = some (.mu entry body depth ordinary) →
        before.nodeRecords key = some (.mu entry body depth ordinary) ∨
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original initial (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path before event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ key entry body depth ordinary,
          outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
          before.nodeRecords key = some (.mu entry body depth ordinary) ∨
          ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
            Reached original initial (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
            key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
            earlier.afterBody.nodeRecords earlier.key = none ∧
            Nonempty (Path before earlier.before) ∧
            Nonempty (Path earlier.before earlier.afterDepth) ∧
            Nonempty (Path earlier.afterDepth earlier.cut) ∧
            Nonempty (Path earlier.allocated earlier.afterBody) ∧
            Grows earlier.after outer.afterBody ∧
            Extends earlier.after.nodes.issued outer.afterBody.nodes.issued) ∧
      (∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ row, RowAt outer.body row → RowOrigin original initial before path index outer row) ∧
      ∃ targetIndex : Nat, ∃ selected : @Publication Symbol Guard _,
        (events path)[targetIndex]? = some selected ∧
        Reached original initial (.binder selected.smart selected.expression) selected.environment selected.before ∧
        event.key = selected.key ∧ event.candidate = selected.candidate ∧
        selected.afterBody.nodeRecords selected.key = none ∧
        Nonempty (Path before selected.before) ∧ Nonempty (Path selected.before selected.afterDepth) ∧
        Nonempty (Path selected.afterDepth selected.cut) ∧ Nonempty (Path selected.allocated selected.afterBody) ∧
        Grows selected.after after ∧ Extends selected.after.nodes.issued after.nodes.issued ∧
        ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
          producerIndex ≤ targetIndex ∧ (events path)[producerIndex]? = some producer ∧
          producer.expression = outerBody ∧
          ∃ raw rawAfter,
            build producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
              producer.allocated = .done raw rawAfter ∧
            run (withoutSelfReference (.interned producer.entry.identity) raw) rawAfter = (producer.body,producer.afterBody) ∧
            Context producer.allocated (.reference (.interned producer.entry.identity) :: producer.environment) ∧
            Reached original initial producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
              producer.allocated ∧ RowAt raw row ∧
            SourceRow producer.expression (.reference (.interned producer.entry.identity) :: producer.environment)
              producer.allocated raw rawAfter row ∧
          ∃ terminalExpression terminalInputs terminalStart terminalValue terminalStop,
            SourceRow terminalExpression terminalInputs terminalStart terminalValue terminalStop row ∧
            build terminalExpression terminalInputs terminalStart = .done terminalValue terminalStop ∧
            Context terminalStart terminalInputs ∧ Reached original initial terminalExpression terminalInputs terminalStart ∧
            Grows producer.allocated terminalStart ∧
            Extends producer.allocated.nodes.issued terminalStart.nodes.issued ∧
            terminalInputs = (.reference (.interned producer.entry.identity) :: producer.environment) ∧
            SyntaxBound terminalExpression producer.expression ∧
            UnionDescent producer.expression terminalExpression ∧
            Grows terminalStop rawAfter ∧ Extends terminalStop.nodes.issued rawAfter.nodes.issued ∧
            Grows rawAfter producer.afterBody ∧ Extends rawAfter.nodes.issued producer.afterBody.nodes.issued ∧
            Grows terminalStop selected.afterBody ∧ Extends terminalStop.nodes.issued selected.afterBody.nodes.issued ∧
          ∃ smart body tDepth tAfterDepth tOrdinary tCut tEntry tBody,
            terminalExpression = .binder smart body ∧ terminalExpression = nested ∧
            smart = false ∧ body = nestedBody ∧
            callback body terminalInputs .depth terminalStart = .done tDepth tAfterDepth ∧
            callback body terminalInputs (.uninterned (ordinaryLevel tDepth)) tAfterDepth = .done tOrdinary tCut ∧
            request smart tDepth tOrdinary (callback body terminalInputs) tCut = .done terminalValue terminalStop ∧
            terminalStop.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary) ∧
            terminalValue = finish smart (.mu tEntry tBody tDepth tOrdinary) ∧ RowAt tBody row ∧
            before.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary) ∧
            Value.mu tEntry tBody tDepth tOrdinary = firstMu ∧
            Grows before tCut ∧
            tCut.nodes.table (muKey tDepth tOrdinary) = some tEntry ∧
            tCut.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary) ∧
            terminalStop = tCut ∧ terminalValue = firstMu ∧
            request smart tDepth tOrdinary (callback body terminalInputs) tCut = .done firstMu tCut) := checked_witness

end MicroCFTA.WarmBuildRowFixture
