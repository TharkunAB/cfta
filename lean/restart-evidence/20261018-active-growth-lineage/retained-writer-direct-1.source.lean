import MicroCFTA.SourceCurrentPublicationFilterAlignment
import MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution

/-!
# Earlier Mu writers at a later physical reader

Actual source execution produces the first publication and its physical
growth into the reader. The selected writer can have a BinderFree body
without any restriction on the other source publications or its captures.
-/
namespace MicroCFTA.SourceCurrentRetainedMuWriterAlignment
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedFacts InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedStoredMuOrigins (filter_noNewMu)
open InternedConstructionProvenance InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History Publication)
open SourceEqualityRequiredCache (Ready Keeps)

/-- The exact first writer precedes this reader, including issued references. -/
def Writer [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (key : NodeKey)
    (value : Value Symbol Guard) (event : Publication (Symbol := Symbol) (Guard := Guard)) : Prop :=
  key = event.key ∧ value = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
    Nonempty (History empty event.before) ∧
    Nonempty (History event.before event.afterDepth) ∧
    Nonempty (History event.afterDepth event.cut) ∧
    Nonempty (History event.allocated event.afterBody) ∧
    Grows event.afterBody reader ∧ Extends event.afterBody.nodes.issued reader.nodes.issued

/-- Physical growth retains the same earlier writer and every callback history. -/
theorem Writer.grows [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    {event : Publication (Symbol := Symbol) (Guard := Guard)}
    (writer : Writer before key value event) (growth : Grows before after)
    (issued : Extends before.nodes.issued after.nodes.issued) : Writer after key value event := by
  obtain ⟨key,value,first,prefix,depth,ordinary,body,earlier,history⟩ := writer
  exact ⟨key,value,first,prefix,depth,ordinary,body,grows_trans earlier growth,extends_trans history issued⟩

private def Heap [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, reader.nodeRecords key = some (.mu entry body depth ordinary) →
    ∃ event, Writer reader key (.mu entry body depth ordinary) event

private theorem empty_heap [DecidableEq (EdgeKey Symbol Guard)] :
    Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

private theorem preserve [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (known : Heap before) (old : NoNewMu before after) (growth : Grows before after)
    (issued : Extends before.nodes.issued after.nodes.issued) : Heap after := by
  intro key entry body depth ordinary present
  obtain ⟨event,writer⟩ := known key entry body depth ordinary (old key entry body depth ordinary present)
  exact ⟨event,writer.grows growth issued⟩

private theorem work_heap [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard Result)
    (before : State Symbol Guard) (valid : Valid before) (known : Heap before)
    (old : NoNewMu before (run job before).2) : Heap (run job before).2 :=
  preserve before _ known old (run_correct job before valid).2 (run_issued_extends job before valid)

private theorem bind_heap [DecidableEq (EdgeKey Symbol Guard)]
    (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (known : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact known
  | done value after => exact later value after rfl known

private theorem callback_history [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (name : Reference) (before : State Symbol Guard) (context : Context before environment)
    (available : Available before (.reference name)) :
    Nonempty (History before (callback expression environment name before).state) := by
  obtain ⟨history⟩ := SourceCurrentNativeMuPublication.build_history expression _ before (context.local name available)
  cases actual : build expression (.reference name :: environment) before with
  | pending key after => simpa only [callback,actual,Outcome.bind,Outcome.state] using Nonempty.intro history
  | done value after =>
      have raw : History before after := by simpa only [actual,Outcome.state] using history
      exact ⟨by simpa only [callback,actual,Outcome.bind,work,Outcome.state] using
        History.trans raw (.retain after _ (filter_noNewMu name value after))⟩

private theorem callback_prefix [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (name : Reference) (before : State Symbol Guard) (context : Context before environment)
    (available : Available before (.reference name)) (prefix : History empty before)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : callback expression environment name before = .done value after) : History empty after := by
  obtain ⟨history⟩ := callback_history expression environment name before context available
  exact .trans prefix (by simpa only [actual,Outcome.state] using history)

private theorem complete_heap [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) (known : Heap event.afterBody)
    (prefix : History empty event.before) : Heap event.after := by
  have growth : Grows event.afterBody event.after :=
    ⟨extends_refl _,extends_refl _,extends_refl _,keepFirst_extends _ _ _⟩
  have issued : Extends event.afterBody.nodes.issued event.after.nodes.issued := extends_refl _
  intro key entry body depth ordinary present
  cases first : event.afterBody.nodeRecords event.key with
  | some previous =>
      have old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary) := by
        change keepFirst event.afterBody.nodeRecords event.key event.candidate key = _ at present
        simpa only [keepFirst,first] using present
      obtain ⟨earlier,writer⟩ := known key entry body depth ordinary old
      exact ⟨earlier,writer.grows growth issued⟩
  | none =>
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨keyEqual,valueEqual⟩
      · obtain ⟨earlier,writer⟩ := known key entry body depth ordinary old
        exact ⟨earlier,writer.grows growth issued⟩
      · obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
        have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
          (reserve_available event.key event.cut cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
        refine ⟨event,keyEqual,valueEqual,first,⟨prefix⟩,?_,?_,?_,growth,issued⟩
        · have history := callback_history event.expression event.environment .depth event.before
            event.context (depth_available event.before)
          simpa only [event.depthDone,Outcome.state] using history
        · have history := callback_history event.expression event.environment (.uninterned (ordinaryLevel event.depth))
            event.afterDepth depthContext (ordinary_available _ _)
          simpa only [event.ordinaryDone,Outcome.state] using history
        · have actual : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
              .done event.body event.afterBody := event.bodyDone
          have history := callback_history event.expression event.environment (.interned event.entry.identity)
            event.allocated bodyContext bodyArgument
          simpa only [actual,Outcome.state] using history

mutual
private theorem build_writers [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (prefix : History empty state) (known : Heap state) :
    Heap (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build,Outcome.state] using known
  | node rows =>
      rw [build]
      apply bind_heap _ _ (edges_writers rows environment state context prefix known)
      intro edges after actual afterKnown
      have facts := (buildEdges_verified rows environment state context.base.normal.facts context.base.inputs).facts
      have valid : Valid after := by simpa only [actual,Outcome.state] using facts.coherent.valid
      exact work_heap (makeNode edges) after valid afterKnown (makeNode_noNewMu edges after)
  | union members =>
      rw [build]
      apply bind_heap _ _ (many_writers members environment state context prefix known)
      intro values after actual afterKnown
      have facts := (buildMany_verified members environment state context.base.normal.facts context.base.inputs).facts
      have valid : Valid after := by simpa only [actual,Outcome.state] using facts.coherent.valid
      exact work_heap (makeUnion values) after valid afterKnown (makeUnion_noNewMu values after)
  | binder smart body =>
      have checked : ∀ name current, Context current environment → History empty current →
          Available current (.reference name) → Heap current → Heap (callback body environment name current).state := by
        intro name current currentContext currentPrefix argument currentKnown
        apply bind_heap _ _ (build_writers body _ current (currentContext.local name argument) currentPrefix currentKnown)
        intro value after actual afterKnown
        have facts := (build_verified body _ current currentContext.base.normal.facts
          (currentContext.local name argument).base.inputs).facts
        have valid : Valid after := by simpa only [actual,Outcome.state] using facts.coherent.valid
        exact work_heap (withoutSelfReference name value) after valid afterKnown (filter_noNewMu name value after)
      rw [build]
      change Heap ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary cut =>
          request smart depth ordinary (callback body environment) cut).state
      apply bind_heap _ _ (checked .depth state context prefix (depth_available state) known)
      intro depth afterDepth depthDone depthKnown
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone,Outcome.state] using context.callback body .depth (depth_available state)
      have depthPrefix := callback_prefix body environment .depth state context (depth_available state) prefix depth afterDepth depthDone
      apply bind_heap _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext depthPrefix
        (ordinary_available _ _) depthKnown)
      intro ordinary cut ordinaryDone cutKnown
      have cutContext : Context cut environment := by
        simpa only [ordinaryDone,Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available _ _)
      have cutPrefix := callback_prefix body environment (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available _ _) depthPrefix ordinary cut ordinaryDone
      cases missing : cut.nodes.table (muKey depth ordinary) with
      | some entry =>
          cases present : cut.nodeRecords (muKey depth ordinary) <;>
            simpa only [request,missing,present,Outcome.state] using cutKnown
      | none =>
          let entry := Cache.intern cut.nodes (muKey depth ordinary)
          let allocated := {cut with nodes := entry.2}
          have reserved : Context allocated environment := cutContext.reserve (muKey depth ordinary)
          have argument : Available allocated (.reference (.interned entry.1.identity)) :=
            (reserve_available (muKey depth ordinary) cut cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
          have reserveGrowth : Grows cut allocated :=
            ⟨extends_refl _,InternedBinderProtocol.intern_grows _ _,extends_refl _,extends_refl _⟩
          have reserveIssued := intern_issued_extends cut.nodes (muKey depth ordinary) cutContext.base.normal.facts.coherent.valid.2
          have allocatedKnown : Heap allocated := preserve cut allocated cutKnown (fun _ _ _ _ _ found => found) reserveGrowth reserveIssued
          have allocatedPrefix : History empty allocated := .trans cutPrefix (.retain cut allocated (fun _ _ _ _ _ found => found))
          have actualKnown := checked (.interned entry.1.identity) allocated reserved allocatedPrefix argument allocatedKnown
          simp only [request,missing]
          change Heap ((callback body environment (.interned entry.1.identity) allocated).bind
            (fun value after => complete smart entry.1 value depth ordinary after)).state
          apply bind_heap _ _ actualKnown
          intro result afterBody bodyDone afterKnown
          let event : Publication (Symbol := Symbol) (Guard := Guard) :=
            ⟨smart,body,environment,state,afterDepth,cut,afterBody,depth,ordinary,result,
              context,depthDone,ordinaryDone,missing,bodyDone⟩
          exact complete_heap event afterKnown prefix
termination_by sizeOf expression

private theorem many_writers [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (prefix : History empty state) (known : Heap state) :
    Heap (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany,Outcome.state] using known
  | cons first rest =>
      rw [buildMany]
      apply bind_heap _ _ (build_writers first environment state context prefix known)
      intro value after actual afterKnown
      have laterContext : Context after environment := by simpa only [actual,Outcome.state] using context.build first
      obtain ⟨history⟩ := SourceCurrentNativeMuPublication.build_history first environment state context
      have laterPrefix : History empty after := .trans prefix (by simpa only [actual,Outcome.state] using history)
      exact bind_heap _ _ (many_writers rest environment after laterContext laterPrefix afterKnown)
        (fun _ _ _ finalKnown => finalKnown)
termination_by sizeOf expressions

private theorem edges_writers [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (prefix : History empty state) (known : Heap state) :
    Heap (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges,Outcome.state] using known
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [buildEdges]
          apply bind_heap _ _ (many_writers children environment state context prefix known)
          intro values after actual afterKnown
          have laterContext : Context after environment := by simpa only [actual,Outcome.state] using context.many children
          obtain ⟨history⟩ := SourceCurrentNativeMuPublication.buildMany_history children environment state context
          have laterPrefix : History empty after := .trans prefix (by simpa only [actual,Outcome.state] using history)
          have valid := laterContext.base.normal.facts.coherent.valid
          let result := run (makeEdge symbol guard values) after
          have available := (buildMany_verified children environment state context.base.normal.facts context.base.inputs).result values after actual
          have edgeContext : Context result.2 environment := laterContext.edge symbol guard values available
          have edgeKnown : Heap result.2 := work_heap (makeEdge symbol guard values) after valid afterKnown (fun _ _ _ _ _ found => found)
          have edgePrefix : History empty result.2 := .trans laterPrefix (.retain after result.2 (fun _ _ _ _ _ found => found))
          change Heap ((buildEdges rest environment result.2).bind _).state
          exact bind_heap _ _ (edges_writers rest environment result.2 edgeContext edgePrefix edgeKnown)
            (fun _ _ _ finalKnown => finalKnown)
termination_by sizeOf expressions
end

/-- Every source-started selected Mu has its exact earlier writer and physical reader transport. -/
theorem source_writer [DecidableEq (EdgeKey Symbol Guard)] (source : Syntax Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : (build source [] empty).state.nodeRecords key = some (.mu entry body depth ordinary)) :
    ∃ event, Writer (build source [] empty).state key (.mu entry body depth ordinary) event :=
  build_writers source [] empty SourceCurrentConstrainedCapSourceHistory.empty_context (.refl _) empty_heap
    key entry body depth ordinary present

end MicroCFTA.SourceCurrentRetainedMuWriterAlignment
