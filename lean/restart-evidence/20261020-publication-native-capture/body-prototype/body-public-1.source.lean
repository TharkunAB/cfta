import MicroCFTA.SourceCurrentBuildStructuralRowOrigins
import MicroCFTA.SourceCurrentCompletedBuildRootedWriters

/-!
# Source rows of one selected publication body

The publication stays fixed while its actual reserved callback is exposed.
Its original source route reaches the same callback entry. Self filtering
preserves the selected structural row. The raw source call then derives
its node, capture, union, or retained-winner origin.
-/
namespace MicroCFTA.SourceCurrentPublicationBodySourceRows
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentConstrainedCapSourceHistory (Context)
open InternedFreshOrdinaryActiveOrigins (Crossing Entered)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentNativeMuIssuedHistory (Path)

/-- The fixed publication derives its actual raw body call and the same structural row's source. -/
theorem publication_body_origin [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (reached : Reached root initial (.binder event.smart event.expression) event.environment event.before)
    (row : EdgeValue Symbol Guard) (inside : RowAt event.body row) :
    ∃ raw rawAfter,
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached root initial event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧
      RowAt raw row ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter row := by
  let crossing : Crossing Symbol Guard :=
    ⟨event.smart,event.expression,event.environment,event.before,.interned event.entry.identity,
      event.allocated,event.context.base,
      .fresh event.depth event.ordinary event.afterDepth event.cut
        event.depthDone event.ordinaryDone event.missing⟩
  have callbackReached : Reached root initial event.expression
      (.reference (.interned event.entry.identity) :: event.environment) event.allocated :=
    reached.enter crossing
  obtain ⟨_ordinaryContext,cutContext,allocatedContext⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.contexts event
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut
      cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  have context := allocatedContext.local (.interned event.entry.identity) argument
  obtain ⟨raw,rawAfter,built,filtered⟩ := SourceCurrentNativeMuPublicationCallbacks.callback_raw
    event.expression event.environment (.interned event.entry.identity) event.allocated
    event.body event.afterBody event.bodyDone
  have returned : Context rawAfter (.reference (.interned event.entry.identity) :: event.environment) := by
    simpa only [built,Outcome.state] using context.build event.expression
  have checked := InternedFreshOrdinaryFacts.build_verified event.expression _ event.allocated
    context.base.normal.facts context.base.inputs
  have available := checked.result raw rawAfter built
  have rawRow : RowAt raw row :=
    (SourceCurrentStoredCallbackChildContexts.filter_row rawAfter returned.base.normal
      (.interned event.entry.identity) raw available row).mp (by simpa only [filtered] using inside)
  exact ⟨raw,rawAfter,built,filtered,context,callbackReached,rawRow,
    SourceCurrentBuildStructuralRowOrigins.build_row_origin event.expression _ event.allocated
      raw rawAfter context built row rawRow⟩

/-- One rooted writer keeps its selected event, payload, issued intervals, and actual raw row source. -/
theorem written_body_origin [DecidableEq (EdgeKey Symbol Guard)]
    {root : Syntax Symbol Guard} {initial : List (Value Symbol Guard)}
    {before reader : State Symbol Guard} {key : NodeKey} {entry : Interned NodeKey}
    {body depth ordinary : Value Symbol Guard}
    (written : SourceCurrentCompletedBuildRootedWriters.Written root initial before reader key
      (.mu entry body depth ordinary))
    (row : EdgeValue Symbol Guard) (inside : RowAt body row) :
    ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
      Reached root initial (.binder event.smart event.expression) event.environment event.before ∧
      key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path before event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after reader ∧ Extends event.after.nodes.issued reader.nodes.issued ∧
      ∃ raw rawAfter,
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached root initial event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        RowAt raw row ∧
        SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated raw rawAfter row := by
  obtain ⟨event,reached,keySame,valueSame,missing,earlier,depthPath,ordinaryPath,bodyPath,growth,issued⟩ := written
  change Value.mu entry body depth ordinary = Value.mu event.entry event.body event.depth event.ordinary at valueSame
  obtain ⟨entrySame,bodySame,depthSame,ordinarySame⟩ := Value.mu.inj valueSame
  have eventRow : RowAt event.body row := bodySame ▸ inside
  exact ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,
    missing,earlier,depthPath,ordinaryPath,bodyPath,growth,issued,
    publication_body_origin event root initial reached row eventRow⟩

end MicroCFTA.SourceCurrentPublicationBodySourceRows

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentPublicationBodySourceRows.publication_body_origin
#print MicroCFTA.SourceCurrentPublicationBodySourceRows.publication_body_origin
#print axioms MicroCFTA.SourceCurrentPublicationBodySourceRows.publication_body_origin

#check @MicroCFTA.SourceCurrentPublicationBodySourceRows.written_body_origin
#print MicroCFTA.SourceCurrentPublicationBodySourceRows.written_body_origin
#print axioms MicroCFTA.SourceCurrentPublicationBodySourceRows.written_body_origin
