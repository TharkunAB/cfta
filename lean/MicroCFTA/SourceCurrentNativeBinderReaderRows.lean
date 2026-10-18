import MicroCFTA.SourceCurrentNativeConstructReaderReadback

/-!
# Ordinary rows from an actual smart binder at a later reader

The completed binder supplies the exact current callback and raw row schedule.
The selected record grows forward into the reader's publication history.
-/
namespace MicroCFTA.SourceCurrentNativeBinderReaderRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open MergedFreshOrdinaryGraph (Origin)

/-- A selected ordinary row retains the actual binder schedule and current raw row origins. -/
def Rows [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (value : Value Symbol Guard) (after reader : State Symbol Guard)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ depth afterDepth ordinary cut raw middle entry storedBody,
    callback body environment .depth before = .done depth afterDepth ∧
    callback body environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
    request true depth ordinary (callback body environment) cut = .done value after ∧
    build body (.reference (.uninterned (ordinaryLevel depth)) :: environment) afterDepth = .done raw middle ∧
    run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) middle = (ordinary,cut) ∧
    Context afterDepth environment ∧ Context cut environment ∧ Context after environment ∧
    Context middle (.reference (.uninterned (ordinaryLevel depth)) :: environment) ∧ Available middle raw ∧
    Grows before afterDepth ∧ Extends before.nodes.issued afterDepth.nodes.issued ∧
    Grows afterDepth middle ∧ Extends afterDepth.nodes.issued middle.nodes.issued ∧
    Grows middle after ∧ Extends middle.nodes.issued after.nodes.issued ∧
    Grows before middle ∧ Extends before.nodes.issued middle.nodes.issued ∧
    Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
    after.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
    reader.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
    value = finish true (.mu entry storedBody depth ordinary) ∧
    InternedFreshOrdinaryDepthHeap.Correct entry storedBody depth ordinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
    value = storedBody ∧ .interned entry.identity ∉ storedBody.free ∧
    (nodeEdges storedBody)[rowIndex]? = some row ∧
    value = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary ∧
    (∀ view edge, Origin view [value] edge ↔ Origin view [raw] edge) ∧
    ∀ view, Origin view [raw] row

/-- A completed smart binder derives current raw row origins from a later actual history. -/
theorem binder_row [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (context : Context before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : build (.binder true body) environment before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges value)[rowIndex]? = some row) :
    Rows body environment before value after reader rowIndex row := by
  obtain ⟨depth,afterDepth,ordinary,cut,raw,middle,depthDone,ordinaryDone,requestDone,
    depthContext,cutContext,finalContext,rawDone,filtered,rawContext,rawGrowth,rawIssued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose true body environment before value after context actual
  have depthChecked := InternedFreshOrdinaryFacts.callback_verified body environment .depth before
    context.base.normal.facts (context.local .depth (InternedNestedProvenance.depth_available before)).base.inputs
  have depthGrowth : Grows before afterDepth := by
    simpa only [depthDone, Outcome.state] using depthChecked.growth
  have depthIssued : Extends before.nodes.issued afterDepth.nodes.issued := by
    simpa only [depthDone, Outcome.state] using depthChecked.history
  have localContext := depthContext.local (.uninterned (ordinaryLevel depth))
    (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth))
  have rawChecked := InternedFreshOrdinaryFacts.build_verified body _ afterDepth
    localContext.base.normal.facts localContext.base.inputs
  have rawAvailable := rawChecked.result raw middle rawDone
  have rawStepGrowth : Grows afterDepth middle := by
    simpa only [rawDone, Outcome.state] using rawChecked.growth
  have rawStepIssued : Extends afterDepth.nodes.issued middle.nodes.issued := by
    simpa only [rawDone, Outcome.state] using rawChecked.history
  have beforeRawGrowth := grows_trans depthGrowth rawStepGrowth
  have beforeRawIssued := extends_trans depthIssued rawStepIssued
  have beforeAfterGrowth := grows_trans beforeRawGrowth rawGrowth
  have beforeAfterIssued := extends_trans beforeRawIssued rawIssued
  obtain ⟨entry,storedBody,present,returned⟩ := SourceCurrentNativeRequestProbes.request_probes
    true depth ordinary _ cut value after requestDone finalContext.base.normal.facts depthAvailable ordinaryAvailable
  have correct := finalContext.depth (muKey depth ordinary) entry storedBody depth ordinary present
  obtain ⟨unused,sameBody,selfAbsent,bodyRow⟩ := SourceCurrentNativeOrdinaryMuFinish.selected
    entry storedBody depth ordinary correct value returned.symm rowIndex row selected
  have readerCell := growth.nodeRecords (muKey depth ordinary) _ present
  have erased : value = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary :=
    returned.trans (SourceCurrentNativeNormalizedComparisonExecution.history_unused reader history
      (muKey depth ordinary) entry storedBody depth ordinary readerCell unused)
  have origins : ∀ view edge, Origin view [value] edge ↔ Origin view [raw] edge := by
    intro view edge
    rw [erased,SourceCurrentNativeCallbackRowOrigins.erase_self]
    have filteredOrigins := SourceCurrentNativeCallbackRowOrigins.filter middle view
      (.uninterned (ordinaryLevel depth)) raw edge rawContext.base.normal rawAvailable
    simpa only [filtered] using filteredOrigins
  refine ⟨depth,afterDepth,ordinary,cut,raw,middle,entry,storedBody,
    depthDone,ordinaryDone,requestDone,rawDone,filtered,depthContext,cutContext,finalContext,rawContext,rawAvailable,
    depthGrowth,depthIssued,rawStepGrowth,rawStepIssued,rawGrowth,rawIssued,beforeRawGrowth,beforeRawIssued,
    beforeAfterGrowth,beforeAfterIssued,present,readerCell,returned,correct,unused,sameBody,selfAbsent,bodyRow,
    erased,origins,?_⟩
  intro view
  apply (origins view row).mp
  exact ⟨value,.seed (List.mem_singleton_self _),List.mem_of_getElem? selected⟩

end MicroCFTA.SourceCurrentNativeBinderReaderRows
