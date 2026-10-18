import MicroCFTA.SourceCurrentNativeConstructReadback
import MicroCFTA.SourceCurrentNativeOrdinaryMuFinish

/-!
# Actual ordinary Mu return at a later causal reader

The completed construct supplies its own semantic callback contexts.
The selected record grows forward into the reader's publication history.
The proof does not infer an earlier history from that later history.
-/
namespace MicroCFTA.SourceCurrentNativeConstructReaderReadback
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome request finish)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedStoredSubstitution (leaves encode)
open InternedStoredSubstitutionRebind (replacement)
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open MergedFreshOrdinaryGraph (Origin)

/-- An ordinary selected return retains its actual callback schedule and full raw row origins. -/
def RowReadback [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (before : State Symbol Guard) (value : Value Symbol Guard) (after reader : State Symbol Guard)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ depth afterDepth ordinary cut raw middle entry storedBody,
    SourceRecursiveIntersectionMaybeMu.callback old body .depth before = .done depth afterDepth ∧
    SourceRecursiveIntersectionMaybeMu.callback old body (.uninterned (ordinaryLevel depth)) afterDepth =
      .done ordinary cut ∧
    request true depth ordinary (SourceRecursiveIntersectionMaybeMu.callback old body) cut = .done value after ∧
    InternedFreshOrdinaryStoredSubstitution.execute body
      (replacement old (.reference (.uninterned (ordinaryLevel depth)))) afterDepth = .done raw middle ∧
    run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) middle = (ordinary,cut) ∧
    InternedStoredMuOrigins.Normal middle ∧ Available middle raw ∧
    Grows middle after ∧ Extends middle.nodes.issued after.nodes.issued ∧
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

/-- A later actual history proves readback for the current completed construct and selected row. -/
theorem construct_row [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (available : Available before body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.construct old body before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader)
    (rowIndex : Nat) (row : EdgeValue Symbol Guard) (selected : (nodeEdges value)[rowIndex]? = some row) :
    RowReadback old body before value after reader rowIndex row := by
  have context : SourceCurrentConstrainedCapSourceHistory.Context before (leaves body) :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic (leaves body)
      (InternedStoredSubstitution.leaves_available body before available),semantic.2⟩
  have lexical := actual
  rw [SourceRecursiveIntersectionMaybeMu.construct_eq old body before before semantic.1.normal.facts available] at lexical
  obtain ⟨depth,afterDepth,ordinary,cut,raw,middle,depthDone,ordinaryDone,requestDone,
    depthContext,_cutContext,finalContext,rawDone,filtered,rawContext,rawGrowth,rawIssued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose true (encode (leaves body) [old] body) (leaves body)
      before value after context lexical
  have callbacks : SourceRecursiveIntersectionMaybeMu.callback old body =
      InternedFreshOrdinaryFacts.callback (encode (leaves body) [old] body) (leaves body) := by
    funext name state
    exact SourceRecursiveIntersectionMaybeMu.callback_eq old body name before state semantic.1.normal.facts available
  have localContext := depthContext.local (.uninterned (ordinaryLevel depth))
    (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth))
  have rawAvailable := (InternedFreshOrdinaryFacts.build_verified (encode (leaves body) [old] body) _
    afterDepth localContext.base.normal.facts localContext.base.inputs).result raw middle rawDone
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
    ?_,?_,?_,?_,filtered,rawContext.base.normal,rawAvailable,rawGrowth,rawIssued,present,readerCell,
    returned,correct,unused,sameBody,selfAbsent,bodyRow,erased,origins,?_⟩
  · simpa only [callbacks] using depthDone
  · simpa only [callbacks] using ordinaryDone
  · simpa only [callbacks] using requestDone
  · rw [← InternedStoredSubstitutionRebind.rebind_build body old _ before afterDepth
      semantic.1.normal.facts.coherent available]
    exact rawDone
  · intro view
    apply (origins view row).mp
    exact ⟨value,.seed (List.mem_singleton_self _),List.mem_of_getElem? selected⟩

end MicroCFTA.SourceCurrentNativeConstructReaderReadback
