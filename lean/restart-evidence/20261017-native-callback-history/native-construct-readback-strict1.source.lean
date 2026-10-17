import MicroCFTA.SourceCurrentNativeMuHistory
import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
import MicroCFTA.SourceCurrentNativeCallbackRowOrigins
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives

/-!
# Actual native optional-binder readback

The actual call retains both probes and the raw ordinary substitution.
An unused local binder returns that call's erased ordinary result, even
when the physical request selects an earlier stored winner. Root cleanup
preserves the complete rows of the current raw ordinary substitution.
-/
namespace MicroCFTA.SourceCurrentNativeConstructReadback
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome request finish)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedStoredSubstitution (leaves encode)
open InternedStoredSubstitutionRebind (replacement)
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open MergedFreshOrdinaryGraph (Origin)

/-- A native return retains its current callbacks, physical winner, and unused-row identity. -/
def Readback [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (before : State Symbol Guard) (value : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∃ depth afterDepth ordinary cut raw middle entry storedBody,
    SourceRecursiveIntersectionMaybeMu.callback old body .depth before = .done depth afterDepth ∧
    SourceRecursiveIntersectionMaybeMu.callback old body (.uninterned (ordinaryLevel depth)) afterDepth =
      .done ordinary cut ∧
    request true depth ordinary (SourceRecursiveIntersectionMaybeMu.callback old body) cut = .done value after ∧
    InternedFreshOrdinaryStoredSubstitution.execute body
      (replacement old (.reference (.uninterned (ordinaryLevel depth)))) afterDepth = .done raw middle ∧
    run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) middle = (ordinary, cut) ∧
    InternedFreshOrdinaryNormal.Normal middle ∧ Available middle raw ∧
    after.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
    value = finish true (.mu entry storedBody depth ordinary) ∧
    Nonempty (History empty after) ∧
    (InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false →
      value = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary ∧
      ∀ view row, Origin view [value] row ↔ Origin view [raw] row)

/-- Actual native construction derives readback from its earlier causal publication history. -/
theorem construct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (available : Available before body)
    (history : History empty before) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.construct old body before = .done value after) :
    Readback old body before value after := by
  have context : SourceCurrentConstrainedCapSourceHistory.Context before (leaves body) :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic (leaves body)
      (InternedStoredSubstitution.leaves_available body before available), semantic.2⟩
  have lexical := actual
  rw [SourceRecursiveIntersectionMaybeMu.construct_eq old body before before semantic.1.normal.facts available] at lexical
  obtain ⟨depth, afterDepth, ordinary, cut, raw, middle, depthDone, ordinaryDone, requestDone,
    depthContext, _, finalContext, rawDone, filtered, rawContext, _, _, depthAvailable, ordinaryAvailable⟩ :=
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
  obtain ⟨entry, storedBody, present, returned⟩ := SourceCurrentNativeRequestProbes.request_probes
    true depth ordinary _ cut value after requestDone finalContext.base.normal.facts depthAvailable ordinaryAvailable
  obtain ⟨later⟩ := SourceCurrentNativeMuHistory.construct old body before semantic available
  have whole : History empty after := by
    have segment : History before after := by simpa only [actual, Outcome.state] using later
    exact History.trans history segment
  refine ⟨depth, afterDepth, ordinary, cut, raw, middle, entry, storedBody,
    ?_, ?_, ?_, ?_, filtered, rawContext.base.normal, rawAvailable, present, returned, ⟨whole⟩, ?_⟩
  · simpa only [callbacks] using depthDone
  · simpa only [callbacks] using ordinaryDone
  · simpa only [callbacks] using requestDone
  · rw [← InternedStoredSubstitutionRebind.rebind_build body old _ before afterDepth
      semantic.1.normal.facts.coherent available]
    exact rawDone
  · intro unused
    have erased : value = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary :=
      returned.trans (SourceCurrentNativeNormalizedComparisonExecution.history_unused after whole
        (muKey depth ordinary) entry storedBody depth ordinary present unused)
    refine ⟨erased, ?_⟩
    intro view row
    rw [erased, SourceCurrentNativeCallbackRowOrigins.erase_self]
    have origins := SourceCurrentNativeCallbackRowOrigins.filter middle view
      (.uninterned (ordinaryLevel depth)) raw row rawContext.base.normal rawAvailable
    simpa only [filtered] using origins

/-- Initial ready inputs construct the actual optional return and its causal readback. -/
theorem optional_complete [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat)
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before) (available : Available before body)
    (history : History empty before) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body before = .done value after ∧
      SourceEqualityRequiredCache.Keeps before after ∧ Available after value ∧
      Nonempty (History empty after) ∧
      ((.intersection pair.1 pair.2 ∉ body.free ∧ value = body ∧ after = before) ∨
        (.intersection pair.1 pair.2 ∈ body.free ∧ Readback (.intersection pair.1 pair.2) body before value after)) := by
  obtain ⟨value, after, actual, keeps, result⟩ :=
    SourceEqualityNativeDemandHeapPrimitives.optionalBinder_complete pair body before ready available
  obtain ⟨later⟩ := SourceCurrentNativeMuHistory.maybeMu pair body before ready.semantic available
  have whole : History empty after := by
    have segment : History before after := by simpa only [actual, Outcome.state] using later
    exact History.trans history segment
  refine ⟨value, after, actual, keeps, result, ⟨whole⟩, ?_⟩
  by_cases used : .intersection pair.1 pair.2 ∈ body.free
  · right
    refine ⟨used, construct _ body before ready.semantic available history value after ?_⟩
    simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu, used, ite_true] using actual
  · left
    have equal : Outcome.done body before = (Outcome.done value after : Outcome Symbol Guard (Value Symbol Guard)) := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu, used, ite_false] using actual
    exact ⟨used, (Outcome.done.inj equal).1.symm, (Outcome.done.inj equal).2.symm⟩

end MicroCFTA.SourceCurrentNativeConstructReadback
