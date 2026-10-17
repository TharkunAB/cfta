import MicroCFTA.SourceCurrentConstrainedCapNativeCallbacks

/-!
# Native callback certificates during an outer reservation

The local certificate permits an unfinished outer Mu key. It derives cap
and occurrence laws for each actual return and retains causal stores at
every stopping state. A finite enclosing producer must supply its own trace.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCallbackCertificates
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Outcome work finish)
open InternedBinderProtocol (Reference NodeKey)
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPairOccurrences (Classified)
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
open SourceCurrentHereditaryConstruction (MuStored Checked)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
variable {Symbol Guard : Type}

/-- Actual callbacks retain complete physical facts without complete-cache coverage. -/
theorem verified [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard) (old marker : Reference)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state body)
    (markerAvailable : Available state (.reference marker)) :
    Verified state (SourceRecursiveIntersectionMaybeMu.callback old body marker state) Available := by
  rw [SourceRecursiveIntersectionMaybeMu.callback_eq old body marker state state facts available]
  apply InternedFreshOrdinaryFacts.callback_verified _ _ marker state facts
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact markerAvailable
  · exact leaves_available body state available value member

/-- The actual stopping callback heap retains all semantic observations during an outer reservation. -/
theorem semantic [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard) (old marker : Reference)
    (state : State Symbol Guard) (heap : SemanticHeap state) (available : Available state body)
    (markerAvailable : Available state (.reference marker)) :
    SemanticHeap (SourceRecursiveIntersectionMaybeMu.callback old body marker state).state := by
  rw [SourceRecursiveIntersectionMaybeMu.callback_eq old body marker state state heap.1.normal.facts available]
  let expression := encode (leaves body) [old] body
  have context := SourceRecursiveIntersectionSemanticHeap.context state heap (leaves body) (leaves_available body state available)
  have after := context.callback expression marker markerAvailable
  have depth := (InternedRecordDepthExecution.callback_depth expression (leaves body) marker state context markerAvailable heap.2).heap
  exact ⟨⟨after.normal, (by intro value member; cases member), after.profiles, after.freeNames⟩, depth⟩

/-- Initial body laws certify every actual callback return without assuming callback completion. -/
theorem checked [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (body : Value Symbol Guard) (old marker : Reference) (state : State Symbol Guard)
    (heap : SemanticHeap state) (available : Available state body) (markerAvailable : Available state (.reference marker))
    (bounded : Cap annotation depth body) (stored : MuStored annotation state)
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (fresh : marker ∉ body.free) :
    Checked annotation (SourceRecursiveIntersectionMaybeMu.callback old body marker state)
      (fun value => Cap annotation depth value ∧ Classified (mark weight marker bound) bound value ∧
        InternedDeepLocalNormal.Local marker value) := by
  have replacements : Replacements state (replacement old (.reference marker)) := by
    intro name value found
    unfold replacement at found
    split at found
    · cases found
      exact markerAvailable
    · cases found
  have annotations : ∀ (name : Reference) (value : Value Symbol Guard), replacement old (.reference marker) name = some value →
      SourceEqualityAnnotationLanguage.Annotated annotation value := by
    intro name value found
    unfold replacement at found
    split at found
    · cases found
      exact .reference marker
    · cases found
  have rawChecked := SourceCurrentConstrainedCapStoredSubstitution.execute annotation depth body
    (replacement old (.reference marker)) state heap.1.normal.facts available bounded replacements annotations stored
  have inputs := inputs_available body (replacement old (.reference marker)) state available replacements
  have physical := InternedFreshOrdinaryFacts.build_verified (encode (leaves body) [] body) _ state heap.1.normal.facts inputs
  have normal := InternedFreshOrdinaryNormal.build_normal (encode (leaves body) [] body) _ state heap.1.normal inputs
  unfold SourceRecursiveIntersectionMaybeMu.callback
  cases actual : InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) state with
  | pending key after =>
      exact ⟨by simpa only [actual, Outcome.bind, Outcome.state] using rawChecked.stored,
        by intro _ _ impossible; cases impossible⟩
  | done raw middle =>
      have middleNormal : InternedStoredMuOrigins.Normal middle := by
        change InternedStoredMuOrigins.Normal
          (InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) state).state at normal
        simpa only [actual, Outcome.state] using normal
      have rawAvailable := physical.result raw middle actual
      have rawCap := rawChecked.result raw middle actual
      have rawClassified := SourceCurrentConstrainedCapMarkerTransport.transport body state heap.1 heap.2 available
        old marker markerAvailable weight bound oldWeight classified fresh raw middle actual
      have middleStored : MuStored annotation middle := by simpa only [actual, Outcome.state] using rawChecked.stored
      simp only [Outcome.bind]
      refine ⟨middleStored.preserve (InternedStoredMuOrigins.filter_noNewMu marker raw middle), ?_⟩
      intro value after done
      obtain ⟨rfl, rfl⟩ := Outcome.done.inj done
      exact ⟨SourceCurrentConstrainedCapPairOccurrences.filter_cap annotation depth marker raw middle middleNormal rawAvailable rawCap,
        SourceCurrentConstrainedCapPairOccurrences.filter (mark weight marker bound) bound marker raw middle middleNormal
          rawAvailable rawClassified,
        InternedDeepLocalNormal.filter_local marker raw middle middleNormal rawAvailable⟩

/-- An actual body receipt derives candidate cleanup and retains the same outer pending coverage. -/
theorem candidate_of_actual [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (body : Value Symbol Guard) (old : Reference) (entry : Interned NodeKey) (state : State Symbol Guard)
    (heap : SemanticHeap state) (available : Available state body)
    (markerAvailable : Available state (.reference (.interned entry.identity)))
    (bounded : Cap annotation depth body) (stored : MuStored annotation state)
    (weight : Reference → Nat) (bound : Nat) (positive : 0 < bound) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (fresh : .interned entry.identity ∉ body.free)
    (pending : List NodeKey) (covered : Covered pending state)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.callback old body (.interned entry.identity) state = .done value after)
    (probe ordinary : Value Symbol Guard) :
    Cap annotation depth (finish true (.mu entry value probe ordinary)) ∧
      Classified weight bound (finish true (.mu entry value probe ordinary)) ∧
      MuStored annotation after ∧ SemanticHeap after ∧ Covered pending after ∧
      Available after value ∧ Facts after ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued := by
  have localChecked := checked annotation depth body old (.interned entry.identity) state heap available markerAvailable
    bounded stored weight bound oldWeight classified fresh
  have physical := verified body old (.interned entry.identity) state heap.1.normal.facts available markerAvailable
  have retained := semantic body old (.interned entry.identity) state heap available markerAvailable
  have localResult := localChecked.result value after actual
  have candidate := SourceCurrentConstrainedCapNativeCallbacks.finish_local annotation depth weight bound entry value probe ordinary
    positive localResult.1 localResult.2.1 localResult.2.2
  refine ⟨candidate.2.1, candidate.2.2, ?_, ?_, ?_, physical.result value after actual, ?_, ?_, ?_⟩
  · simpa only [actual, Outcome.state] using localChecked.stored
  · simpa only [actual, Outcome.state] using retained
  · exact SourceRecursiveIntersectionMaybeMu.callback_covered old body (.interned entry.identity) state
      heap.1.normal.facts.coherent.valid covered value after actual
  · simpa only [actual, Outcome.state] using physical.facts
  · simpa only [actual, Outcome.state] using physical.growth
  · simpa only [actual, Outcome.state] using physical.history

end MicroCFTA.SourceCurrentConstrainedCapCallbackCertificates
