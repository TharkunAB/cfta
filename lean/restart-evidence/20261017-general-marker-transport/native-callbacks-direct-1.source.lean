import MicroCFTA.SourceCurrentConstrainedCapStoredSubstitution
import MicroCFTA.SourceCurrentConstrainedCapMarkerTransport
import MicroCFTA.SourceCurrentConstrainedCapWarmOccurrences

/-!
# General finite native callbacks with marked occurrences

Initial source cap and occurrence laws produce the actual normalized return.
The same return retains the ready cache, causal Mu store, and both histories.
Smart cleanup removes a maximal fresh local. Existing outer Mu winners need
a separate guard-cap readback law.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeCallbacks
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Outcome work finish)
open InternedBinderProtocol (Reference NodeKey)
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPairOccurrences (Classified)
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceEqualityRequiredCache (Ready Keeps)
variable {Symbol Guard : Type}

/-- Actual root filtering retains complete cache readiness and both histories. -/
theorem filter_keeps [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state value) :
    Keeps state (run (withoutSelfReference name value) state).2 := by
  have facts := ready.semantic.1.normal.facts
  have checked := filter_verified name value state facts available
  have old := InternedStoredMuOrigins.filter_noNewMu name value state
  have normal := InternedFreshOrdinaryNormal.filter_normal name value state ready.semantic.1.normal available
  exact ⟨⟨SourceRecursiveIntersectionSemanticHeap.preserve state _ ready.semantic normal old,
    InternedNestedCoverage.run_covered _ state facts.coherent.valid ready.covered,
    InternedOpenDepthReadback.preserve state _ ready.depth old⟩, checked.growth, checked.history⟩

/-- Initial body laws construct the same finite normalized native callback and all returned certificates. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (body : Value Symbol Guard) (old marker : Reference) (state : State Symbol Guard)
    (ready : Ready state) (available : Available state body) (markerAvailable : Available state (.reference marker))
    (bounded : Cap annotation depth body) (stored : MuStored annotation state)
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (fresh : marker ∉ body.free) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.callback old body marker state = .done value after ∧
      Cap annotation depth value ∧ Classified (mark weight marker bound) bound value ∧
      MuStored annotation after ∧ Available after value ∧ Keeps state after ∧
      InternedDeepLocalNormal.Local marker value := by
  have replacements : Replacements state (replacement old (.reference marker)) := by
    intro name value found
    unfold replacement at found
    split at found
    · cases found
      exact markerAvailable
    · cases found
  have annotations : ∀ name value, replacement old (.reference marker) name = some value →
      SourceEqualityAnnotationLanguage.Annotated annotation value := by
    intro name value found
    unfold replacement at found
    split at found
    · cases found
      exact .reference marker
    · cases found
  obtain ⟨raw, middle, rawDone, rawCap, middleStored, rawAvailable, middleReady, growth, history⟩ :=
    SourceCurrentConstrainedCapStoredSubstitution.complete annotation depth body (replacement old (.reference marker))
      state ready available bounded replacements annotations stored
  have rawClassified := SourceCurrentConstrainedCapMarkerTransport.transport body state ready.semantic.1 ready.semantic.2
    available old marker markerAvailable weight bound oldWeight classified fresh raw middle rawDone
  have normal := middleReady.semantic.1.normal
  have checked := filter_verified marker raw middle normal.facts rawAvailable
  let result := run (withoutSelfReference marker raw) middle
  have filterKeeps := filter_keeps marker raw middle middleReady rawAvailable
  have actual : SourceRecursiveIntersectionMaybeMu.callback old body marker state = .done result.1 result.2 := by
    simp only [SourceRecursiveIntersectionMaybeMu.callback, rawDone, Outcome.bind, work, result]
  refine ⟨result.1, result.2, actual, ?_, ?_, ?_, checked.result _ _ rfl,
    (Keeps.trans ⟨middleReady, growth, history⟩ filterKeeps), ?_⟩
  · exact SourceCurrentConstrainedCapPairOccurrences.filter_cap annotation depth marker raw middle normal rawAvailable rawCap
  · exact SourceCurrentConstrainedCapPairOccurrences.filter (mark weight marker bound) bound marker raw middle normal
      rawAvailable rawClassified
  · exact middleStored.preserve (InternedStoredMuOrigins.filter_noNewMu marker raw middle)
  · exact InternedDeepLocalNormal.filter_local marker raw middle normal rawAvailable

/-- The maximal marked local is removed by actual smart candidate cleanup. -/
theorem finish_local (annotation : Guard → Prop) (depth : Nat) (weight : Reference → Nat) (bound : Nat)
    (entry : Interned NodeKey) (body probe ordinary : Value Symbol Guard)
    (positive : 0 < bound) (bounded : Cap annotation depth body)
    (classified : Classified (mark weight (.interned entry.identity) bound) bound body)
    (localNormal : InternedDeepLocalNormal.Local (.interned entry.identity) body) :
    let value := finish true (.mu entry body probe ordinary)
    (value = body ∨ value = .empty) ∧ Cap annotation depth value ∧ Classified weight bound value := by
  dsimp only
  have notDeep := classified.not_deep positive (.interned entry.identity) (by simp [mark])
  by_cases absent : .interned entry.identity ∉ body.free
  · have same : finish true (.mu entry body probe ordinary) = body := by simp [finish, cleanup, absent]
    rw [same]
    refine ⟨.inl rfl, bounded, ?_⟩
    constructor
    · intro name member
      have different : name ≠ .interned entry.identity := by intro equal; exact absent (equal ▸ member)
      simpa only [SourceCurrentConstrainedCapWarmOccurrences.mark_other weight _ bound name different] using
        classified.free name member
    · intro name member
      have different : name ≠ .interned entry.identity := by intro equal; exact notDeep (equal ▸ member)
      simpa only [SourceCurrentConstrainedCapWarmOccurrences.mark_other weight _ bound name different] using
        classified.deep name member
  · rcases localNormal (Classical.not_not.mp absent) with impossible | bare
    · exact False.elim (notDeep impossible)
    · subst body
      have same : finish true (.mu entry (.reference (.interned entry.identity)) probe ordinary) = .empty := by
        simp [finish, cleanup, Value.free, Value.referenceOf]
      rw [same]
      exact ⟨.inr rfl, .plain depth .empty, SourceCurrentConstrainedCapPairOccurrences.empty weight bound⟩

/-- General source callbacks produce a capped classified candidate from initial data alone. -/
theorem candidate_complete [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (body : Value Symbol Guard) (old : Reference) (entry : Interned NodeKey) (state : State Symbol Guard)
    (ready : Ready state) (available : Available state body)
    (markerAvailable : Available state (.reference (.interned entry.identity)))
    (bounded : Cap annotation depth body) (stored : MuStored annotation state)
    (weight : Reference → Nat) (bound : Nat) (positive : 0 < bound) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (fresh : .interned entry.identity ∉ body.free)
    (probe ordinary : Value Symbol Guard) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.callback old body (.interned entry.identity) state = .done value after ∧
      Cap annotation depth (finish true (.mu entry value probe ordinary)) ∧
      Classified weight bound (finish true (.mu entry value probe ordinary)) ∧
      (finish true (.mu entry value probe ordinary) = value ∨ finish true (.mu entry value probe ordinary) = .empty) ∧
      MuStored annotation after ∧ Available after value ∧ Keeps state after := by
  obtain ⟨value, after, actual, capped, marked, kept, output, effects, localNormal⟩ :=
    complete annotation depth body old (.interned entry.identity) state ready available markerAvailable bounded stored
      weight bound oldWeight classified fresh
  have result := finish_local annotation depth weight bound entry value probe ordinary positive capped marked localNormal
  exact ⟨value, after, actual, result.2.1, result.2.2, result.1, kept, output, effects⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeCallbacks
