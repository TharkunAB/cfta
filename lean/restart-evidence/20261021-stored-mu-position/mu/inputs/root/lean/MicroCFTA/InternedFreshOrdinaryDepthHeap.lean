import MicroCFTA.InternedDeepLocalNormal
import MicroCFTA.InternedFreshOrdinaryFreeHeap
import MicroCFTA.InternedProfileCallbackForm

/-!
# Depth and deep-name observations decoded from repaired probes

The fresh ordinary argument detects a deep local occurrence. The two
probe components also recover each fixed deep capture. These fields
determine raw and smart readback depth and deep names. Establishing this
invariant through the full executor is a separate theorem.
-/
namespace MicroCFTA.InternedFreshOrdinaryDepthHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome finish)
open InternedDeepFreeDepth InternedDeepLocalNormal
open InternedFreshOrdinaryConstruction InternedFreeNameDecoder
open InternedRootProfile (response)
open InternedProfileCallbackForm (response_member)
open InternedBinderProtocol (Reference NodeKey)

/-- The ordinary probe records whether a local survives below a constructor boundary. -/
def usesLocal (depth ordinary : Value Symbol Guard) : Bool :=
  decide (.uninterned (ordinaryLevel depth) ∈ deepNames ordinary)

/-- Both binder forms use the exact depth of their normalized Depth probe. -/
def decodedDepth (smart : Bool) (depth ordinary : Value Symbol Guard) : Nat :=
  if !smart || usesLocal depth ordinary then depth.depth + 1 else depth.depth

/-- A retained Mu makes all captures deep; a removed binder retains only deep captures. -/
def decodedDeep (smart : Bool) (depth ordinary : Value Symbol Guard) : List Reference :=
  if !smart || usesLocal depth ordinary then
    decode .depth (.uninterned (ordinaryLevel depth)) depth.free ordinary.free
  else decode .depth (.uninterned (ordinaryLevel depth)) (deepNames depth) (deepNames ordinary)

/-- A stored pair determines both exact depth and deep-name membership for both binder forms. -/
def Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  ∀ smart, (finish smart (.mu entry body depth ordinary)).depth = decodedDepth smart depth ordinary ∧
    ∀ name, name ∈ deepNames (finish smart (.mu entry body depth ordinary)) ↔ name ∈ decodedDeep smart depth ordinary

/-- Every complete recursive record has its probe-decoded depth and deep names. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Correct entry body depth ordinary

/-- Empty caches have no recursive observation obligation. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Ordinary source effects preserve the invariant of complete recursive records. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before)
    (old : InternedShallowHeap.NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- A later decoded heap proves the same invariant for every retained earlier complete record. -/
theorem of_grows (before after : State Symbol Guard) (growth : Grows before after) (heap : Heap after) : Heap before := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (growth.nodeRecords key _ present)

/-- Completing a request installs its proved observation or retains an earlier record. -/
theorem complete_heap (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) (correct : Correct entry body depth ordinary) :
    Heap (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- Coherent canonical hit readback uses the exact pair supplied by the current request. -/
theorem hit_observation (smart : Bool) (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (heap : Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    (finish smart value).depth = decodedDepth smart depth ordinary ∧
      ∀ name, name ∈ deepNames (finish smart value) ↔ name ∈ decodedDeep smart depth ordinary := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  exact heap _ entry body depth ordinary present smart

/-- One pure body determines fixed deep captures and an optional supplied argument. -/
def Observed (captured : List Reference) (uses : Bool) (argument : Reference) (value : Value Symbol Guard) : Prop :=
  ∀ name, name ∈ deepNames value ↔ name ∈ response captured uses argument

/-- Other names in one deep observation are precisely fixed captures. -/
theorem observed_other (captured : List Reference) (uses : Bool) (argument : Reference) (value : Value Symbol Guard)
    (observed : Observed captured uses argument value) (name : Reference) (different : name ≠ argument) :
    name ∈ deepNames value ↔ name ∈ captured := by
  simpa only [response_member, different, and_false, or_false] using observed name

/-- At a fresh supplied name, deep membership detects the local contribution exactly. -/
theorem observed_own (captured : List Reference) (uses : Bool) (argument : Reference) (value : Value Symbol Guard)
    (observed : Observed captured uses argument value) (fresh : argument ∉ captured) :
    argument ∈ deepNames value ↔ uses = true := by
  simpa only [response_member, fresh, false_or, and_true] using observed argument

/-- Three actual observations with fresh probes establish the complete stored invariant. -/
theorem candidate (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state body)
    (localNormal : Local (.interned entry.identity) body) (bodyDepth : body.depth = depth.depth)
    (captured : List Reference) (uses : Bool)
    (depthObserved : Observed captured uses .depth depth)
    (ordinaryObserved : Observed captured uses (.uninterned (ordinaryLevel depth)) ordinary)
    (bodyObserved : Observed captured uses (.interned entry.identity) body)
    (ordinaryFresh : .uninterned (ordinaryLevel depth) ∉ captured)
    (bodyFresh : .interned entry.identity ∉ captured)
    (freeCorrect : InternedFreshOrdinaryFreeHeap.Correct entry body depth ordinary) : Correct entry body depth ordinary := by
  have bodyUses := observed_own captured uses _ body bodyObserved bodyFresh
  have ordinaryUses := observed_own captured uses _ ordinary ordinaryObserved ordinaryFresh
  have decoded := decode_observed captured (deepNames depth) (deepNames ordinary) .depth
    (.uninterned (ordinaryLevel depth)) (by intro impossible; cases impossible)
    (observed_other captured uses .depth depth depthObserved)
    (observed_other captured uses _ ordinary ordinaryObserved)
  intro smart
  constructor
  · rw [finish_depth smart entry body depth ordinary state coherent available localNormal, bodyDepth]
    cases uses <;> cases smart <;> simp_all [decodedDepth, usesLocal]
  · intro name
    rw [finish_deep smart entry body depth ordinary state coherent available localNormal name]
    cases smart with
    | false => simpa [decodedDeep] using freeCorrect name
    | true =>
        cases uses with
        | true => simpa [decodedDeep, usesLocal, bodyUses, ordinaryUses] using freeCorrect name
        | false =>
            have bodyCaptured : name ∈ deepNames body ↔ name ∈ captured := by
              simpa [response] using bodyObserved name
            simpa [decodedDeep, usesLocal, bodyUses, ordinaryUses] using bodyCaptured.trans (decoded name).symm

end MicroCFTA.InternedFreshOrdinaryDepthHeap
