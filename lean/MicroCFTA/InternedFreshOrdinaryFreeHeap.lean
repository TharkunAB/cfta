import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedFreeNameDecoder
import MicroCFTA.InternedProfileHeap

/-!
# Decoded free names for repaired recursive cache records

A complete Mu records the free names recovered from its two normalized
source probes. Ordinary effects retain this property. New recursive
records need the local three-call proof before completion.
-/
namespace MicroCFTA.InternedFreshOrdinaryFreeHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedFreshOrdinaryConstruction
open InternedFreeNameDecoder
open InternedBinderProtocol (Reference NodeKey)

/-- The actual complete Mu free field agrees with its canonical probe pair. -/
def Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  ∀ name, name ∈ (Value.mu entry body depth ordinary).free ↔
    name ∈ decode .depth (.uninterned (ordinaryLevel depth)) depth.free ordinary.free

/-- Every complete recursive payload has its source-decoded free-name set. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Correct entry body depth ordinary

/-- The empty source state contains no recursive payloads. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Effects that add no recursive payload preserve the decoded free-name field. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before) (old : NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- Completing a miss installs its proved candidate or retains an earlier proved record. -/
theorem complete_heap (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) (correct : Correct entry body depth ordinary) :
    Heap (complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- Sequential source execution keeps the invariant at complete and pending outcomes. -/
theorem bind_heap (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (heap : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- A canonical cache hit reads the free-name set of the actual requested probes. -/
theorem hit_free (smart : Bool) (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (heap : Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) (name : Reference) :
    name ∈ (finish smart value).free ↔ name ∈ decode .depth (.uninterned (ordinaryLevel depth)) depth.free ordinary.free := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  rw [finish_free]
  exact heap _ entry body depth ordinary present name

end MicroCFTA.InternedFreshOrdinaryFreeHeap
