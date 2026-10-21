import MicroCFTA.InternedSyntaxProbeDecoder
import MicroCFTA.InternedStoredMuOrigins

/-!
# Decoded profiles for complete recursive cache records

The invariant relates each actual smart cleanup result to its canonical
probe pair. Ordinary effects preserve the relation. A complete cache hit
uses the exact stored probes, as derived from resident record identity.
The source executor must establish this invariant for new records.
-/
namespace MicroCFTA.InternedProfileHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedRequestFacts InternedFreshProbeKeys InternedShallowHeap
open InternedRootProfile InternedProbeDecoder InternedProfileEquivalence
open InternedBinderProtocol (Reference NodeKey)

/-- The actual smart cleanup profile agrees with the two canonical source probes. -/
def Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  Equivalent (profile (finish true (.mu entry body depth ordinary)))
    (decode .depth (.uninterned depth.depth) (profile depth) (profile ordinary))

/-- Every complete stored recursive record has the decoded smart result profile. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Correct entry body depth ordinary

/-- The empty source state has no complete recursive payloads. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Source effects that do not add recursive records preserve all decoded profiles. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before) (old : NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- A completed source miss installs its verified candidate or retains an earlier verified record. -/
theorem complete_heap (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) (correct : Correct entry body depth ordinary) :
    Heap (complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- Source sequencing keeps the profile invariant at both complete and pending outcomes. -/
theorem bind_heap (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (heap : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- A Mu-key payload contains the exact complete probe records requested by the caller. -/
theorem stored_probes (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    ∃ entry body, value = .mu entry body depth ordinary := by
  obtain ⟨stored, installed, fields⟩ := facts.coherent.nodes (muKey depth ordinary) value present
  cases value with
  | empty | reference | node | union => simp [NodeFields, muKey] at fields
  | mu entry body actualDepth actualOrdinary =>
      have keySame : muKey depth ordinary = muKey actualDepth actualOrdinary := fields.2
      have references : depth.referenceOf = actualDepth.referenceOf ∧ ordinary.referenceOf = actualOrdinary.referenceOf := by
        simpa only [muKey, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq] using keySame
      have available := facts.cached.nodes _ _ present
      have first := available.children actualDepth (by simp [children])
      have second := available.children actualOrdinary (by simp [children])
      have depthSame := resident_reference_injective state facts.coherent depth actualDepth depthAvailable.resident first.resident references.1
      have ordinarySame := resident_reference_injective state facts.coherent ordinary actualOrdinary ordinaryAvailable.resident second.resident references.2
      exact ⟨entry, body, by simp [depthSame, ordinarySame]⟩

/-- A complete canonical hit obtains its smart profile from the established heap invariant. -/
theorem hit_profile (smart : Bool) (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (heap : Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    Equivalent (profile (finish smart value))
      (if smart then decode .depth (.uninterned depth.depth) (profile depth) (profile ordinary) else none) := by
  obtain ⟨entry, body, rfl⟩ := stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  cases smart with
  | false => simp [finish, profile, Equivalent]
  | true => exact heap _ entry body depth ordinary present

end MicroCFTA.InternedProfileHeap
