import MicroCFTA.SourceCurrentConstrainedCapPairOccurrenceCallbacks
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Ranked occurrence readback from actual populated Mu cells

The semantic heap decodes a stored winner from its exact requested probes.
Marked probe bounds exclude a deep local at a positive owner bound.
The same hit retains the base free and deep bounds without a winner oracle.
Guard-cap transport is a separate obligation.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapWarmOccurrences
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedDeepFreeDepth
open InternedNestedConstruction (finish)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryDepthHeap (usesLocal decodedDepth decodedDeep)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapPairOccurrences
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
variable {Symbol Guard : Type}

/-- Removing a probe's own name exposes its unchanged base weight. -/
theorem mark_other (weight : Reference → Nat) (marker : Reference) (bound : Nat)
    (name : Reference) (different : name ≠ marker) : mark weight marker bound name = weight name := by
  simp only [mark, different, ite_false]

/-- Every name decoded from marked probes retains the inclusive base bound. -/
theorem decode_free (weight : Reference → Nat) (bound : Nat) (firstName secondName : Reference)
    (first second : Value Symbol Guard)
    (firstBound : FreeLE (mark weight firstName bound) bound first)
    (secondBound : FreeLE (mark weight secondName bound) bound second)
    (name : Reference)
    (member : name ∈ InternedFreeNameDecoder.decode firstName secondName first.free second.free) :
    weight name ≤ bound := by
  simp only [InternedFreeNameDecoder.decode, List.mem_append, List.mem_filter, bne_iff_ne] at member
  rcases member with ⟨named, different⟩ | ⟨named, different⟩
  · simpa only [mark_other weight firstName bound name different] using firstBound name named
  · simpa only [mark_other weight secondName bound name different] using secondBound name named

/-- Decoded deep captures retain the strict base bound of each marked probe. -/
theorem decode_deep (weight : Reference → Nat) (bound : Nat) (firstName secondName : Reference)
    (first second : Value Symbol Guard)
    (firstBound : Classified (mark weight firstName bound) bound first)
    (secondBound : Classified (mark weight secondName bound) bound second)
    (name : Reference)
    (member : name ∈ InternedFreeNameDecoder.decode firstName secondName (deepNames first) (deepNames second)) :
    weight name < bound ∨ bound = 0 := by
  simp only [InternedFreeNameDecoder.decode, List.mem_append, List.mem_filter, bne_iff_ne] at member
  rcases member with ⟨named, different⟩ | ⟨named, different⟩
  · simpa only [mark_other weight firstName bound name different] using firstBound.deep name named
  · simpa only [mark_other weight secondName bound name different] using secondBound.deep name named

/-- A maximal marked ordinary probe cannot report a deep local occurrence. -/
theorem ordinary_unused (weight : Reference → Nat) (bound : Nat) (depth ordinary : Value Symbol Guard)
    (positive : 0 < bound)
    (classified : Classified (mark weight (.uninterned (ordinaryLevel depth)) bound) bound ordinary) :
    usesLocal depth ordinary = false := by
  have absent := classified.not_deep positive (.uninterned (ordinaryLevel depth)) (by simp [mark])
  simp only [usesLocal, absent, decide_false]

/-- The actual stored body or empty is returned when its ordinary probe has no deep local. -/
theorem no_wrapper (state : State Symbol Guard) (heap : InternedFreshOrdinaryDepthHeap.Heap state)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : state.nodeRecords key = some (.mu entry body depth ordinary))
    (unused : usesLocal depth ordinary = false) :
    finish true (.mu entry body depth ordinary) = body ∨
      finish true (.mu entry body depth ordinary) = .empty := by
  have decoded := heap key entry body depth ordinary present
  have raw := (decoded false).1
  have smart := (decoded true).1
  have sameDepth : body.depth = depth.depth := by
    simp only [finish, Bool.false_eq_true, ↓reduceIte, Value.depth, decodedDepth, Bool.not_false,
      Bool.true_or] at raw
    omega
  have resultDepth : (finish true (.mu entry body depth ordinary)).depth = depth.depth := by
    simpa only [decodedDepth, Bool.not_true, unused, Bool.false_or, Bool.false_eq_true, ↓reduceIte] using smart
  by_cases absent : .interned entry.identity ∉ body.free
  · exact .inl (by simp [finish, cleanup, absent])
  · by_cases self : body.referenceOf = .ref (.interned entry.identity)
    · exact .inr (by simp [finish, cleanup, absent, self])
    · have retained : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
        simp [finish, cleanup, absent, self]
      rw [retained, Value.depth, sameDepth] at resultDepth
      omega

/-- Exact marked probes derive the classification of any actual warm winner. -/
theorem hit_classified (weight : Reference → Nat) (bound : Nat)
    (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (present : state.nodeRecords (muKey depth ordinary) = some value)
    (positive : 0 < bound)
    (depthBound : Classified (mark weight .depth bound) bound depth)
    (ordinaryBound : Classified (mark weight (.uninterned (ordinaryLevel depth)) bound) bound ordinary) :
    Classified weight bound (finish true value) := by
  have facts := semantic.1.normal.facts
  have unused := ordinary_unused weight bound depth ordinary positive ordinaryBound
  constructor
  · intro name member
    have decoded := (InternedFreshOrdinaryFreeHeap.hit_free true depth ordinary value state facts
      depthAvailable ordinaryAvailable semantic.1.freeNames present name).mp member
    exact decode_free weight bound _ _ depth ordinary depthBound.free ordinaryBound.free name decoded
  · intro name member
    have decoded := ((InternedFreshOrdinaryDepthHeap.hit_observation true depth ordinary value state facts
      depthAvailable ordinaryAvailable semantic.2 present).2 name).mp member
    simp only [decodedDeep, Bool.not_true, unused, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at decoded
    exact decode_deep weight bound _ _ depth ordinary depthBound ordinaryBound name decoded

/-- A maximal marked ordinary probe excludes a retained wrapper at the exact warm key. -/
theorem hit_cleanup (weight : Reference → Nat) (bound : Nat)
    (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (present : state.nodeRecords (muKey depth ordinary) = some value)
    (positive : 0 < bound)
    (ordinaryBound : Classified (mark weight (.uninterned (ordinaryLevel depth)) bound) bound ordinary) :
    ∃ entry body, value = .mu entry body depth ordinary ∧
      (finish true value = body ∨ finish true value = .empty) := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state
    semantic.1.normal.facts depthAvailable ordinaryAvailable present
  exact ⟨entry, body, rfl, no_wrapper state semantic.2 _ entry body depth ordinary present
    (ordinary_unused weight bound depth ordinary positive ordinaryBound)⟩

/-- An actual populated request completes with the derived classifier and the same heap. -/
theorem request_hit (weight : Reference → Nat) (bound : Nat)
    (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (next : Reference → State Symbol Guard → InternedNestedConstruction.Outcome Symbol Guard (Value Symbol Guard))
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (present : state.nodeRecords (muKey depth ordinary) = some value)
    (positive : 0 < bound)
    (depthBound : Classified (mark weight .depth bound) bound depth)
    (ordinaryBound : Classified (mark weight (.uninterned (ordinaryLevel depth)) bound) bound ordinary) :
    InternedNestedConstruction.request true depth ordinary next state = .done (finish true value) state ∧
      Classified weight bound (finish true value) := by
  obtain ⟨entry, installed, _⟩ := semantic.1.normal.facts.coherent.nodes _ _ present
  exact ⟨by simp only [InternedNestedConstruction.request, installed, present],
    hit_classified weight bound depth ordinary value state semantic depthAvailable ordinaryAvailable present positive
      depthBound ordinaryBound⟩

end MicroCFTA.SourceCurrentConstrainedCapWarmOccurrences
