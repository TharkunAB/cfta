import MicroCFTA.SourceSynthesisUniverseBodyReferenceControl
import MicroCFTA.SourceSynthesisUniverseMarkerCompletion

/-!
# Actual marker/reference cross-child completion

The second domain comes from the preceding body/reference execution.
Its original Mu binding and cutoff set derive lookup and pair freshness.
The proof then composes actual lookup, closed-domain reset, and the checked
five-level marker/Mu request. Returned values are closed, but this file
does not identify them with the marker or classify the original catalog.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerReference
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedFreshProbeKeys
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionDomain SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (first first_valid second second_seen secondState)

variable {Symbol Guard : Type}

private abbrev bodyValue (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) : Value Symbol Guard :=
  .node b rows 0 [.interned u.identity]

private abbrev muValue (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) : Value Symbol Guard :=
  .mu u (bodyValue u b rows) depth ordinary

private abbrev markerValue (m : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth : Nat) : Value Symbol Guard := .node m rows depth []

private abbrev refValue (u : Interned NodeKey) : Value Symbol Guard :=
  .reference (Reference.interned u.identity)

/-- Both actual domain allocations preserve the domain-cache invariant. -/
theorem second_valid (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains) :
    Cache.Valid (second u b rows depth ordinary state).2 :=
  (IntersectionEmptyDomain.make_correct (first u b rows depth ordinary state).2
    (first_valid u b rows depth ordinary state valid) _).1

/-- The second allocation retains its literal source key and rebinds only the original Mu. -/
theorem second_key (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains) :
    (second u b rows depth ordinary state).1.key =
      extend (first u b rows depth ordinary state).1.key [u.identity] (pair b.identity u.identity) := by
  simpa [second, SourceRecursiveIntersectionEnvironment.bindings,
    SourceRecursiveIntersectionEnvironment.binder] using
    SourceRecursiveIntersectionSchedule.entered_key (first u b rows depth ordinary state).2
      (first_valid u b rows depth ordinary state valid) (first u b rows depth ordinary state).1.key
      (bodyValue u b rows) (muValue u b rows depth ordinary) b.identity u.identity

/-- The actual second domain has precisely the original Mu name. -/
theorem second_names (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains)
    (name : Nat) : name ∈ names (second u b rows depth ordinary state).1.key ↔ name = u.identity := by
  have firstNames : name ∈ names (first u b rows depth ordinary state).1.key ↔ name = u.identity := by
    rw [SourceSynthesisUniverseReferenceControl.diagonal_key u (bodyValue u b rows) depth ordinary state valid,
      extend_names]
    simp [names, IntersectionEmptyDomain.emptyKey]
  rw [second_key u b rows depth ordinary state valid, extend_names, firstNames]
  simp only [List.mem_singleton, or_self]

/-- Physical readback in the second machine returns the complete original Mu. -/
theorem second_lookup (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains) (available : Available state.heap (muValue u b rows depth ordinary)) :
    lookup (secondState u b rows depth ordinary state).heap
      (second u b rows depth ordinary state).1.key u.identity = some (muValue u b rows depth ordinary) :=
  lookup_mu state.heap facts _ u (bodyValue u b rows) depth ordinary available
    ((second_names u b rows depth ordinary state valid u.identity).mpr rfl)

/-- Closed marker records differ from both the open body and its Mu identity. -/
theorem marker_distinct (u b m : Interned NodeKey)
    (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m markerRows markerDepth)) :
    m.identity ≠ b.identity ∧ m.identity ≠ u.identity := by
  have bodyAvailable : Available state.heap (bodyValue u b bodyRows) :=
    universeAvailable.children _ (by simp [children])
  constructor
  · intro same
    have equal := resident_identity_unique state.heap facts.coherent
      (markerValue m markerRows markerDepth) (bodyValue u b bodyRows)
      markerAvailable.resident bodyAvailable.resident m b rfl rfl same
    have impossible : ([] : List Reference) = [.interned u.identity] := congrArg Value.free equal
    cases impossible
  · intro same
    have impossible := resident_identity_unique state.heap facts.coherent
      (markerValue m markerRows markerDepth) (muValue u b bodyRows depth ordinary)
      markerAvailable.resident universeAvailable.resident m u rfl rfl same
    cases impossible

private theorem pair_cancel (left right common : Nat) (same : pair left common = pair right common) :
    left = right := by
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

/-- Marker-pair freshness follows from the actual two-entry cutoff set and coherent payloads. -/
theorem marker_pair_absent (u b m : Interned NodeKey)
    (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m markerRows markerDepth)) :
    pair m.identity u.identity ∉ (second u b bodyRows depth ordinary state).1.key.seen := by
  have different := marker_distinct u b m bodyRows markerRows markerDepth depth ordinary
    state facts universeAvailable markerAvailable
  intro member
  rcases (second_seen u b bodyRows depth ordinary state valid _).mp member with bodyPair | diagonal
  · exact different.1 (pair_cancel _ _ _ bodyPair)
  · exact different.2 (pair_cancel _ _ _ diagonal)

/-- A marker/reference child reaches actual right-reference resolution in the second domain. -/
theorem marker_reference_branch (u b m : Interned NodeKey)
    (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m markerRows markerDepth)) :
    decision (second u b bodyRows depth ordinary state).1.key
      (markerValue m markerRows markerDepth) (refValue u) = .rightReference := by
  have absent := marker_pair_absent u b m bodyRows markerRows markerDepth depth ordinary
    state facts valid universeAvailable markerAvailable
  have tagOrder : compare (1 : Nat) 4 = .lt := by decide
  simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
    Value.referenceOf, Value.free, absent, tagOrder]

/-- The actual second-domain lookup restores U without changing the current machine. -/
theorem marker_reference [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m markerRows markerDepth)) :
    onNode emptyGuard conjoin call (second u b bodyRows depth ordinary state).1
      (markerValue m markerRows markerDepth) (refValue u) (secondState u b bodyRows depth ordinary state) =
      call (second u b bodyRows depth ordinary state).1 (markerValue m markerRows markerDepth)
        (muValue u b bodyRows depth ordinary) (secondState u b bodyRows depth ordinary state) := by
  unfold onNode
  rw [marker_reference_branch u b m bodyRows markerRows markerDepth depth ordinary
    state facts valid universeAvailable markerAvailable]
  have member := (second_names u b bodyRows depth ordinary state valid u.identity).mpr rfl
  have found := second_lookup u b bodyRows depth ordinary state facts valid universeAvailable
  have read : SourcePreparedSharedRows.read state.heap u.identity = some (muValue u b bodyRows depth ordinary) := by
    simpa only [lookup, member, ite_true] using found
  simp only [reference, member, ite_true, read, Bool.false_eq_true, ite_false]

/-- After lookup, the two closed operands reset the nonempty free environment before Mu work. -/
theorem marker_universe_reset [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : Cache.Valid state.domains) :
    onNode emptyGuard conjoin call (second u b bodyRows depth ordinary state).1
      (markerValue m markerRows markerDepth) (muValue u b bodyRows depth ordinary)
      (secondState u b bodyRows depth ordinary state) =
      call IntersectionEmptyDomain.emptyDomain (markerValue m markerRows markerDepth)
        (muValue u b bodyRows depth ordinary) (secondState u b bodyRows depth ordinary state) := by
  have member := (second_names u b bodyRows depth ordinary state valid u.identity).mpr rfl
  have nonempty : (second u b bodyRows depth ordinary state).1.key.free.isEmpty = false := by
    cases values : (second u b bodyRows depth ordinary state).1.key.free with
    | nil => simp [names, values] at member
    | cons head tail => rfl
  have restart : reset (second u b bodyRows depth ordinary state).1.key
      (markerValue m markerRows markerDepth) (muValue u b bodyRows depth ordinary) = true := by
    simp [reset, Value.free, nonempty]
  have selected := reset_first (second u b bodyRows depth ordinary state).1.key
    (markerValue m markerRows markerDepth) (muValue u b bodyRows depth ordinary) rfl restart
  unfold onNode
  rw [selected]

/-- Seven source levels complete a marker/reference cross-child with a closed available result. -/
theorem marker_reference_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m markerRows markerDepth))
    (leaves : ∀ row ∈ markerRows, row.children = []) :
    ∃ value final,
      execute emptyGuard conjoin 7 (second u b bodyRows depth ordinary state).1
        (markerValue m markerRows markerDepth) (refValue u) (secondState u b bodyRows depth ordinary state) =
        .done value final ∧ Facts final.heap ∧ Available final.heap value ∧ value.free = [] := by
  obtain ⟨value, final, done, finalFacts, available, closed⟩ :=
    SourceSynthesisUniverseMarkerCompletion.marker_universe_complete emptyGuard conjoin
      m b u markerRows bodyRows markerDepth depth ordinary (secondState u b bodyRows depth ordinary state)
      ⟨facts, second_valid u b bodyRows depth ordinary state valid⟩ markerAvailable universeAvailable leaves
  refine ⟨value, final, ?_, finalFacts, available, closed⟩
  change onNode emptyGuard conjoin (execute emptyGuard conjoin 6)
    (second u b bodyRows depth ordinary state).1 (markerValue m markerRows markerDepth) (refValue u)
    (secondState u b bodyRows depth ordinary state) = _
  rw [marker_reference u b m bodyRows markerRows markerDepth depth ordinary emptyGuard conjoin _
    state facts valid universeAvailable markerAvailable]
  change onNode emptyGuard conjoin (execute emptyGuard conjoin 5)
    (second u b bodyRows depth ordinary state).1 (markerValue m markerRows markerDepth)
    (muValue u b bodyRows depth ordinary) (secondState u b bodyRows depth ordinary state) = _
  rw [marker_universe_reset u b m bodyRows markerRows markerDepth depth ordinary emptyGuard conjoin _ state valid]
  exact done

/-- The reverse cross-child takes one actual operand-swap step before the seven-level request. -/
theorem reference_marker_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m markerRows markerDepth))
    (leaves : ∀ row ∈ markerRows, row.children = []) :
    ∃ value final,
      execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1
        (refValue u) (markerValue m markerRows markerDepth) (secondState u b bodyRows depth ordinary state) =
        .done value final ∧ Facts final.heap ∧ Available final.heap value ∧ value.free = [] := by
  obtain ⟨value, final, done, finalFacts, available, closed⟩ :=
    marker_reference_complete u b m bodyRows markerRows markerDepth depth ordinary emptyGuard conjoin
      state facts valid universeAvailable markerAvailable leaves
  refine ⟨value, final, ?_, finalFacts, available, closed⟩
  have selected : decision (second u b bodyRows depth ordinary state).1.key
      (refValue u) (markerValue m markerRows markerDepth) = .swap := by rfl
  change onNode emptyGuard conjoin (execute emptyGuard conjoin 7)
    (second u b bodyRows depth ordinary state).1 (refValue u) (markerValue m markerRows markerDepth)
    (secondState u b bodyRows depth ordinary state) = _
  simpa only [onNode, selected] using done

end MicroCFTA.SourceSynthesisUniverseMarkerReference
