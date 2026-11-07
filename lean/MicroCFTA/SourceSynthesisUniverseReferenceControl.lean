import MicroCFTA.SourceRecursiveIntersectionKernelCalls
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence

/-!
# Actual open-reference/Mu diagonal control

The request starts in the reserved empty domain. Operand sorting precedes
Mu entry, and entry retains the physical binder and both actual caches.
These equations leave body products and outer canonical reconstruction open.
-/
namespace MicroCFTA.SourceSynthesisUniverseReferenceControl
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedFreshProbeKeys
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionDomain SourceRecursiveIntersectionKernel

variable {Symbol Guard : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Allocate the literal Mu/open-reference diagonal domain from the empty domain. -/
def diagonal (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) : Interned DomainKey × Cache.State DomainKey :=
  SourceRecursiveIntersectionEnvironment.enter state.domains IntersectionEmptyDomain.emptyKey
    (Value.mu entry stored depth ordinary) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) entry.identity entry.identity

/-- A source reference sorts after the physical Mu before any binder lookup. -/
theorem referenceMu (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) (state : Machine Symbol Guard) :
    onNode emptyGuard conjoin call IntersectionEmptyDomain.emptyDomain (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) (Value.mu entry stored depth ordinary) state =
      call IntersectionEmptyDomain.emptyDomain (Value.mu entry stored depth ordinary) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) state := by rfl

/-- After the swap, the empty-domain request enters Mu before resolving its reference. -/
theorem muReference (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) (state : Machine Symbol Guard) :
    onNode emptyGuard conjoin call IntersectionEmptyDomain.emptyDomain (Value.mu entry stored depth ordinary) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) state =
      mu call IntersectionEmptyDomain.emptyDomain (Value.mu entry stored depth ordinary) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) state := by
  have tagOrder : compare (2 : Nat) 4 = .lt := by decide
  simp [onNode, decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
    identity, payload, Value.referenceOf, Value.free, tagOrder,
    IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey]

/-- Two actual control steps retain the body call and its real optional-Mu continuation. -/
theorem execute_referenceMu (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (state : Machine Symbol Guard) :
    execute emptyGuard conjoin (fuel + 2) IntersectionEmptyDomain.emptyDomain (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) (Value.mu entry stored depth ordinary) state =
      (execute emptyGuard conjoin fuel (diagonal entry stored depth ordinary state).1 stored (Value.reference (Reference.interned entry.identity) : Value Symbol Guard)
        {state with domains := (diagonal entry stored depth ordinary state).2}).bind
        (fun value after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity) value after.heap) after) := by
  rw [execute, referenceMu, execute, muReference]
  rfl

/-- At the two-step prefix bound, exhaustion occurs after the exact domain allocation. -/
theorem execute_referenceMu_two (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) :
    execute emptyGuard conjoin 2 IntersectionEmptyDomain.emptyDomain (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) (Value.mu entry stored depth ordinary) state =
      .failed .exhausted {state with domains := (diagonal entry stored depth ordinary state).2} := by
  rw [show 2 = 0 + 2 from rfl, execute_referenceMu]
  rfl

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- The actual cache allocation has the singleton binder and diagonal cutoff key. -/
theorem diagonal_key (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains) :
    (diagonal entry stored depth ordinary state).1.key =
      extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity entry.identity) := by
  simpa [diagonal, SourceRecursiveIntersectionEnvironment.bindings,
    SourceRecursiveIntersectionEnvironment.binder] using
    SourceRecursiveIntersectionSchedule.entered_key state.domains valid IntersectionEmptyDomain.emptyKey
      (Value.mu entry stored depth ordinary) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) entry.identity entry.identity

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- The diagonal cutoff comes from actual entry, rather than a supplied seen-pair premise. -/
theorem diagonal_seen (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains) :
    pair entry.identity entry.identity ∈ (diagonal entry stored depth ordinary state).1.key.seen := by
  rw [diagonal_key entry stored depth ordinary state valid]
  exact (extend_seen _ _ _ _).mpr (Or.inl rfl)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- The original available Mu supplies the reservation for its open source reference. -/
private theorem reference_available_of_mu (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (available : Available state.heap (Value.mu entry stored depth ordinary)) : Available state.heap (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) := by
  have resident := resident_entry state.heap facts.coherent (Value.mu entry stored depth ordinary) available.resident entry rfl
  have issued := (facts.coherent.valid.2.2 entry.key entry resident).2
  apply reference_available
  intro name member
  have same : name = entry.identity := by simpa [Value.free] using member
  subst name
  exact ⟨entry.key, issued⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Facts and actual availability recover the complete original Mu in the allocated domain. -/
theorem diagonal_lookup (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (valid : Cache.Valid state.domains) (available : Available state.heap (Value.mu entry stored depth ordinary)) :
    lookup state.heap (diagonal entry stored depth ordinary state).1.key entry.identity = some (Value.mu entry stored depth ordinary) := by
  rw [diagonal_key entry stored depth ordinary state valid]
  have found := SourceRecursiveIntersectionEnvironment.enter_lookup state.heap facts
    IntersectionEmptyDomain.emptyKey (Value.mu entry stored depth ordinary) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) available
    (reference_available_of_mu entry stored depth ordinary state facts available)
    entry.identity entry.identity (entry.identity, (Value.mu entry stored depth ordinary))
    (by simp [SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder])
  simpa [SourceRecursiveIntersectionEnvironment.bindings,
    SourceRecursiveIntersectionEnvironment.binder] using found

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Actual reference resolution keeps the entered cache and restores the original stored binder. -/
theorem reference_entered (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard →
      Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (Value.mu entry stored depth ordinary)) (other : Value Symbol Guard) (left : Bool) :
    reference call (diagonal entry stored depth ordinary state).1 entry.identity other left
      {state with domains := (diagonal entry stored depth ordinary state).2} =
      if left then call (diagonal entry stored depth ordinary state).1 (Value.mu entry stored depth ordinary) other
        {state with domains := (diagonal entry stored depth ordinary state).2}
      else call (diagonal entry stored depth ordinary state).1 other (Value.mu entry stored depth ordinary)
        {state with domains := (diagonal entry stored depth ordinary state).2} := by
  have found := diagonal_lookup entry stored depth ordinary state facts valid available
  by_cases member : entry.identity ∈ names (diagonal entry stored depth ordinary state).1.key
  · have read := found
    simp only [lookup, member, ite_true] at read
    simp only [reference, member, ite_true, read]
  · simp only [lookup, member, ite_false] at found
    cases found

/-- Open diagonal references return the actual RecIntersect placeholder before lookup. -/
theorem execute_repeatedReference (entry : Interned NodeKey) (stored depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (state : Machine Symbol Guard) (valid : Cache.Valid state.domains) :
    execute emptyGuard conjoin (fuel + 1) (diagonal entry stored depth ordinary state).1 (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard)
      {state with domains := (diagonal entry stored depth ordinary state).2} =
      .done (repeatedValue (pair entry.identity entry.identity))
        {state with domains := (diagonal entry stored depth ordinary state).2} := by
  have same : closedSelf (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) = false := by simp [closedSelf, Value.free]
  have order : greater (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) = false := by
    simp [greater, compareValue, tag, SourceRecursiveIntersectionSchedule.reference_interned]
  have selected := repeated_first (diagonal entry stored depth ordinary state).1.key (Value.reference (Reference.interned entry.identity) : Value Symbol Guard) (Value.reference (Reference.interned entry.identity) : Value Symbol Guard)
    rfl rfl same order entry.identity entry.identity rfl rfl
    (diagonal_seen entry stored depth ordinary state valid)
  simp only [execute, onNode, selected]

end MicroCFTA.SourceSynthesisUniverseReferenceControl
