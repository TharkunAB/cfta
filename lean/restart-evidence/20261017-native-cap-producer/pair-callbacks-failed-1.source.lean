import MicroCFTA.SourceCurrentConstrainedCapPairOccurrences
import MicroCFTA.SourceCurrentConstrainedCapNormalizedBinder

/-!
# Actual marker transport in a normalized source callback

The old pair occurs as one direct root alternative. The other alternative
is an actual closed ordinary record and can have a nonhereditary guard.
Actual substitution replaces the old pair with a marked local reference.
The raw union has a maximal root occurrence. Filtering returns the ordinary
record. This local callback producer does not certify earlier Mu winners.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapPairOccurrenceCallbacks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedFacts InternedStoredMuOrigins InternedNestedProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapPairOccurrences
variable {Symbol Guard : Type}

/-- The actual callback local carries the old request's positive weight. -/
def mark (weight : Reference → Nat) (name : Reference) (bound : Nat) : Reference → Nat :=
  fun actual => if actual = name then bound else weight actual

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual stored substitution replaces the root pair and retains the exact closed ordinary record. -/
theorem substitute (old name : Reference) (entry node : Interned NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat)
    (state : State Symbol Guard) (facts : Facts state)
    (available : Available state (SourceCurrentConstrainedCapNormalizedBinder.body old entry node edges level outerLevel)) :
    InternedFreshOrdinaryStoredSubstitution.execute
      (SourceCurrentConstrainedCapNormalizedBinder.body old entry node edges level outerLevel)
      (InternedStoredSubstitutionRebind.replacement old (.reference name)) state =
      .done (run (makeUnion [.reference name, .node node edges level []]) state).1
        (run (makeUnion [.reference name, .node node edges level []]) state).2 := by
  rw [← InternedStoredSubstitutionRebind.rebind_build _ old name state state facts.coherent available]
  simp [SourceCurrentConstrainedCapNormalizedBinder.body, InternedStoredSubstitution.encode,
    InternedStoredSubstitution.encodeMany, InternedStoredSubstitution.leaves,
    InternedStoredSubstitution.manyLeaves, InternedStoredSubstitution.slot, List.findIdx_cons,
    InternedFreshOrdinaryConstruction.build, InternedFreshOrdinaryConstruction.buildMany,
    InternedNestedConstruction.Outcome.bind, InternedNestedConstruction.work, Value.free, Value.referenceOf]

/-- A marked actual callback derives both its raw occurrence classification and its normalized output cap. -/
theorem callback (weight : Reference → Nat) (bound : Nat) (annotation : Guard → Prop) (depth : Nat)
    (old name : Reference) (entry node : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat)
    (state : State Symbol Guard) (normal : Normal state)
    (available : Available state (SourceCurrentConstrainedCapNormalizedBinder.body old entry node edges level outerLevel))
    (reference : Available state (.reference name))
    (bounded : SourceCurrentConstrainedCap.Cap annotation depth (.node node edges level [])) :
    let raw := run (makeUnion [.reference name, .node node edges level []]) state
    InternedFreshOrdinaryStoredSubstitution.execute
        (SourceCurrentConstrainedCapNormalizedBinder.body old entry node edges level outerLevel)
        (InternedStoredSubstitutionRebind.replacement old (.reference name)) state = .done raw.1 raw.2 ∧
      Classified (mark weight name bound) bound raw.1 ∧
      SourceRecursiveIntersectionMaybeMu.callback old
        (SourceCurrentConstrainedCapNormalizedBinder.body old entry node edges level outerLevel) name state =
        .done (.node node edges level []) raw.2 ∧
      Classified (mark weight name bound) bound (.node node edges level []) ∧
      SourceCurrentConstrainedCap.Cap annotation depth (.node node edges level []) ∧
      name ∉ (Value.node node edges level []).free := by
  dsimp only
  have ordinary := available.children (.node node edges level []) (by
    simp [SourceCurrentConstrainedCapNormalizedBinder.body, children])
  have classified : Classified (mark weight name bound) bound (.node node edges level []) := by
    constructor <;> simp [FreeLE, deepNames, Value.free]
  refine ⟨substitute old name entry node edges level outerLevel state normal.facts available, ?_,
    SourceCurrentConstrainedCapNormalizedBinder.callback old name entry node edges level outerLevel
      state normal.facts available reference, classified, bounded, by simp [Value.free]⟩
  apply SourceCurrentConstrainedCapPairOccurrences.makeUnion (mark weight name bound) bound _ state normal
  · intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact reference
    · exact List.mem_singleton.mp member ▸ ordinary
  · intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact SourceCurrentConstrainedCapPairOccurrences.reference _ bound name (by simp [mark])
    · exact List.mem_singleton.mp member ▸ classified

/-- The marked callback's exact ordinary output is discarded as a binder candidate's unused local body. -/
theorem finish_callback (weight : Reference → Nat) (bound : Nat) (annotation : Guard → Prop) (depth : Nat)
    (old : Reference) (entry node owner : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (level outerLevel : Nat)
    (state : State Symbol Guard) (normal : Normal state)
    (available : Available state (SourceCurrentConstrainedCapNormalizedBinder.body old entry node edges level outerLevel))
    (reference : Available state (.reference (.interned owner.identity)))
    (bounded : SourceCurrentConstrainedCap.Cap annotation depth (.node node edges level []))
    (probe ordinary : Value Symbol Guard) :
    ∃ after,
      SourceRecursiveIntersectionMaybeMu.callback old
          (SourceCurrentConstrainedCapNormalizedBinder.body old entry node edges level outerLevel)
          (.interned owner.identity) state = .done (.node node edges level []) after ∧
        InternedNestedConstruction.finish true (.mu owner (.node node edges level []) probe ordinary) = .node node edges level [] ∧
        Classified (mark weight (.interned owner.identity) bound) bound (.node node edges level []) ∧
        SourceCurrentConstrainedCap.Cap annotation depth (.node node edges level []) := by
  have actual := callback weight bound annotation depth old (.interned owner.identity) entry node edges level outerLevel
    state normal available reference bounded
  exact ⟨_, actual.2.2.1, by simp [InternedNestedConstruction.finish, cleanup, Value.free], actual.2.2.2.1, bounded⟩

end Actual
end MicroCFTA.SourceCurrentConstrainedCapPairOccurrenceCallbacks
