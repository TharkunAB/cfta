import MicroCFTA.InternedProbeDependencyAge
import MicroCFTA.InternedRequestAgreement

/-!
# Exact request agreement at an old complete Mu

The original probes of an old complete Mu have only older boundary
identities. Local observed agreement therefore makes the two requested
probe pairs equal. Actual request replay then gives equal complete
results. The paired probe observations remain the induction premises.
-/
namespace MicroCFTA.InternedOldProbeReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedMissReadback InternedStoredMuOrigins
open InternedNodeIdentityFootprint InternedBoundaryAge InternedBoundaryAtoms
open InternedObservedAbsence InternedBoundaryFreeAge InternedProbeDependencyAge
open InternedBinderProtocol (NodeKey)

/-- A value whose full identity footprint is old has no fresh reference or Mu boundary. -/
theorem footprint_clear (value : Value Symbol Guard) (cutoff : Nat)
    (old : ∀ identity, Occurs identity value → identity < cutoff) : Clear (Fresh cutoff) value := by
  intro atom member
  cases atom with
  | empty | node | union => simp [Fresh]
  | ref name =>
      cases name with
      | depth | uninterned | state | intersection => simp [Fresh]
      | interned identity =>
          have older := old identity (atom_occurs value _ identity (Or.inl rfl) member)
          simpa only [Fresh, Nat.not_le] using older
  | mu identity =>
      have older := old identity (atom_occurs value _ identity (Or.inr rfl) member)
      simpa only [Fresh, Nat.not_le] using older

/-- Both original probes are clear at every cutoff at or after their parent's reservation. -/
theorem origin_probes_clear [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (origin : Origin entry body depth ordinary)
    (cutoff : Nat) (old : entry.identity ≤ cutoff) :
    Clear (Fresh cutoff) depth ∧ Clear (Fresh cutoff) ordinary := by
  constructor
  · exact footprint_clear depth cutoff (fun identity occurrence =>
      Nat.lt_of_lt_of_le (origin_probes_older entry body depth ordinary origin identity (Or.inl occurrence)) old)
  · exact footprint_clear ordinary cutoff (fun identity occurrence =>
      Nat.lt_of_lt_of_le (origin_probes_older entry body depth ordinary origin identity (Or.inr occurrence)) old)

/-- Local paired observations identify the exact probes of an old complete source Mu. -/
theorem old_probes_same [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body firstDepth firstOrdinary secondDepth secondOrdinary : Value Symbol Guard)
    (origin : Origin entry body firstDepth firstOrdinary) (cutoff : Nat) (old : entry.identity ≤ cutoff)
    (depthRelated : Related (Fresh cutoff) firstDepth secondDepth)
    (ordinaryRelated : Related (Fresh cutoff) firstOrdinary secondOrdinary) :
    firstDepth = secondDepth ∧ firstOrdinary = secondOrdinary := by
  have clear := origin_probes_clear entry body firstDepth firstOrdinary origin cutoff old
  exact ⟨depthRelated.2 clear.1, ordinaryRelated.2 clear.2⟩

/-- An old complete left hit agrees with an actual right request once its two smaller probe observations hold. -/
theorem old_hit_same [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (entry : Interned NodeKey) (body firstDepth firstOrdinary secondDepth secondOrdinary : Value Symbol Guard)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (left right afterRight common : State Symbol Guard) (rightValue : Value Symbol Guard)
    (leftCoherent : Coherent left) (rightValid : InternedConstructorTemplates.Valid right)
    (origins : InternedStoredMuOrigins.Heap left)
    (stored : left.nodeRecords (muKey firstDepth firstOrdinary) = some (.mu entry body firstDepth firstOrdinary))
    (cutoff : Nat) (old : entry.identity ≤ cutoff)
    (depthRelated : Related (Fresh cutoff) firstDepth secondDepth)
    (ordinaryRelated : Related (Fresh cutoff) firstOrdinary secondOrdinary)
    (rightDone : request smart secondDepth secondOrdinary (callback expression environment) right = .done rightValue afterRight)
    (leftGrowth : Grows left common) (rightGrowth : Grows afterRight common) :
    finish smart (.mu entry body firstDepth firstOrdinary) = rightValue := by
  obtain ⟨depthSame, ordinarySame⟩ := old_probes_same entry body firstDepth firstOrdinary secondDepth secondOrdinary
    (origins _ _ _ _ _ stored) cutoff old depthRelated ordinaryRelated
  subst secondDepth
  subst secondOrdinary
  obtain ⟨actual, installed, _⟩ := leftCoherent.nodes _ _ stored
  have leftDone : request smart firstDepth firstOrdinary (callback expression environment) left =
      .done (finish smart (.mu entry body firstDepth firstOrdinary)) left := by
    simp only [request, installed, stored]
  exact InternedRequestAgreement.source_request_same smart firstDepth firstOrdinary expression expression
    environment environment left right left afterRight common _ rightValue leftCoherent.valid rightValid
    leftDone rightDone leftGrowth rightGrowth

end MicroCFTA.InternedOldProbeReplay
