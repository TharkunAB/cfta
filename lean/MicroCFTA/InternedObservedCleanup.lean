import MicroCFTA.InternedObservedRootAlternatives
import MicroCFTA.InternedBoundaryFreeAge
import MicroCFTA.InternedBoundaryCleanup
import MicroCFTA.InternedCleanupEmptiness

/-!
# Observed agreement through actual recursive cleanup

Empty and bare-self body observations determine empty cleanup results.
An observed result cannot retain a forbidden fresh Mu identity. Smart
cleanup must return its unused body or remove its bare self reference.
Actual source provenance excludes a second fresh local from an old body.
-/
namespace MicroCFTA.InternedObservedCleanup
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence InternedProbeProvenance
open InternedObservedAbsence InternedObservedRootAlternatives InternedBoundaryFreeAge
open InternedNestedFacts InternedNestedProvenance InternedPendingOrigins
open InternedCleanupEmptiness InternedBoundaryCleanup
open InternedBinderProtocol (NodeRef NodeKey)

/-- Cleanup preserves empty observations and exact observed bodies without assuming callback key equality. -/
theorem finish_related (forbidden : NodeRef → Prop) (smart : Bool)
    (firstEntry secondEntry : Interned NodeKey)
    (firstBody firstDepth firstOrdinary secondBody secondDepth secondOrdinary : Value Symbol Guard)
    (fresh : forbidden (.mu firstEntry.identity))
    (bodies : RelatedOwn forbidden (.interned firstEntry.identity) (.interned secondEntry.identity) firstBody secondBody)
    (secondAbsent : Clear forbidden firstBody → .interned secondEntry.identity ∉ firstBody.free) :
    Related forbidden (finish smart (.mu firstEntry firstBody firstDepth firstOrdinary))
      (finish smart (.mu secondEntry secondBody secondDepth secondOrdinary)) := by
  constructor
  · rw [finish_empty_reference_iff, finish_empty_reference_iff]
    apply and_congr Iff.rfl
    apply or_congr ?_ bodies.2
    simpa only [← InternedEmptyNormalization.reference_empty] using bodies.1.1
  · intro clear
    have noMu : .mu firstEntry.identity ∉ InternedBoundaryAtoms.atoms
        (finish smart (.mu firstEntry firstBody firstDepth firstOrdinary)) :=
      fun present => clear _ present fresh
    obtain ⟨smartTrue, cases⟩ := finish_cases smart firstEntry firstBody firstDepth firstOrdinary noMu
    subst smart
    rcases cases with ⟨returned, _⟩ | ⟨returned, bare⟩
    · have bodyClear : Clear forbidden firstBody := returned ▸ clear
      have same := bodies.1.2 bodyClear
      have unused := secondAbsent bodyClear
      rw [returned, ← same]
      simp [finish, cleanup, unused]
    · have otherBare := bodies.2.mp bare
      rw [returned, otherBare]
      simp [finish, cleanup, Value.free, Value.referenceOf]

/-- Actual nested source execution supplies the remaining fresh-name exclusion for the cleanup comparison. -/
theorem source_finish_related [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (dense : Cache.Dense before.nodes)
    (origins : Origins pending before) (covered : Covered pending before)
    (smart : Bool) (firstEntry secondEntry : Interned NodeKey)
    (firstBody firstDepth firstOrdinary secondBody secondDepth secondOrdinary : Value Symbol Guard)
    (available : Available (build expression environment before).state firstBody)
    (firstFresh : before.nodes.next ≤ firstEntry.identity) (secondFresh : before.nodes.next ≤ secondEntry.identity)
    (bodies : RelatedOwn (Fresh before.nodes.next) (.interned firstEntry.identity) (.interned secondEntry.identity)
      firstBody secondBody) :
    Related (Fresh before.nodes.next) (finish smart (.mu firstEntry firstBody firstDepth firstOrdinary))
      (finish smart (.mu secondEntry secondBody secondDepth secondOrdinary)) := by
  apply finish_related (Fresh before.nodes.next) smart firstEntry secondEntry
    firstBody firstDepth firstOrdinary secondBody secondDepth secondOrdinary firstFresh bodies
  intro clear
  exact build_fresh_absent expression environment before facts inputs dense origins covered firstBody available clear
    secondEntry.identity secondFresh

end MicroCFTA.InternedObservedCleanup
