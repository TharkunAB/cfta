import MicroCFTA.SourceRecursiveIntersectionMaybeMuCoverage
import MicroCFTA.InternedFreshOrdinaryOldCall

/-!
# Repaired nested pending encounters from actual source optional binders

The actual stored source body determines the repaired lexical expression
and available captures. Complete incoming coverage derives an encountered
active ancestor if construction reports pending. No callback completion,
probe equality, or pending-origin witness is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open Cache InternedConstructorTemplates InternedRecordCoherence InternedNestedFacts
open InternedProbeProvenance InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)

/-- A pending actual optional binder derives the exact repaired nested callback encounter and its original ancestor reservation. -/
theorem pending_encounter [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey) (facts : Facts state) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    InternedFreshOrdinaryEncounter.Encounter key final := by
  rw [maybeMu_eq pair body state state facts available] at stopped
  split at stopped
  · apply InternedFreshOrdinaryEncounter.build_encounter _ (leaves body) state facts
      (leaves_available body state available) [] covered _ key final stopped
    constructor <;> intro name member <;> cases member
  · cases stopped

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
