import MicroCFTA.SourcePruningEnumerationAncestryExtension
import MicroCFTA.SourcePruningEnumerationTerminalPrefix

/-!
# Recursion ancestry through the actual terminal prefix

Representative reads and unions change only the forest.
Every successful prefix retains all old keys and exact expansion ancestry.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningEnumerationAncestryExtension
attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- An actual successful terminal prefix extends every slot and retains expansion ancestry. -/
theorem run_ancestry_extension
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State SourcePruningTemplates.Symbol EnumGuard)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    Extends before after ∧ after.expansionAncestry = before.expansionAncestry := by
  unfold run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedFields := mapM_invariant (fun sc => representative fuel sc.var)
    (fun state => Extends before state ∧ state.expansionAncestry = before.expansionAncestry)
    (first :: rest) (by
      intro sc _ previous result next fields step
      obtain ⟨_found, _lookup, _root, rfl⟩ :=
        (representative_success fuel sc.var previous next result).mp step
      exact fields) before scanned actualRecorded ⟨Extends.refl before, rfl⟩ scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedFields := forM_invariant (fun sc => unionVariables fuel first.var sc.var)
    (fun state => Extends before state ∧ state.expansionAncestry = before.expansionAncestry)
    rest (by
      intro sc _ previous next fields step
      obtain ⟨_forest, _lookup, rfl⟩ :=
        (unionVariables_success fuel first.var sc.var previous next).mp step
      exact fields) scanned united scannedFields unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨_found, _lookup, _root, rfl⟩ :=
    (representative_success fuel first.var united resolved actualWinner).mp resolution
  obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
  exact unitedFields

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
