import MicroCFTA.SourcePruningEnumerationKeyAncestry
import MicroCFTA.SourcePruningEnumerationTerminalPrefix

/-!
# Historical key shapes through the actual terminal prefix

Representative reads and unions change only the forest.
The successful prefix retains both complete ancestry fields.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningEnumerationKeyAncestry
attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- Every actual successful terminal prefix retains the original key carrier. -/
theorem run_key_ancestry
    {carrier : List (List (List (List Nat)))}
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State SourcePruningTemplates.Symbol EnumGuard)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (bounded : KeyAncestry carrier before)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    KeyAncestry carrier after := by
  unfold run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedBounded := mapM_invariant (fun sc => representative fuel sc.var) (KeyAncestry carrier)
    (first :: rest) (by
      intro sc _ previous result next valid step
      obtain ⟨_found, _lookup, _root, rfl⟩ :=
        (representative_success fuel sc.var previous next result).mp step
      exact valid) before scanned actualRecorded bounded scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedBounded := forM_invariant (fun sc => unionVariables fuel first.var sc.var)
    (KeyAncestry carrier) rest (by
      intro sc _ previous next valid step
      obtain ⟨_forest, _lookup, rfl⟩ :=
        (unionVariables_success fuel first.var sc.var previous next).mp step
      exact valid) scanned united scannedBounded unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨_found, _lookup, _root, rfl⟩ :=
    (representative_success fuel first.var united resolved actualWinner).mp resolution
  obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
  exact unitedBounded

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
