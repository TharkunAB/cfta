import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.EnumerationProgress

/-!
# Proper pending paths through the actual terminal prefix

Representative reads and unions retain the stored value array.
The fixed-bound successful prefix therefore retains every proper stored trie.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationProgress EnumerationSchedule

attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- Every actual successful terminal prefix retains proper stored suspended tries. -/
theorem run_proper
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State SourcePruningTemplates.Symbol EnumGuard)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (proper : ProperState before)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    ProperState after := by
  unfold run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scannedProper := mapM_invariant (fun sc => representative fuel sc.var) ProperState (first :: rest)
    (fun sc _ previous result next valid step => representative_proper fuel sc.var result previous next valid step)
    before scanned actualRecorded proper scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedProper := forM_invariant (fun sc => unionVariables fuel first.var sc.var) ProperState rest
    (fun sc _ previous next valid step => unionVariables_proper fuel first.var sc.var previous next valid step)
    scanned united scannedProper unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  have resolvedProper := representative_proper fuel first.var actualWinner united resolved
    unitedProper resolution
  obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
  exact resolvedProper

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
