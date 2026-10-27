import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.EnumerationFrame

/-!
# Neutral captured payloads through the actual terminal prefix

The prefix reads and changes the representative forest.
It does not inspect stored payloads.
Its actual successful result retains the same assignment equations after neutralization.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open Language EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}
attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- An actual successful prefix preserves totality and adds exactly its listed equations. -/
theorem run_assignment
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State Symbol EnumGuard) (recorded : List Nat) (winner : Nat)
    (moved : EnumerationWaitingIndex.Waiting) (total : UnionFind.Total before.representatives)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) :
    UnionFind.Total after.representatives ∧
      (Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before ∧
        ∀ sc ∈ rest, assignment first.var = assignment sc.var) := by
  unfold run at success
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
  obtain ⟨scannedTotal, scanMeaning⟩ := representatives_assignment
    language meaning assignment fuel (first :: rest) before scanned actualRecorded total scanning
  obtain ⟨unitedTotal, unionMeaning⟩ := terminal_unions_assignment
    language meaning assignment fuel first.var rest scanned united scannedTotal unions
  obtain ⟨resolvedTotal, rootMeaning⟩ := representative_assignment
    language meaning assignment fuel first.var actualWinner united resolved unitedTotal resolution
  exact ⟨resolvedTotal, rootMeaning.trans (unionMeaning.trans (and_congr_left fun _ => scanMeaning))⟩

/-- The same successful prefix result commutes with neutralization of any stored payload. -/
theorem run_neutral
    (held fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State Symbol EnumGuard) (recorded : List Nat) (winner : Nat)
    (moved : EnumerationWaitingIndex.Waiting)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    Success (run fuel first rest waiting) (neutralize held before)
      (recorded, winner, moved) (neutralize held after) := by
  unfold run at success ⊢
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp success
  have scanMoved := mapM_transport (fun sc => representative fuel sc.var) (neutralize held) (fun _ => True)
    (first :: rest)
    (fun sc _ previous result next _ step =>
      ⟨trivial, representative_neutral held fuel sc.var result previous next step⟩)
    before scanned actualRecorded trivial scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unionsMoved := forM_transport (fun sc => unionVariables fuel first.var sc.var) (neutralize held) rest
    (fun sc _ previous next step => unionVariables_neutral held fuel first.var sc.var previous next step)
    scanned united unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  have resolutionMoved := representative_neutral held fuel first.var actualWinner united resolved resolution
  obtain ⟨same, rfl⟩ := (success_pure _ _ _ _).mp final
  exact (success_bind _ _ _ _ _).mpr ⟨actualRecorded, neutralize held scanned, scanMoved,
    (success_bind _ _ _ _ _).mpr ⟨(), neutralize held united, unionsMoved,
      (success_bind _ _ _ _ _).mpr ⟨actualWinner, neutralize held resolved, resolutionMoved,
        (success_pure _ _ _ _).mpr ⟨same, rfl⟩⟩⟩⟩

/-- The actual prefix adds the same equations when the captured payload restriction is removed. -/
theorem neutral_semantics
    (held fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State Symbol EnumGuard) (recorded : List Nat) (winner : Nat)
    (moved : EnumerationWaitingIndex.Waiting) (total : UnionFind.Total before.representatives)
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) :
    Satisfies language meaning assignment (neutralize held after) ↔
      Satisfies language meaning assignment (neutralize held before) ∧
        ∀ sc ∈ rest, assignment first.var = assignment sc.var :=
  (run_assignment fuel first rest waiting (neutralize held before) (neutralize held after)
    recorded winner moved total
    (run_neutral held fuel first rest waiting before after recorded winner moved success)
    language meaning assignment).2

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
