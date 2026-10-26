import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# Scalar bounds for the actual terminal prefix

Representative lookup and class union change only the forest. Every actual
successful prefix therefore preserves the counter and suspended mass.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
attribute [local instance] terminalPrefixMonadList

/-- Every actual successful prefix changes only the representative forest. -/
theorem success_frame
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (before after : Core)
    (result : List Nat × Nat × EnumerationWaitingIndex.Waiting)
    (completed : Success (run fuel first rest waiting) before result after) :
    after = {before with representatives := after.representatives} := by
  simp only [run] at completed
  obtain ⟨recorded, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp completed
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨winner, resolved, resolution, finished⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨_resultSame, stateSame⟩ := (success_pure _ result resolved after).mp finished
  have scanFrame : scanned = {before with representatives := scanned.representatives} := by
    apply mapM_invariant (fun (sc : Suspended) => representative fuel sc.var)
      (fun current => current = {before with representatives := current.representatives})
      (first :: rest) ?_ before scanned recorded rfl scan
    intro sc _member current root next previous success
    obtain ⟨found, _lookup, _rootSame, nextSame⟩ :=
      (representative_success fuel sc.var current next root).mp success
    rw [nextSame]
    exact congrArg (fun state : Core => {state with representatives := found.forest}) previous
  have unionFrame : united = {before with representatives := united.representatives} := by
    apply forM_invariant (fun (sc : Suspended) => unionVariables fuel first.var sc.var)
      (fun current => current = {before with representatives := current.representatives})
      rest ?_ scanned united scanFrame unions
    intro sc _member current next previous success
    obtain ⟨forest, _lookup, nextSame⟩ :=
      (unionVariables_success fuel first.var sc.var current next).mp success
    rw [nextSame]
    exact congrArg (fun state : Core => {state with representatives := forest}) previous
  obtain ⟨found, _lookup, _rootSame, resolvedSame⟩ :=
    (representative_success fuel first.var united resolved winner).mp resolution
  rw [stateSame, resolvedSame]
  exact congrArg (fun state : Core => {state with representatives := found.forest}) unionFrame

/-- An actual singleton prefix retains the original counter and all suspended occurrences. -/
theorem observed_counter_mass
    (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (before after : Core)
    (result : List Nat × Nat × EnumerationWaitingIndex.Waiting)
    (observed : ExceptT.run (run fuel first rest waiting before) = [.ok (result, after)]) :
    after.counter = before.counter ∧ suspendedBound after = suspendedBound before := by
  have completed : Success (run fuel first rest waiting) before result after := by
    simp only [Success, observed, List.mem_singleton]
  have frame := success_frame fuel first rest waiting before after result completed
  constructor
  · exact congrArg (fun state : Core => state.counter) frame
  · exact SourcePruningEnumerationPrefixAdmission.suspendedBound_values before after
      (congrArg (fun state : Core => state.values) frame)

end MicroCFTA.SourcePruningEnumerationTerminalPrefix
