import MicroCFTA.SourcePruningEnumerationNativeSelectionProgress

namespace MicroCFTA.SourcePruningEnumerationRestart

open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationProgress
open SourcePruningRecordTypes SourcePruningEnumerationObservation SourcePruningEnumerationNodes

local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

variable {Typing : Type} {width : Nat}

/-- The literal initial cache selects an expansion from its original progress gates. -/
theorem initial_next_of_pending
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : SourceCurrentAllocatedPartialState.State width)
    (graph : Graph Symbol Constraint)
    (root : Nat) (value : InternedConstructorTemplates.Value Symbol Constraint)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller
      (EnumerationExpandableIndex.initial graph root))
    (safe : Safe (EnumerationState.initial root : EnumerationState.State Symbol Constraint))
    (proper : ProperState (EnumerationState.initial root : EnumerationState.State Symbol Constraint))
    (decoded : lookupNode caller.checked.native.machine.heap root = some value)
    (work : MergedOrdinaryHeight.recursiveBoundary value = false)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      residualMeaning assignment (EnumerationState.initial root)) :
    ∃ selected,
      EnumerationPureSelection.next (order metadata)
        (EnumerationExpandableIndex.initial graph root) = .expand selected ∧
      EnumerationDriver.Ready selected (EnumerationState.initial root : EnumerationState.State Symbol Constraint) ∧
      EnumerationReferences.IncomingAvoid selected
        (EnumerationState.initial root : EnumerationState.State Symbol Constraint) := by
  obtain ⟨selected, chosen, ready, incoming⟩ :=
    expand_of_pending formulas solver order metadata caller
      (EnumerationExpandableIndex.initial graph root)
      valid safe proper 0 root [] value rfl decoded (Or.inl work)
      ambient residualMeaning assignment satisfied
  refine ⟨selected, ?_, ready, incoming⟩
  exact Option.some.inj chosen

end MicroCFTA.SourcePruningEnumerationRestart
