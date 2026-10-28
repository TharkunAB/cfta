import MicroCFTA.SourcePruningEnumerationDischargeBoundary
import MicroCFTA.SourcePruningEnumerationNativeProgress

/-!
# Native selection progress from an original pending slot

Disable the stop rule at the original cache. A stored ordinary node or a
nonempty suspended bucket supplies work. A proper finite model excludes stuck
selection. The actual preference rule can then select a ready native root.
This statement retains free equality variables and empty recursive boundaries.
-/
namespace MicroCFTA.SourcePruningEnumerationRestart
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationProgress
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}

/-- The original proper model and pending native work force an actual ready selection. -/
theorem expand_of_pending
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (safe : Safe before.core) (proper : ProperState before.core)
    (slot handle : Nat) (scs : List Suspended) (value : Node)
    (stored : before.core.values[slot]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (work : MergedOrdinaryHeight.recursiveBoundary value = false ∨ scs ≠ [])
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      residualMeaning assignment before.core) :
    ∃ selected,
      decision none order metadata before = some (.expand selected) ∧
      EnumerationDriver.Ready selected before.core ∧
      EnumerationReferences.IncomingAvoid selected before.core := by
  have notDone : decision none order metadata before ≠ some .done := by
    intro done
    obtain ⟨native, observed, _available, _closed, boundary, empty⟩ :=
      done_pending_boundary order metadata caller before valid done slot handle scs stored
    have same : native = value := Option.some.inj (observed.symm.trans decoded)
    subst native
    rcases work with ordinary | nonempty
    · rw [ordinary] at boundary
      cases boundary
    · exact nonempty empty
  have notStuck := not_stuck_of_proper formulas solver none order metadata caller before
    valid safe proper ambient residualMeaning assignment satisfied
  cases chosen : EnumerationPureSelection.next (order metadata) before with
  | done => exact (notDone (congrArg some chosen)).elim
  | stuck => exact (notStuck (congrArg some chosen)).elim
  | expand selected =>
      have actual : decision none order metadata before = some (.expand selected) :=
        congrArg some chosen
      obtain ⟨ready, incoming, _realized⟩ := SourcePruningEnumerationRestart.selected
        none order metadata caller before selected valid safe actual
      exact ⟨selected, actual, ready, incoming⟩

end MicroCFTA.SourcePruningEnumerationRestart
