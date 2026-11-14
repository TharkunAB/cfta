import MicroCFTA.SourcePruningRecordTypes
import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
import MicroCFTA.SourcePruningEnumerationSelection

namespace MicroCFTA.SourcePruningEnumerationRestart
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningRecordTypes SourcePruningEnumerationObservation SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Typing : Type} {width : Nat}

/-- Test the stop rule on every remaining candidate before selecting unblocked work. -/
def decision (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) : Option Next :=
  match stop with
  | none => some (EnumerationPureSelection.next (order metadata) before)
  | some rule =>
      let remaining := EnumerationIndexSelection.candidates before
      if !remaining.isEmpty && remaining.all (rule metadata) then none
      else some (EnumerationPureSelection.next (order metadata) before)

/-- Reject blocked work and otherwise retain the exact metadata and enumeration state. -/
def run (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    EnumerateM Symbol Constraint (Metadata Typing × Option Next) :=
  let next := decision stop order metadata before
  fun state => if next = some .stuck then [] else [.ok ((metadata, next), state)]

/-- Restart rejects only stuck selection and otherwise returns its exact pure decision. -/
theorem run_exact (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    ExceptT.run ((run stop order metadata before) before.core) =
      if decision stop order metadata before = some .stuck then []
      else [.ok ((metadata, decision stop order metadata before), before.core)] := rfl

/-- A frame with the same allocation counter retains the decision at the same metadata. -/
theorem decision_frame (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (after : EnumerationState.State Symbol Constraint) (counter : after.counter = before.core.counter) :
    decision stop order metadata (EnumerationExpandableIndex.frame after before) =
      decision stop order metadata before := by
  cases stop <;>
    simp only [decision, EnumerationPureSelection.next, EnumerationPureSelection.find,
      EnumerationIndexSelection.candidates, EnumerationExpandableIndex.frame, counter]
  all_goals rfl

/-- An actual restart expansion derives readiness and its closed available pending value. -/
theorem selected (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : SourceCurrentAllocatedPartialState.State width)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (uv : Nat)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (safe : Safe before.core) (chosen : decision stop order metadata before = some (.expand uv)) :
    EnumerationDriver.Ready uv before.core ∧ EnumerationReferences.IncomingAvoid uv before.core ∧
      ∃ (handle : Nat) (scs : List Suspended)
        (value : InternedConstructorTemplates.Value Symbol Constraint),
        before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
        lookupNode caller.checked.native.machine.heap handle = some value ∧
        InternedProbeProvenance.Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
        (!(MergedOrdinaryHeight.recursiveBoundary value && scs.isEmpty)) = true := by
  have picked : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := valid
  exact ⟨SourcePruningEnumerationSelection.ready caller.checked.native.machine.heap before
      (order metadata) uv safe roots paths counts flags picked,
    SourcePruningEnumerationSelection.incoming caller.checked.native.machine.heap before
      (order metadata) uv safe roots paths counts flags picked,
    SourcePruningEnumerationSelection.realized caller.checked.native.machine.heap before
      (order metadata) uv safe.1.aligned realized flags picked⟩

end MicroCFTA.SourcePruningEnumerationRestart
