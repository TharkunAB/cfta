import MicroCFTA.EnumerationFlatCached
import MicroCFTA.SourcePruningEnumerationRestart

/-!
# Restart selection with a direct-parent cache

Selection uses the raw allocation counter and both cached indexes.
Core correspondence retains these observations without an index invariant.
-/

namespace MicroCFTA.SourceFlatPruningRestart

open EnumerationState EnumerationFlatCached SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Typing : Type}

/-- Scan expandable raw IDs in ascending allocation order. -/
def candidates (before : Cached Symbol Constraint) : List Nat :=
  (List.range before.core.counter).filter before.expandable

/-- Keep source preference and its candidate-minus-waiting selection. -/
def next (preference : List Nat → Option Nat) (before : Cached Symbol Constraint) : Next :=
  let remaining := candidates before
  pickNext preference (if remaining.isEmpty then none
    else some (remaining.filter fun uv => (before.waiting uv).isNone))

/-- Test the stop rule on all candidates before selecting unblocked work. -/
def decision (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached Symbol Constraint) : Option Next :=
  match stop with
  | none => some (next (order metadata) before)
  | some rule =>
      let remaining := candidates before
      if !remaining.isEmpty && remaining.all (rule metadata) then none
      else some (next (order metadata) before)

/-- Reject stuck work and otherwise retain the exact metadata and core. -/
def run (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached Symbol Constraint) : EnumerationFlatState.Action Symbol Constraint (Metadata Typing × Option Next) :=
  let selected := decision stop order metadata before
  fun core => if selected = some .stuck then [] else [.ok ((metadata, selected), core)]

/-- Complete related caches have the same pure restart decision. -/
theorem decision_related (related : Related flat earlier)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing) :
    decision stop order metadata flat = SourcePruningEnumerationRestart.decision stop order metadata earlier := by
  cases stop <;>
    simp only [decision, next, candidates, SourcePruningEnumerationRestart.decision,
      EnumerationPureSelection.next, EnumerationPureSelection.find, EnumerationIndexSelection.candidates,
      related.core.counter, related.expandable, related.waiting]

/-- Restart retains both related cores or rejects the same stuck selection. -/
theorem run_related (related : Related flat earlier)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing) :
    EnumerationResultRelation.Results EnumerationFlatState.Related
      (run stop order metadata flat flat.core)
      (SourcePruningEnumerationRestart.run stop order metadata earlier earlier.core) := by
  unfold run SourcePruningEnumerationRestart.run
  rw [decision_related related]
  split
  · exact .nil
  · exact .cons (.ok _ related.core) .nil

end MicroCFTA.SourceFlatPruningRestart
