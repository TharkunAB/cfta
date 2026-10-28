import MicroCFTA.SourcePruningEnumerationPreparedRecursiveEquations

/-!
# Actual prepared recursive phases at one common work bound

The selected prefix and prepared continuation share their actual endpoint.
Their stable observations combine at the sum of their original bounds.
The parked branch consumes its actual indexed restart without another prefix.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Output)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint
  (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "EntryRaw" => List (Except EnumerationState.Error
  ((Nat × Nat × List Suspended × Node) × Core))
local notation "Preparation" => EntryRaw × Option (MergedSourceComparison.Result Symbol Constraint Node)
local notation "Fold" => SourcePruningEnumerationNativeContinuations.Result
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)

/-- Repeated recursion consumes the exact indexed restart at its actual returned cache. -/
theorem resume_parked
    (workFuel recursiveFuel uv : Nat) (metadata updated : Metadata Typing)
    (caller : Caller width) (queries : Queries) (before parked : Cached)
    (checked core : Core) (next : Option Next)
    (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (recursiveFuel + 1)
      metadata caller queries before (some (.expand uv)) =
        resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
          updated caller queries (EnumerationExpandableIndex.frame core parked) next := by
  rw [resume, observed]

/-- Stable actual prefix and prepared dispatch observations use one sufficient common sum. -/
theorem resume_depth_stable
    (prefixFuel dispatchFuel recursiveFuel uv : Nat) (metadata updated : Metadata Typing)
    (caller reached : Caller width) (queries saved : Queries) (before after : Cached)
    (preparation : Preparation) (result : Fold (Output width Typing) (Failure width Typing) width)
    (prefixRun : ∀ extra, ∃ (checked : Core) (prepared : Prepared),
      SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
        metadata (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before queries =
          .narrowed checked prepared reached saved (some [.ok ((), after.core)]) (some after)
            (some [.ok ((false, updated), after.core)]) none)
    (dispatched : ∀ extra, SourcePruningEnumerationSelectedContinuations.run
      (continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (dispatchFuel + extra) recursiveFuel)
        graph templates stop order (dispatchFuel + extra) updated uv)
      checkEmpty (dispatchFuel + extra) (dispatchFuel + extra) (dispatchFuel + extra)
        (dispatchFuel + extra) (dispatchFuel + extra) (dispatchFuel + extra) (dispatchFuel + extra)
        uv edgesOf reached after saved = (preparation, some result)) :
    ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
      (prefixFuel + dispatchFuel + extra) (recursiveFuel + 1)
      metadata caller queries before (some (.expand uv)) = finish uv result := by
  intro extra
  obtain ⟨checked, prepared, prefixAt⟩ := prefixRun (dispatchFuel + extra)
  have actualPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata (prefixFuel + dispatchFuel + extra) (prefixFuel + dispatchFuel + extra)
      (prefixFuel + dispatchFuel + extra) (prefixFuel + dispatchFuel + extra)
      (prefixFuel + dispatchFuel + extra) (prefixFuel + dispatchFuel + extra) uv caller before queries =
        .narrowed checked prepared reached saved (some [.ok ((), after.core)]) (some after)
          (some [.ok ((false, updated), after.core)]) none := by
    simpa only [Nat.add_assoc] using prefixAt
  have actualDispatch := dispatched (prefixFuel + extra)
  have common : dispatchFuel + (prefixFuel + extra) = prefixFuel + dispatchFuel + extra := by omega
  rw [common] at actualDispatch
  rw [resume_prepared holeKey fits admits graph templates checkEmpty edgesOf stop order
    (prefixFuel + dispatchFuel + extra) recursiveFuel uv metadata updated caller reached queries saved
    before after checked after.core after.core prepared actualPrefix]
  rw [actualDispatch]

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
