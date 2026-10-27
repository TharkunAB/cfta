import MicroCFTA.SourcePruningEnumerationResumeExecution

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
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
local notation "Fold" => SourcePruningEnumerationNativeContinuations.Result
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)

/-- Stable prefix and scan observations share one work bound at every recursive depth. -/
theorem resume_depth_stable
    (prefixFuel scanFuel recursiveFuel uv : Nat) (metadata updated : Metadata Typing)
    (caller reached : Caller width) (queries saved : Queries) (before after : Cached)
    (raw : EntryRaw) (result : Fold (Output width Typing) (Failure width Typing) width)
    (prefixRun : ∀ extra, ∃ (checked : Core) (prepared : Prepared),
      SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
        metadata (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra)
        (prefixFuel + extra) (prefixFuel + extra) (prefixFuel + extra) uv caller before queries =
        .narrowed checked prepared reached saved (some [.ok ((), after.core)]) (some after)
          (some [.ok ((false, updated), after.core)]) none)
    (ordinary : ∀ extra, SourcePruningEnumerationNativeOrdinaryContinuations.run
      (continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (scanFuel + extra) recursiveFuel)
        graph templates stop order (scanFuel + extra) updated uv)
      checkEmpty (scanFuel + extra) (scanFuel + extra) (scanFuel + extra) (scanFuel + extra)
        (scanFuel + extra) uv edgesOf reached after saved = (raw, some result)) :
    ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
      (prefixFuel + scanFuel + extra) (recursiveFuel + 1) metadata caller queries before (some (.expand uv)) =
        finish uv result := by
  intro extra
  obtain ⟨checked, prepared, prefixAt⟩ := prefixRun (scanFuel + extra)
  have actualPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata (prefixFuel + scanFuel + extra) (prefixFuel + scanFuel + extra)
      (prefixFuel + scanFuel + extra) (prefixFuel + scanFuel + extra)
      (prefixFuel + scanFuel + extra) (prefixFuel + scanFuel + extra) uv caller before queries =
      .narrowed checked prepared reached saved (some [.ok ((), after.core)]) (some after)
        (some [.ok ((false, updated), after.core)]) none := by
    simpa only [Nat.add_assoc] using prefixAt
  have actualOrdinary := ordinary (prefixFuel + extra)
  have sameFuel : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
  rw [sameFuel] at actualOrdinary
  exact resume_narrowed_ordinary holeKey fits admits graph templates checkEmpty edgesOf stop order
    (prefixFuel + scanFuel + extra) recursiveFuel uv metadata updated caller reached queries saved before after
    checked prepared raw result actualPrefix actualOrdinary

end MicroCFTA.SourcePruningEnumerationRecursive
