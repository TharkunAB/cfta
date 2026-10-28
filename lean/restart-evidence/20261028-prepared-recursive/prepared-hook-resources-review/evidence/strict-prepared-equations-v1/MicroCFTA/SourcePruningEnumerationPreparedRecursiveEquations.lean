import MicroCFTA.SourcePruningEnumerationPreparedRecursive

/-!
# The actual prepared recursive continuation

The selected prefix supplies the callback metadata and reached endpoint.
Preparation then runs once at that endpoint. Each completed receipt invokes
the Left callback before the recursive restart and the next sibling.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint
  (Node × Option (EnumerateM Symbol Constraint Unit))
variable {Typing Key : Type} {width : Nat}
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (SourcePruningEnumerationRecursive.Output width Typing) (Failure width Typing) width

/-- A rejected Left callback emits no output and keeps its actual native endpoint. -/
theorem continueWith_rejected
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata updated : Metadata Typing) (uv : Nat)
    (fragment : Fragment) (caller : Caller width) (queries : Queries)
    (before : Cached) (core : Core)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates callbackFuel metadata uv (.inl fragment) before.core) =
        [.ok ((true, updated), core)]) :
    continueWith recur graph templates stop order callbackFuel metadata uv fragment caller queries before =
      .complete [] caller queries := by
  simp only [continueWith, recorded]

/-- A successful Left callback restarts at its actual returned cache and metadata. -/
theorem continueWith_restarted
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata updated : Metadata Typing) (uv : Nat)
    (fragment : Fragment) (caller : Caller width) (queries : Queries)
    (before : Cached) (core : Core)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates callbackFuel metadata uv (.inl fragment) before.core) =
        [.ok ((false, updated), core)]) :
    continueWith recur graph templates stop order callbackFuel metadata uv fragment caller queries before =
      recur updated caller queries (EnumerationExpandableIndex.frame core before)
        (SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame core before)) := by
  simp only [continueWith, recorded]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual Right continuation supplies the complete prepared recursive dispatch. -/
theorem resume_prepared
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel fuel uv : Nat)
    (metadata updated : Metadata Typing) (caller reached : Caller width)
    (queries saved : Queries) (before after : Cached)
    (checked actionCore rightCore : Core) (prepared : Prepared)
    (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .narrowed checked prepared reached saved (some [.ok ((), actionCore)]) (some after)
          (some [.ok ((false, updated), rightCore)]) none) :
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (fuel + 1)
      metadata caller queries before (some (.expand uv)) =
      let continuation := SourcePruningEnumerationSelectedContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved
      match continuation.2 with
      | none => .stopped [] (.preparation uv continuation.1) none
      | some folded => finish uv folded := by
  simp only [resume, observed]

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
