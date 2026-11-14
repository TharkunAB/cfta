import MicroCFTA.SourcePruningEnumerationParkedLanguage
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

/-!
# Exact limits of a repeated recursion key

Retargeting a bucket leaves its recursion key unchanged.
An existential pre-clear model needs one post-clear model with all removed Holds.
The actual parked branch restarts without a Left callback for that slot.
These facts do not construct a model or establish source reachability.
-/
namespace MicroCFTA.EnumerationState

/-- Retargeting every suspended variable preserves the exact recursion key. -/
theorem recursionKey_retarget (handle : Nat) (bucket : List Suspended) (mapVar : Nat → Nat) :
    recursionKey handle (bucket.map fun sc => (⟨sc.trie, mapVar sc.var⟩ : Suspended)) =
      recursionKey handle bucket := by
  simp only [recursionKey, List.map_map]

end MicroCFTA.EnumerationState

namespace MicroCFTA.SourcePruningEnumerationRecursion
open Language Fragments EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- An actual true-clear has a model exactly when one parked model also realizes its removed bucket. -/
theorem checkRepeated_exists_satisfies_iff
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (fuel uv handle : Nat) (bucket : List Suspended)
    (before after : State Symbol EnumGuard)
    (ready : EnumerationDriver.Ready uv before)
    (stored : before.values[uv]? = some (.unenumerated (some handle) bucket))
    (observed : Success (checkRepeated heap fuel uv handle bucket) before true after) :
    (∃ assignment : Nat → Term Symbol, Satisfies language meaning assignment before) ↔
      ∃ assignment : Nat → Term Symbol,
        Satisfies language meaning assignment after ∧
        ∀ sc ∈ bucket, Suspended.Holds assignment (assignment uv) sc := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact ⟨assignment, (checkRepeated_true_satisfies heap language meaning assignment
      fuel uv handle bucket before after ready stored observed).mp satisfied⟩
  · rintro ⟨assignment, satisfied, removed⟩
    exact ⟨assignment, (checkRepeated_true_satisfies heap language meaning assignment
      fuel uv handle bucket before after ready stored observed).mpr ⟨satisfied, removed⟩⟩

end MicroCFTA.SourcePruningEnumerationRecursion

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {width : Nat}
local notation "Result" => NativeContinuations.HookResult (Output width Typing) (Failure width Typing) width
local notation "Fold" => NativeContinuations.Result (Output width Typing) (Failure width Typing) width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (ChildDispatch.Observation width → Option Cached → Fold) → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual parked singleton resumes directly at its returned core and decision. -/
theorem resumeWithNarrow_parked
    (child : Visitor)
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel uv : Nat)
    (metadata updated : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before parked : Cached) (checked core : Core) (next : Option Next)
    (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow narrow graph templates
      stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    resumeWithNarrow child narrow graph templates checkEmpty edgesOf stop order workFuel
        (recursiveFuel + 1) metadata caller queries before (some (.expand uv)) =
      resumeWithNarrow child narrow graph templates checkEmpty edgesOf stop order workFuel
        recursiveFuel updated caller queries (EnumerationExpandableIndex.frame core parked) next := by
  simp only [resumeWithNarrow, observed]

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
