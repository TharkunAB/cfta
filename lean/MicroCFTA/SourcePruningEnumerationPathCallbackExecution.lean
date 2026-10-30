import MicroCFTA.SourcePruningEnumerationPathCallbackInvariant
import MicroCFTA.SourcePruningEnumerationPreparedRecursive

/-!
# The actual recursive call retains the original stored paths

The recursive function remains uninterpreted.
-/

namespace MicroCFTA.SourcePruningEnumerationPathCallbackExecution
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationPathTransport SourcePruningEnumerationHookInvocation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
variable {width : Nat} {Typing : Type} {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "NativeResult" => HookResult (SourcePruningEnumerationRecursive.Output width Typing)
  (SourcePruningEnumerationRecursive.Failure width Typing) width
local notation "PreparedResult" => HookResult (SourcePruningEnumerationRecursive.Output width Typing)
  (SourcePruningEnumerationPreparedRecursive.Failure width Typing) width

/-- The actual native false branch calls recur with the same original path predicate. -/
theorem native_false_paths_of_forecast
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → NativeResult)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (work : Nat) (metadata : Metadata Typing)
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation
      (SourcePruningEnumerationRecursive.continueWith recur graph templates stop order work metadata target)
      checkEmpty r n p h k target scs before edges caller queries fragment reached saved after)
    (guards : List Constraint) (known : ∀ edge ∈ edges, edge.entry.key.constraint ∈ guards)
    (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (updated : Metadata Typing) (callbackCore : Core)
    (observed : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates work metadata target (.inl fragment) after.core) =
      [.ok ((false, updated), callbackCore)]) :
    StatePaths P (EnumerationExpandableIndex.frame callbackCore after).core ∧
      SourcePruningEnumerationRecursive.continueWith recur graph templates stop order work metadata target
        fragment reached saved after =
      recur updated reached saved (EnumerationExpandableIndex.frame callbackCore after)
        (SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame callbackCore after)) := by
  have success : Success
      (SourcePruningRecordTypes.recordTypes graph templates work metadata target (.inl fragment))
      after.core (false, updated) callbackCore := by
    unfold Success
    rw [observed]
    exact List.mem_singleton_self _
  refine ⟨?_, ?_⟩
  · exact invocation.recorded_paths_of_forecast guards known projected tails paths inherited
      graph templates work metadata (false, updated) callbackCore success
  · simp only [SourcePruningEnumerationRecursive.continueWith, observed]

/-- The actual prepared false branch calls recur with the same original path predicate. -/
theorem prepared_false_paths_of_forecast
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → PreparedResult)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (work : Nat) (metadata : Metadata Typing)
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation
      (SourcePruningEnumerationPreparedRecursive.continueWith recur graph templates stop order work metadata target)
      checkEmpty r n p h k target scs before edges caller queries fragment reached saved after)
    (guards : List Constraint) (known : ∀ edge ∈ edges, edge.entry.key.constraint ∈ guards)
    (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (updated : Metadata Typing) (callbackCore : Core)
    (observed : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates work metadata target (.inl fragment) after.core) =
      [.ok ((false, updated), callbackCore)]) :
    StatePaths P (EnumerationExpandableIndex.frame callbackCore after).core ∧
      SourcePruningEnumerationPreparedRecursive.continueWith recur graph templates stop order work metadata target
        fragment reached saved after =
      recur updated reached saved (EnumerationExpandableIndex.frame callbackCore after)
        (SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame callbackCore after)) := by
  have success : Success
      (SourcePruningRecordTypes.recordTypes graph templates work metadata target (.inl fragment))
      after.core (false, updated) callbackCore := by
    unfold Success
    rw [observed]
    exact List.mem_singleton_self _
  refine ⟨?_, ?_⟩
  · exact invocation.recorded_paths_of_forecast guards known projected tails paths inherited
      graph templates work metadata (false, updated) callbackCore success
  · simp only [SourcePruningEnumerationPreparedRecursive.continueWith, observed]

end MicroCFTA.SourcePruningEnumerationPathCallbackExecution
