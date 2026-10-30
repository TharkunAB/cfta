import MicroCFTA.SourcePruningEnumerationPathHookInvocation
import MicroCFTA.SourcePruningEnumerationPathRecordingValues

/-!
# The original stored path predicate at every recorded callback

Every invocation uses the original captured starting cache.
Every successful recording preserves the same stored path predicate.
The law covers every Boolean recording result before output membership.
-/
namespace MicroCFTA.SourcePruningEnumerationHookInvocation
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Typing : Type} {Output : Type u} {Reason : Type v}
variable {P : EqualityTrie.Path → Prop}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual successful callback recording preserves the original forecast paths. -/
theorem Invocation.recorded_paths_of_forecast
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after)
    (guards : List Constraint) (known : ∀ edge ∈ edges, edge.entry.key.constraint ∈ guards)
    (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (paths : StatePaths P before.core) (inherited : BucketPaths P scs)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (work : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recorded : Bool × SourcePruningRecordTypes.Metadata Typing)
    (callbackCore : EnumerationState.State Symbol Constraint)
    (observed : Success
      (SourcePruningRecordTypes.recordTypes graph templates work metadata target (.inl fragment))
      after.core recorded callbackCore) :
    StatePaths P (EnumerationExpandableIndex.frame callbackCore after).core := by
  have headPaths := invocation.paths_of_forecast guards known projected tails paths inherited
  change StatePaths P callbackCore
  exact SourcePruningEnumerationPathRecordingValues.recordTypes_paths graph templates work metadata
    target (.inl fragment) after.core callbackCore recorded headPaths observed

end MicroCFTA.SourcePruningEnumerationHookInvocation
