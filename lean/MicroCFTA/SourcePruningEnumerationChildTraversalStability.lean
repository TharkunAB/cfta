import MicroCFTA.SourcePruningEnumerationChildTraversal
import MicroCFTA.SourcePruningEnumerationChildDispatchStability

namespace MicroCFTA.SourcePruningEnumerationChildTraversal
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual complete child trace retains every endpoint at larger primitive bounds. -/
theorem Trace.moreBounds
    {checkEmpty : Bool} {r n p h k R N P H K : Nat}
    {inputs : List (Node × List Suspended)} {beforeCaller afterCaller : Caller width}
    {before after : Cached} {queries afterQueries : Queries} {fragments : List Fragment}
    (trace : Trace checkEmpty r n p h k inputs beforeCaller before queries
      fragments afterCaller after afterQueries)
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    Trace checkEmpty R N P H K inputs beforeCaller before queries
      fragments afterCaller after afterQueries := by
  induction trace with
  | nil => exact .nil _ _ _
  | cons head _tail ih =>
    exact .cons (SourcePruningEnumerationChildDispatch.run_singleton_stable head
      enoughRepresentative enoughNative enoughP enoughH enoughIndex) ih

/-- A completed ordered traversal keeps its full result at larger primitive bounds. -/
theorem run_complete_moreBounds
    {checkEmpty : Bool} {r n p h k R N P H K : Nat}
    {inputs : List (Node × List Suspended)} {beforeCaller afterCaller : Caller width}
    {before after : Cached} {queries afterQueries : Queries} {fragments : List Fragment}
    (completed : run checkEmpty r n p h k inputs beforeCaller before queries =
      .complete fragments afterCaller afterQueries after)
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    run checkEmpty R N P H K inputs beforeCaller before queries =
      .complete fragments afterCaller afterQueries after := by
  exact trace_complete ((complete_trace checkEmpty r n p h k inputs beforeCaller afterCaller
    before after queries afterQueries fragments completed).moreBounds
      enoughRepresentative enoughNative enoughP enoughH enoughIndex)

end MicroCFTA.SourcePruningEnumerationChildTraversal
