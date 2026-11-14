import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationSharedChildDispatchStability
import MicroCFTA.SourcePruningEnumerationNativeIndexStability

/-!
# Successful replay of actual shared selected and captured rows

Each successful actual child call retains its exact endpoint at larger bounds.
The actual selected row retains its own-class prefix and residual update.
The captured row retains its actual finalization cache.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Each actual completed child trace retains its exact calls at larger bounds. -/
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
      exact .cons (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run_singleton_stable
        head enoughRepresentative enoughNative enoughP enoughH enoughIndex) ih

/-- The complete actual child traversal retains every returned field at larger bounds. -/
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

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A completed actual selected row retains its fragment, caller, queries and full cache. -/
theorem complete_stable
    {checkEmpty : Bool} {r R n N p P h H k K : Nat}
    {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries} {fragment : Fragment}
    (completed : run checkEmpty r n p h k scs edge caller before queries =
      .complete fragment reached saved after)
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    run checkEmpty R N P H K scs edge caller before queries =
      .complete fragment reached saved after := by
  cases prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => simp only [run, prepared, reduceCtorEq] at completed
  | some rows =>
      cases rows with
      | nil => simp only [run, prepared, reduceCtorEq] at completed
      | cons first rest =>
          cases rest with
          | cons second rest => simp only [run, prepared, reduceCtorEq] at completed
          | nil =>
              rcases first with ⟨⟨symbol, staged, residual⟩, middle⟩
              cases children : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run
                  checkEmpty r n p h k (staged.map (fun input => (input.1, input.2.1)))
                  caller middle queries with
              | stopped fragments observation candidate =>
                  simp only [run, prepared, children, reduceCtorEq] at completed
              | complete fragments childCaller childQueries childCache =>
                  have childrenLater :=
                    SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run_complete_moreBounds
                      children enoughRepresentative enoughNative enoughP enoughH enoughIndex
                  simpa only [run, prepared, children, childrenLater] using completed

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A completed captured row retains its actual selected result and finalization cache. -/
theorem complete_stable
    {checkEmpty : Bool} {r R n N p P h H k K target : Nat}
    {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries} {fragment : Fragment}
    (completed : run checkEmpty r n p h k target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P)
    (enoughH : h ≤ H) (enoughIndex : k ≤ K) :
    run checkEmpty R N P H K target scs edge caller before queries =
      some (.complete fragment reached saved after) := by
  cases selected : SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.run
      checkEmpty r n p h k scs edge caller before queries with
  | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ =>
      simp only [run, selected, Option.some.injEq, reduceCtorEq] at completed
  | complete produced childCaller childQueries middle =>
      have selectedLater := SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.complete_stable
        selected enoughRepresentative enoughNative enoughP enoughH enoughIndex
      cases finished : SourcePruningEnumerationFinalize.run childCaller.checked.native.machine.heap
          k target produced middle with
      | none =>
          simp only [run, selected, finished, Option.some.injEq, reduceCtorEq] at completed
      | some finalCache =>
          have finishedLater := SourcePruningEnumerationFinalize.run_some_moreFuel
            childCaller.checked.native.machine.heap k (K - k) target produced middle finalCache finished
          have sameFuel : k + (K - k) = K := by omega
          rw [sameFuel] at finishedLater
          simpa only [run, selected, selectedLater, finished, finishedLater] using completed

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
