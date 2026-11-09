import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations

/-!
# Continue one shared captured receipt

Only a completed receipt invokes the hook. Every edge stop retains its
actual endpoint or the known entry endpoint when no receipt exists.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation
open EnumerationState
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
local notation "endpoint" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.endpoint
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- Continue one receipt and preserve the known endpoint on every edge stop. -/
def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (caller : Caller width) (queries : Queries) : Option (Receipt width) → Result Output Reason width
  | none => .stopped [] [] (.edge none (caller, queries))
  | some receipt =>
      match receipt with
      | .complete fragment reached saved after =>
          match hook fragment reached saved after with
          | .complete outputs actual returned => .complete [receipt] outputs actual returned
          | .stopped outputs reason actual => .stopped [] outputs (.continuation receipt reason actual)
      | other =>
          match advance other with
          | none => .stopped [] [] (.edge (some other) (endpoint other caller queries))
          | some (reached, saved) => .complete [other] [] reached saved

/-- A missing receipt retains the known entry endpoint. -/
theorem missing
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (caller : Caller width) (queries : Queries) :
    run hook caller queries none = .stopped [] [] (.edge none (caller, queries)) := rfl

/-- A completed hook supplies its exact outputs and endpoint. -/
theorem completed
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (caller reached actual : Caller width) (queries saved returned : Queries)
    (fragment : Fragment) (after : Cached) (outputs : List Output)
    (continued : hook fragment reached saved after = .complete outputs actual returned) :
    run hook caller queries (some (.complete fragment reached saved after)) =
      .complete [.complete fragment reached saved after] outputs actual returned := by
  simp only [run, continued]

/-- A stopped hook retains its receipt, reason, outputs and optional endpoint. -/
theorem stopped_hook
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (caller reached : Caller width) (queries saved : Queries) (fragment : Fragment) (after : Cached)
    (outputs : List Output) (reason : Reason) (actual : Option (Caller width × Queries))
    (stopped : hook fragment reached saved after = .stopped outputs reason actual) :
    run hook caller queries (some (.complete fragment reached saved after)) =
      .stopped [] outputs (.continuation (.complete fragment reached saved after) reason actual) := by
  simp only [run, stopped]

/-- A failed finalization keeps its actual endpoint and pre-finalize cache. -/
theorem finalize_stopped
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (caller reached : Caller width) (queries saved : Queries) (fragment : Fragment) (after : Cached) :
    run hook caller queries (some (.finalizeStopped fragment reached saved after)) =
      .stopped [] [] (.edge (some (.finalizeStopped fragment reached saved after)) (reached, saved)) := rfl

/-- Unsupported pure work retains the known entry endpoint. -/
theorem unhandled
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (caller : Caller width) (queries : Queries) :
    run hook caller queries (some .unhandled) =
      .stopped [] [] (.edge (some .unhandled) (caller, queries)) := rfl

end MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation
