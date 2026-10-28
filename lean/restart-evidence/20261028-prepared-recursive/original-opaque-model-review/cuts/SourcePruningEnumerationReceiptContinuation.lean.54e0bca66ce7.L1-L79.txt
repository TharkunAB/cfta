import MicroCFTA.SourcePruningEnumerationNativeContinuations

/-!
# Continue one actual captured receipt

Only a completed receipt invokes the hook. A valid rejection advances its
actual native endpoint. Other receipts retain the exact edge stop.
-/
namespace MicroCFTA.SourcePruningEnumerationReceiptContinuation
open EnumerationState
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- Invoke the hook once after an actual completed receipt. -/
def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width) :
    Option (Receipt width) → Result Output Reason width
  | none => .stopped [] [] (.edge none)
  | some receipt =>
      match receipt with
      | .complete fragment caller queries after =>
          match hook fragment caller queries after with
          | .complete outputs reached saved => .complete [receipt] outputs reached saved
          | .stopped outputs reason endpoint =>
              .stopped [] outputs (.continuation receipt reason endpoint)
      | other =>
          match SourcePruningEnumerationNativeBranches.advance other with
          | none => .stopped [] [] (.edge (some other))
          | some (caller, queries) => .complete [other] [] caller queries

/-- A missing receipt remains an edge stop without a supplied endpoint. -/
theorem missing
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width) :
    run hook none = .stopped [] [] (.edge none) := rfl

/-- A completed hook supplies its exact output and returned native endpoint. -/
theorem completed
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (fragment : Fragment) (caller reached : Caller width) (queries saved : Queries)
    (after : Cached) (outputs : List Output)
    (continued : hook fragment caller queries after = .complete outputs reached saved) :
    run hook (some (.complete fragment caller queries after)) =
      .complete [.complete fragment caller queries after] outputs reached saved := by
  simp only [run, continued]

/-- A stopped hook retains its receipt, outputs, reason and actual optional endpoint. -/
theorem stopped_hook
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (fragment : Fragment) (caller : Caller width) (queries : Queries) (after : Cached)
    (outputs : List Output) (reason : Reason) (endpoint : Option (Caller width × Queries))
    (stopped : hook fragment caller queries after = .stopped outputs reason endpoint) :
    run hook (some (.complete fragment caller queries after)) =
      .stopped [] outputs (.continuation (.complete fragment caller queries after) reason endpoint) := by
  simp only [run, stopped]

/-- The identity hook embeds the whole single-receipt advance, including every stop. -/
theorem identity_run (current : Option (Receipt width)) :
    run (SourcePruningEnumerationNativeContinuations.identityHook
      (Output := Output) (Reason := Reason)) current =
      match current with
      | none => .stopped [] [] (.edge none)
      | some receipt =>
          match SourcePruningEnumerationNativeBranches.advance receipt with
          | none => .stopped [] [] (.edge (some receipt))
          | some (caller, queries) => .complete [receipt] [] caller queries := by
  cases current with
  | none => rfl
  | some receipt => cases receipt <;> rfl

end MicroCFTA.SourcePruningEnumerationReceiptContinuation
