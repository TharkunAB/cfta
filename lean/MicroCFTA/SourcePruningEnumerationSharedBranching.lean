import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations

/-!
# Ordered shared scans with an actual row visitor

Each sibling receives the same captured enumeration cache.
A visitor and its hook finish before the next sibling starts.
Native callers and queries pass through their actual reached endpoints.
The prepared adapter is exactly the existing captured-edge worker.
This factor does not add eager child recursion or prove whole traversal completion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedBranching
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result Stop HookResult advance endpoint)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- Execute ordered row visitors with branch-local caches and shared native endpoints. -/
noncomputable def scan
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) : List Edge → Caller width → Queries → Result Output Reason width
  | [], caller, queries => .complete [] [] caller queries
  | edge :: rest, caller, queries =>
      match visit edge caller queries before with
      | .stopped processed outputs current => .stopped processed outputs current
      | .complete processed outputs reached saved =>
          match scan visit before rest reached saved with
          | .complete later remaining finalCaller finalQueries =>
              .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
          | .stopped later remaining current =>
              .stopped (processed ++ later) (outputs ++ remaining) current

/-- An empty scan retains the complete input native endpoint. -/
theorem scan_nil
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) (caller : Caller width) (queries : Queries) :
    scan visit before [] caller queries = .complete [] [] caller queries := rfl

/-- A stopped visitor keeps its exact prefix and stop without running the sibling suffix. -/
theorem scan_stopped
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) (edge : Edge) (rest : List Edge) (caller : Caller width) (queries : Queries)
    (processed : List (Receipt width)) (outputs : List Output) (current : Stop Reason width)
    (observed : visit edge caller queries before = .stopped processed outputs current) :
    scan visit before (edge :: rest) caller queries = .stopped processed outputs current := by
  simp only [scan, observed]

/-- Every completed visitor precedes its suffix at the actual returned native endpoint. -/
theorem scan_complete
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) (edge : Edge) (rest : List Edge) (caller reached : Caller width) (queries saved : Queries)
    (processed : List (Receipt width)) (outputs : List Output)
    (observed : visit edge caller queries before = .complete processed outputs reached saved) :
    scan visit before (edge :: rest) caller queries =
      match scan visit before rest reached saved with
      | .complete later remaining finalCaller finalQueries =>
          .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
      | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current := by
  simp only [scan, observed]

/-- A visitor with no receipts or outputs still passes its reached globals to the suffix. -/
theorem scan_pruned
    (visit : Edge → Caller width → Queries → Cached → Result Output Reason width)
    (before : Cached) (edge : Edge) (rest : List Edge) (caller reached : Caller width) (queries saved : Queries)
    (observed : visit edge caller queries before = .complete [] [] reached saved) :
    scan visit before (edge :: rest) caller queries = scan visit before rest reached saved := by
  simp only [scan, observed]
  cases scan visit before rest reached saved <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Visit one actual captured edge and its hook without replacing any receipt or stopped endpoint. -/
noncomputable def visitCaptured
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : Edge) (caller : Caller width) (queries : Queries) (before : Cached) : Result Output Reason width :=
  match CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
  | none => .stopped [] [] (.edge none (caller, queries))
  | some receipt =>
      match receipt with
      | .complete fragment reached saved after =>
          match hook fragment reached saved after with
          | .stopped outputs reason reachedEndpoint =>
              .stopped [] outputs (.continuation receipt reason reachedEndpoint)
          | .complete outputs finalCaller finalQueries =>
              .complete [receipt] outputs finalCaller finalQueries
      | other =>
          match advance other with
          | none => .stopped [] [] (.edge (some other) (endpoint other caller queries))
          | some (reached, saved) => .complete [other] [] reached saved

/-- The existing shared worker is this generic scan with the actual captured-edge adapter. -/
theorem run_eq_scan
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List Edge) (caller : Caller width) (queries : Queries) :
    NativeContinuations.run hook checkEmpty r n p h k target scs before edges caller queries =
      scan (visitCaptured hook checkEmpty r n p h k target scs) before edges caller queries := by
  induction edges generalizing caller queries with
  | nil => rfl
  | cons edge rest ih =>
      cases observed : CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => simp only [NativeContinuations.run, scan, visitCaptured, observed]
      | some receipt =>
          cases receipt <;> simp only [NativeContinuations.run, scan, visitCaptured, observed]
          all_goals first | rfl | (split <;> simp_all only [] <;> rfl)

end MicroCFTA.SourcePruningEnumerationSharedBranching
