import MicroCFTA.SourcePruningEnumerationCapturedEdge

namespace MicroCFTA.SourcePruningEnumerationNativeBranches
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}

/-- Complete the ordered alternatives or retain the first unsupported receipt. -/
inductive Result (width : Nat) where
  /-- Every alternative has a continuable result, including valid rejections. -/
  | complete (processed : List (Receipt width)) (caller : Caller width) (queries : Queries)
  /-- Retain processed alternatives and the exact first noncontinuable result. -/
  | stopped (processed : List (Receipt width)) (current : Option (Receipt width))

/-- Retain native effects after a completed edge, arity rejection or valid child rejection. -/
def advance : Receipt width → Option (Caller width × Queries)
  | .complete _ caller queries _ => some (caller, queries)
  | .rejected caller queries _ => some (caller, queries)
  | .stopped _ (.ok (some []), caller, queries, _outer, _waiting) (some _) => some (caller, queries)
  | _ => none

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Restore the captured enumeration input while retaining reached native caller and queries. -/
noncomputable def run (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (before : Cached) : List (EdgeValue Symbol Constraint) → Caller width → Queries → Result width
  | [], caller, queries => .complete [] caller queries
  | edge :: rest, caller, queries =>
      match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => .stopped [] none
      | some receipt =>
          match advance receipt with
          | none => .stopped [] (some receipt)
          | some (middleCaller, middleQueries) =>
              match run checkEmpty r n p h k target scs before rest middleCaller middleQueries with
              | .complete processed afterCaller saved => .complete (receipt :: processed) afterCaller saved
              | .stopped processed current => .stopped (receipt :: processed) current

/-- Each ordered receipt records a call at the same captured enumeration input. -/
inductive Trace (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached) :
    List (EdgeValue Symbol Constraint) → Caller width → Queries →
      List (Receipt width) → Caller width → Queries → Prop
  /-- No alternative changes the current native endpoint. -/
  | nil (caller : Caller width) (queries : Queries) :
      Trace checkEmpty r n p h k target scs before [] caller queries [] caller queries
  /-- The head retains its exact receipt and supplies only the next native endpoint. -/
  | cons {edge : EdgeValue Symbol Constraint} {rest : List (EdgeValue Symbol Constraint)}
      {caller middleCaller afterCaller : Caller width} {queries middleQueries saved : Queries}
      {receipt : Receipt width} {processed : List (Receipt width)}
      (head : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
        some receipt)
      (continued : advance receipt = some (middleCaller, middleQueries))
      (tail : Trace checkEmpty r n p h k target scs before rest middleCaller middleQueries
        processed afterCaller saved) :
      Trace checkEmpty r n p h k target scs before (edge :: rest) caller queries
        (receipt :: processed) afterCaller saved

/-- Every actual ordered trace completes through the same worker. -/
theorem trace_complete
    (trace : Trace (width := width) checkEmpty r n p h k target scs before edges caller queries
      processed afterCaller saved) :
    run checkEmpty r n p h k target scs before edges caller queries = .complete processed afterCaller saved := by
  induction trace with
  | nil => rfl
  | cons head continued _tail ih => simp only [run, head, continued, ih]

/-- Every completed run retains the actual caller-threaded trace and every branch cache. -/
theorem complete_trace (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (before : Cached) (edges : List (EdgeValue Symbol Constraint))
    (caller afterCaller : Caller width) (queries saved : Queries) (processed : List (Receipt width))
    (completed : run checkEmpty r n p h k target scs before edges caller queries =
      .complete processed afterCaller saved) :
    Trace checkEmpty r n p h k target scs before edges caller queries processed afterCaller saved := by
  induction edges generalizing caller queries processed with
  | nil =>
      cases completed
      exact .nil _ _
  | cons edge rest ih =>
      cases head : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => simp only [run, head] at completed; cases completed
      | some receipt =>
          cases continued : advance receipt with
          | none => simp only [run, head, continued] at completed; cases completed
          | some endpoint =>
              rcases endpoint with ⟨middleCaller, middleQueries⟩
              cases tail : run checkEmpty r n p h k target scs before rest middleCaller middleQueries with
              | stopped prefix current => simp only [run, head, continued, tail] at completed; cases completed
              | complete prefix finalCaller finalQueries =>
                  simp only [run, head, continued, tail, Result.complete.injEq] at completed
                  obtain ⟨rfl, rfl, rfl⟩ := completed
                  exact .cons head continued (ih middleCaller middleQueries prefix tail)

end MicroCFTA.SourcePruningEnumerationNativeBranches
