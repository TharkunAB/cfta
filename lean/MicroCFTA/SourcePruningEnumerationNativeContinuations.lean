import MicroCFTA.SourcePruningEnumerationNativeBranches

namespace MicroCFTA.SourcePruningEnumerationNativeContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat} {Output Reason : Type}

/-- A completed continuation supplies the native endpoint for the next alternative. -/
inductive HookResult (Output Reason : Type) (width : Nat) where
  /-- Empty output includes normal pruning and a stuck restart. -/
  | complete (outputs : List Output) (caller : Caller width) (queries : Queries)
  /-- Keep the explicit stop reason and any actual reached native endpoint. -/
  | stopped (outputs : List Output) (reason : Reason) (reached : Option (Caller width × Queries))

/-- Keep the exact edge receipt or continuation stop without inventing an endpoint. -/
inductive Stop (Reason : Type) (width : Nat) where
  /-- A missing or noncontinuable edge stops before the hook and the suffix. -/
  | edge (current : Option (Receipt width))
  /-- A stopped hook retains its actual completed edge receipt. -/
  | continuation (current : Receipt width) (reason : Reason)
      (reached : Option (Caller width × Queries))

/-- Retain ordered edge receipts, continuation outputs and the exact stopping context. -/
inductive Result (Output Reason : Type) (width : Nat) where
  /-- Every edge and invoked continuation completed. -/
  | complete (processed : List (Receipt width)) (outputs : List Output)
      (caller : Caller width) (queries : Queries)
  /-- Retain the finished prefix and the current edge or continuation stop. -/
  | stopped (processed : List (Receipt width)) (outputs : List Output) (current : Stop Reason width)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run each completed edge's continuation before the next edge at its returned native endpoint.
The captured enumeration input is fixed. The hook can close over fixed sibling metadata.
This bounded worker does not prove completion or full source-effect correspondence. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached) :
    List (EdgeValue Symbol Constraint) → Caller width → Queries → Result Output Reason width
  | [], caller, queries => .complete [] [] caller queries
  | edge :: rest, caller, queries =>
      match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => .stopped [] [] (.edge none)
      | some receipt =>
          match receipt with
          | .complete fragment reached saved after =>
              match hook fragment reached saved after with
              | .stopped outputs reason endpoint =>
                  .stopped [] outputs (.continuation receipt reason endpoint)
              | .complete outputs middleCaller middleQueries =>
                  match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
                  | .complete processed later finalCaller finalQueries =>
                      .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
                  | .stopped processed later current =>
                      .stopped (receipt :: processed) (outputs ++ later) current
          | other =>
              match SourcePruningEnumerationNativeBranches.advance other with
              | none => .stopped [] [] (.edge (some other))
              | some (middleCaller, middleQueries) =>
                  match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
                  | .complete processed outputs finalCaller finalQueries =>
                      .complete (other :: processed) outputs finalCaller finalQueries
                  | .stopped processed outputs current => .stopped (other :: processed) outputs current

/-- A missing edge result retains its absence and does not invoke the hook or suffix. -/
theorem missing
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller : Caller width) (queries : Queries)
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      none) :
    run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries =
      .stopped [] [] (.edge none) := by
  simp only [run, observed]

/-- The sibling starts at the hook's actual returned endpoint, after the head hook completes. -/
theorem completed_head
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller reached middleCaller : Caller width) (queries saved middleQueries : Queries)
    (fragment : Fragment) (after : Cached) (outputs : List Output)
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (continued : hook fragment reached saved after = .complete outputs middleCaller middleQueries) :
    run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries =
      match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
      | .complete processed later finalCaller finalQueries =>
          .complete (.complete fragment reached saved after :: processed) (outputs ++ later) finalCaller finalQueries
      | .stopped processed later current =>
          .stopped (.complete fragment reached saved after :: processed) (outputs ++ later) current := by
  simp only [run, observed, continued]

/-- A stopped hook retains its output, reason and receipt without evaluating the sibling. -/
theorem stopped_hook
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller reached : Caller width) (queries saved : Queries) (fragment : Fragment) (after : Cached)
    (outputs : List Output) (reason : Reason) (endpoint : Option (Caller width × Queries))
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (halted : hook fragment reached saved after = .stopped outputs reason endpoint) :
    run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries =
      .stopped [] outputs (.continuation (.complete fragment reached saved after) reason endpoint) := by
  simp only [run, observed, halted]

/-- The identity hook retains the edge's native endpoint and emits no output. -/
def identityHook (_fragment : Fragment) (caller : Caller width) (queries : Queries) (_after : Cached) :
    HookResult Output Reason width :=
  .complete [] caller queries

/-- Embed a legacy branch result without continuation outputs or continuation stops. -/
def ofBranches : SourcePruningEnumerationNativeBranches.Result width → Result Output Reason width
  | .complete processed caller queries => .complete processed [] caller queries
  | .stopped processed current => .stopped processed [] (.edge current)

/-- The identity hook preserves the entire legacy result, including stopped receipts. -/
theorem identity_run
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    run (identityHook (Output := Output) (Reason := Reason)) checkEmpty r n p h k target scs before edges caller queries =
      ofBranches (SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs before edges caller queries) := by
  induction edges generalizing caller queries with
  | nil => rfl
  | cons edge rest ih =>
      cases observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => simp only [run, SourcePruningEnumerationNativeBranches.run, observed, ofBranches]
      | some receipt =>
          cases receipt with
          | unhandled =>
              simp only [run, SourcePruningEnumerationNativeBranches.run, observed,
                SourcePruningEnumerationNativeBranches.advance, ofBranches]
          | rejected reached saved after =>
              simp only [run, SourcePruningEnumerationNativeBranches.run, observed,
                SourcePruningEnumerationNativeBranches.advance]
              rw [ih reached saved]
              cases SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs before rest reached saved <;> rfl
          | complete fragment reached saved after =>
              simp only [run, SourcePruningEnumerationNativeBranches.run, observed, identityHook,
                SourcePruningEnumerationNativeBranches.advance]
              rw [ih reached saved]
              cases SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs before rest reached saved <;> rfl
          | stopped fragments observation candidate =>
              simp only [run, SourcePruningEnumerationNativeBranches.run, observed]
              cases advanced : SourcePruningEnumerationNativeBranches.advance (.stopped fragments observation candidate) with
              | none => rfl
              | some endpoint =>
                  obtain ⟨reached, saved⟩ := endpoint
                  dsimp only
                  rw [ih reached saved]
                  cases SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k target scs before rest reached saved <;> rfl

end MicroCFTA.SourcePruningEnumerationNativeContinuations
