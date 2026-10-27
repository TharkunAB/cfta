import MicroCFTA.SourceFlatPruningNativeBranches
import MicroCFTA.SourcePruningEnumerationNativeContinuations

namespace MicroCFTA.SourceFlatPruningNativeContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Receipt" => SourceFlatPruningSelectedEdge.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- A completed continuation supplies the native endpoint for the next alternative. -/
inductive HookResult (Output : Type u) (Reason : Type v) (width : Nat) where
  /-- Empty output includes normal pruning and a stuck restart. -/
  | complete (outputs : List Output) (caller : Caller width) (queries : Queries)
  /-- Keep the explicit stop reason and any actual reached native endpoint. -/
  | stopped (outputs : List Output) (reason : Reason) (reached : Option (Caller width × Queries))

/-- Keep the exact edge receipt or continuation stop without inventing an endpoint. -/
inductive Stop (Reason : Type v) (width : Nat) where
  /-- A missing or noncontinuable edge stops before the hook and the suffix. -/
  | edge (current : Option (Receipt width))
  /-- A stopped hook retains its actual completed edge receipt. -/
  | continuation (current : Receipt width) (reason : Reason)
      (reached : Option (Caller width × Queries))

/-- Retain ordered edge receipts, continuation outputs and the exact stopping context. -/
inductive Result (Output : Type u) (Reason : Type v) (width : Nat) where
  /-- Every edge and invoked continuation completed. -/
  | complete (processed : List (Receipt width)) (outputs : List Output)
      (caller : Caller width) (queries : Queries)
  /-- Retain the finished prefix and the current edge or continuation stop. -/
  | stopped (processed : List (Receipt width)) (outputs : List Output) (current : Stop Reason width)

/-- Related hooks retain the same output order and exact optional native endpoint. -/
def HookResultRelated (flat : HookResult Output Reason width)
    (earlier : SourcePruningEnumerationNativeContinuations.HookResult Output Reason width) : Prop :=
  match flat, earlier with
  | .complete outputs caller queries, .complete oldOutputs oldCaller oldQueries =>
      outputs = oldOutputs ∧ caller = oldCaller ∧ queries = oldQueries
  | .stopped outputs reason reached, .stopped oldOutputs oldReason oldReached =>
      outputs = oldOutputs ∧ reason = oldReason ∧ reached = oldReached
  | _, _ => False

/-- Absent captured results remain absent; every present receipt retains its full relation. -/
def OptionalReceiptRelated (flat : Option (Receipt width))
    (earlier : Option (SourcePruningEnumerationSelectedEdge.Result width)) : Prop :=
  match flat, earlier with
  | none, none => True
  | some current, some oldCurrent => SourceFlatPruningSelectedEdge.ResultRelated current oldCurrent
  | _, _ => False

/-- Related stops retain the stopping stage, current receipt, reason and actual endpoint. -/
def StopRelated (flat : Stop Reason width)
    (earlier : SourcePruningEnumerationNativeContinuations.Stop Reason width) : Prop :=
  match flat, earlier with
  | .edge current, .edge oldCurrent => OptionalReceiptRelated current oldCurrent
  | .continuation current reason reached, .continuation oldCurrent oldReason oldReached =>
      SourceFlatPruningSelectedEdge.ResultRelated current oldCurrent ∧
        reason = oldReason ∧ reached = oldReached
  | _, _ => False

/-- Related workers retain ordered receipts, outputs, stops and exact native effects. -/
def ResultRelated (flat : Result Output Reason width)
    (earlier : SourcePruningEnumerationNativeContinuations.Result Output Reason width) : Prop :=
  match flat, earlier with
  | .complete processed outputs caller queries, .complete oldProcessed oldOutputs oldCaller oldQueries =>
      Language.All₂ SourceFlatPruningSelectedEdge.ResultRelated processed oldProcessed ∧
        outputs = oldOutputs ∧ caller = oldCaller ∧ queries = oldQueries
  | .stopped processed outputs current, .stopped oldProcessed oldOutputs oldCurrent =>
      Language.All₂ SourceFlatPruningSelectedEdge.ResultRelated processed oldProcessed ∧
        outputs = oldOutputs ∧ StopRelated current oldCurrent
  | _, _ => False

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run each completed edge's continuation before the next edge at its returned native endpoint.
The captured enumeration input is fixed. The hook can close over fixed sibling metadata.
This bounded worker does not prove completion or full source-effect correspondence. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended) (before : Cached) :
    List (EdgeValue Symbol Constraint) → Caller width → Queries → Result Output Reason width
  | [], caller, queries => .complete [] [] caller queries
  | edge :: rest, caller, queries =>
      match SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries with
      | none => .stopped [] [] (.edge none)
      | some receipt =>
          match receipt with
          | .complete fragment reached saved after =>
              match hook fragment reached saved after with
              | .stopped outputs reason endpoint =>
                  .stopped [] outputs (.continuation receipt reason endpoint)
              | .complete outputs middleCaller middleQueries =>
                  match run hook checkEmpty nativeFuel p h target scs before rest middleCaller middleQueries with
                  | .complete processed later finalCaller finalQueries =>
                      .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
                  | .stopped processed later current =>
                      .stopped (receipt :: processed) (outputs ++ later) current
          | other =>
              match SourceFlatPruningNativeBranches.advance other with
              | none => .stopped [] [] (.edge (some other))
              | some (middleCaller, middleQueries) =>
                  match run hook checkEmpty nativeFuel p h target scs before rest middleCaller middleQueries with
                  | .complete processed outputs finalCaller finalQueries =>
                      .complete (other :: processed) outputs finalCaller finalQueries
                  | .stopped processed outputs current => .stopped (other :: processed) outputs current

/-- A missing edge result retains its absence and does not invoke the hook or suffix. -/
theorem missing
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller : Caller width) (queries : Queries)
    (observed : SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries =
      none) :
    run hook checkEmpty nativeFuel p h target scs before (edge :: rest) caller queries =
      .stopped [] [] (.edge none) := by
  simp only [run, observed]

/-- The sibling starts at the hook's actual returned endpoint, after the head hook completes. -/
theorem completed_head
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller reached middleCaller : Caller width) (queries saved middleQueries : Queries)
    (fragment : Fragment) (after : Cached) (outputs : List Output)
    (observed : SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (continued : hook fragment reached saved after = .complete outputs middleCaller middleQueries) :
    run hook checkEmpty nativeFuel p h target scs before (edge :: rest) caller queries =
      match run hook checkEmpty nativeFuel p h target scs before rest middleCaller middleQueries with
      | .complete processed later finalCaller finalQueries =>
          .complete (.complete fragment reached saved after :: processed) (outputs ++ later) finalCaller finalQueries
      | .stopped processed later current =>
          .stopped (.complete fragment reached saved after :: processed) (outputs ++ later) current := by
  simp only [run, observed, continued]

/-- A stopped hook retains its output, reason and receipt without evaluating the sibling. -/
theorem stopped_hook
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller reached : Caller width) (queries saved : Queries) (fragment : Fragment) (after : Cached)
    (outputs : List Output) (reason : Reason) (endpoint : Option (Caller width × Queries))
    (observed : SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (halted : hook fragment reached saved after = .stopped outputs reason endpoint) :
    run hook checkEmpty nativeFuel p h target scs before (edge :: rest) caller queries =
      .stopped [] outputs (.continuation (.complete fragment reached saved after) reason endpoint) := by
  simp only [run, observed, halted]

/-- The identity hook retains the edge's native endpoint and emits no output. -/
def identityHook (_fragment : Fragment) (caller : Caller width) (queries : Queries) (_after : Cached) :
    HookResult Output Reason width :=
  .complete [] caller queries

/-- Identity hooks agree without changing either captured cache or native endpoint. -/
theorem identityHook_related (fragment : Fragment) (caller : Caller width) (queries : Queries)
    (flat : Cached) (earlier : EnumerationExpandableIndex.Cached Symbol Constraint) :
    HookResultRelated (identityHook (Output := Output) (Reason := Reason) fragment caller queries flat)
      (SourcePruningEnumerationNativeContinuations.identityHook
        (Output := Output) (Reason := Reason) fragment caller queries earlier) :=
  ⟨rfl, rfl, rfl⟩

/-- Embed a flat branch result without continuation outputs or continuation stops. -/
def ofBranches : SourceFlatPruningNativeBranches.Result width → Result Output Reason width
  | .complete processed caller queries => .complete processed [] caller queries
  | .stopped processed current => .stopped processed [] (.edge current)

/-- The identity hook preserves the entire flat branch result, including stopped receipts. -/
theorem identity_run
    (checkEmpty : Bool) (nativeFuel p h target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    run (identityHook (Output := Output) (Reason := Reason)) checkEmpty nativeFuel p h target scs before edges caller queries =
      ofBranches (SourceFlatPruningNativeBranches.run checkEmpty nativeFuel p h target scs before edges caller queries) := by
  induction edges generalizing caller queries with
  | nil => rfl
  | cons edge rest ih =>
      cases observed : SourceFlatPruningCapturedEdge.run checkEmpty nativeFuel p h target scs edge caller before queries with
      | none => simp only [run, SourceFlatPruningNativeBranches.run, observed, ofBranches]
      | some receipt =>
          cases receipt with
          | unhandled =>
              simp only [run, SourceFlatPruningNativeBranches.run, observed,
                SourceFlatPruningNativeBranches.advance, ofBranches]
          | rejected reached saved after =>
              simp only [run, SourceFlatPruningNativeBranches.run, observed,
                SourceFlatPruningNativeBranches.advance]
              rw [ih reached saved]
              cases SourceFlatPruningNativeBranches.run checkEmpty nativeFuel p h target scs before rest reached saved <;> rfl
          | complete fragment reached saved after =>
              simp only [run, SourceFlatPruningNativeBranches.run, observed, identityHook,
                SourceFlatPruningNativeBranches.advance]
              rw [ih reached saved]
              cases SourceFlatPruningNativeBranches.run checkEmpty nativeFuel p h target scs before rest reached saved <;> rfl
          | stopped fragments observation candidate =>
              simp only [run, SourceFlatPruningNativeBranches.run, observed]
              cases advanced : SourceFlatPruningNativeBranches.advance (.stopped fragments observation candidate) with
              | none => rfl
              | some endpoint =>
                  obtain ⟨reached, saved⟩ := endpoint
                  dsimp only
                  rw [ih reached saved]
                  cases SourceFlatPruningNativeBranches.run checkEmpty nativeFuel p h target scs before rest reached saved <;> rfl

end MicroCFTA.SourceFlatPruningNativeContinuations
