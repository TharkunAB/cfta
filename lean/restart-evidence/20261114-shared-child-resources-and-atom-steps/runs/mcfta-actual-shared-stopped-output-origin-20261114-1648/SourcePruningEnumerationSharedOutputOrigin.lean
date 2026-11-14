import MicroCFTA.SourcePruningEnumerationSharedEagerChildren
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot

/-!
# Actual shared outputs before a stop

Each scan output comes from a visitor at an actual completed prefix endpoint.
Only a completed child receipt supplies outputs from its actual continuation.
The actual Left callback supplies the exact restart input.
These facts do not supply resources or a finite completion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedOutputOrigin
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedBranching (scan)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Fold" => NativeContinuations.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- A complete or stopped scan output comes from its actual visitor and completed prefix. -/
theorem scan_output_origin
    (visit : Edge → Caller width → Queries → Cached → Fold Output Reason width)
    (before : Cached) (edges : List Edge) (caller : Caller width) (queries : Queries)
    (output : Output)
    (member : output ∈ (match scan visit before edges caller queries with
      | .complete _ outputs _ _ | .stopped _ outputs _ => outputs)) :
    ∃ (prefix : List Edge) (edge : Edge) (suffix : List Edge)
      (processed : List (Receipt width)) (earlier : List Output)
      (reached : Caller width) (saved : Queries),
      edges = prefix ++ edge :: suffix ∧
      scan visit before prefix caller queries = .complete processed earlier reached saved ∧
      output ∈ (match visit edge reached saved before with
        | .complete _ outputs _ _ | .stopped _ outputs _ => outputs) := by
  induction edges generalizing caller queries with
  | nil => cases member
  | cons edge rest ih =>
      cases head : visit edge caller queries before with
      | stopped processed outputs current =>
          have included : output ∈ outputs := by simpa only [scan, head] using member
          exact ⟨[], edge, rest, [], [], caller, queries, rfl, rfl,
            by simpa only [head] using included⟩
      | complete processed outputs reached saved =>
          have atHead (included : output ∈ outputs) :
              ∃ (prefix : List Edge) (row : Edge) (suffix : List Edge)
                (receipts : List (Receipt width)) (earlier : List Output)
                (current : Caller width) (memos : Queries),
                edge :: rest = prefix ++ row :: suffix ∧
                scan visit before prefix caller queries = .complete receipts earlier current memos ∧
                output ∈ (match visit row current memos before with
                  | .complete _ values _ _ | .stopped _ values _ => values) := by
            exact ⟨[], edge, rest, [], [], caller, queries, rfl, rfl,
              by simpa only [head] using included⟩
          have atTail (included : output ∈ (match scan visit before rest reached saved with
                | .complete _ values _ _ | .stopped _ values _ => values)) :
              ∃ (prefix : List Edge) (row : Edge) (suffix : List Edge)
                (receipts : List (Receipt width)) (earlier : List Output)
                (current : Caller width) (memos : Queries),
                edge :: rest = prefix ++ row :: suffix ∧
                scan visit before prefix caller queries = .complete receipts earlier current memos ∧
                output ∈ (match visit row current memos before with
                  | .complete _ values _ _ | .stopped _ values _ => values) := by
            obtain ⟨prefix, row, suffix, receipts, earlier, current, memos,
              decomposed, previous, origin⟩ := ih reached saved included
            refine ⟨edge :: prefix, row, suffix, processed ++ receipts,
              outputs ++ earlier, current, memos, ?_, ?_, origin⟩
            · simpa only [List.cons_append] using congrArg (List.cons edge) decomposed
            · simp only [scan, head, previous]
          cases tail : scan visit before rest reached saved with
          | complete later remaining finalCaller finalQueries =>
              have included : output ∈ outputs ++ remaining := by
                simpa only [scan, head, tail] using member
              rcases List.mem_append.mp included with old | fresh
              · exact atHead old
              · exact atTail (by simpa only [tail] using fresh)
          | stopped later remaining current =>
              have included : output ∈ outputs ++ remaining := by
                simpa only [scan, head, tail] using member
              rcases List.mem_append.mp included with old | fresh
              · exact atHead old
              · exact atTail (by simpa only [tail] using fresh)

/-- An actual completed head retains each output when its sibling suffix completes or stops. -/
theorem scan_head_outputs
    (visit : Edge → Caller width → Queries → Cached → Fold Output Reason width)
    (before : Cached) (edge : Edge) (rest : List Edge)
    (caller reached : Caller width) (queries saved : Queries)
    (processed : List (Receipt width)) (outputs : List Output) (output : Output)
    (observed : visit edge caller queries before = .complete processed outputs reached saved)
    (member : output ∈ outputs) :
    output ∈ (match scan visit before (edge :: rest) caller queries with
      | .complete _ values _ _ | .stopped _ values _ => values) := by
  rw [SourcePruningEnumerationSharedBranching.scan_complete
    visit before edge rest caller reached queries saved processed outputs observed]
  cases scan visit before rest reached saved <;> exact List.mem_append.mpr (.inl member)

/-- Only an actual complete selected receipt can supply continuation outputs. -/
theorem consumeSelected_output_origin
    (done : Fragment → Caller width → Queries → Cached → Fold Output Reason width)
    (caller : Caller width) (queries : Queries) (receipt : Receipt width) (output : Output)
    (member : output ∈ (match SourcePruningEnumerationSharedEagerChildren.consumeSelected done caller queries receipt with
      | .complete _ outputs _ _ | .stopped _ outputs _ => outputs)) :
    ∃ fragment reached saved after,
      receipt = .complete fragment reached saved after ∧
      output ∈ (match done fragment reached saved after with
        | .complete _ outputs _ _ | .stopped _ outputs _ => outputs) := by
  cases receipt with
  | complete fragment reached saved after =>
      refine ⟨fragment, reached, saved, after, rfl, ?_⟩
      cases actual : done fragment reached saved after <;>
        simpa only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, actual] using member
  | unhandled => cases member
  | rejected reached saved after => cases member
  | finalizeStopped fragment reached saved after => cases member
  | stopped completed observation candidate =>
      simp only [SourcePruningEnumerationSharedEagerChildren.consumeSelected] at member
      split at member <;> cases member

end MicroCFTA.SourcePruningEnumerationSharedOutputOrigin

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- An actual shared callback output retains its false record receipt and exact restart input. -/
theorem continueWith_output_restart
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ emitted (continueWith recur graph templates stop order fuel metadata uv fragment caller queries before),
      ∃ updated core,
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv (.inl fragment) before.core) =
          [.ok ((false, updated), core)] ∧
        output ∈ emitted (recur updated caller queries (EnumerationExpandableIndex.frame core before)
          (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core before))) := by
  unfold continueWith
  dsimp only
  split
  · intro output member; cases member
  · intro output member
    exact ⟨_, _, by assumption, member⟩
  · intro output member; cases member

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
