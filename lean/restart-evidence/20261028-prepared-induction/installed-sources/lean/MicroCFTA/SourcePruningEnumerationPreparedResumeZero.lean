import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationPreparedRecursive
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Actual restart results with zero expansion fuel

Each result retains its original native caller. Stop and done emit their
actual cache. A new expansion keeps an explicit exhausted stop.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Zero expansion fuel fixes the actual result and all emitted cache packets at every work fuel. -/
theorem resume_zero_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (next : Option Next) (profile : Profile) (property : Constraint → Prop)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap) :
    ∃ outcome : Result,
      (∀ workFuel, resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
        metadata caller memos.query before next = outcome) ∧
      match outcome with
      | .complete outputs reached saved =>
          reached = caller ∧ saved = memos.query ∧ Fits profile reached.checked ∧
          Heap property reached.checked.native.machine.heap ∧
          ∀ output ∈ outputs,
            Packet formulas solver inventory caller memos metadata output.cache ∧
            output.caller = caller ∧ output.queries = memos.query ∧
            (output.metadata = none ∨ output.metadata = some metadata) ∧ output.cache = before
      | .stopped outputs reason endpoint =>
          ∃ selected, next = some (.expand selected) ∧ outputs = [] ∧
            reason = .exhausted selected metadata before ∧ endpoint = some (caller, memos.query) ∧
            Fits profile caller.checked ∧ Heap property caller.checked.native.machine.heap := by
  let outcome : Result := match next with
    | none => .complete [⟨some metadata, before, caller, memos.query⟩] caller memos.query
    | some .done => .complete [⟨none, before, caller, memos.query⟩] caller memos.query
    | some .stuck => .complete [] caller memos.query
    | some (.expand selected) =>
        .stopped [] (.exhausted selected metadata before) (some (caller, memos.query))
  refine ⟨outcome, ?_, ?_⟩
  · intro workFuel
    cases next with
    | none => rfl
    | some next => cases next <;> rfl
  · cases next with
    | none =>
        refine ⟨rfl, rfl, bounded, known, ?_⟩
        intro output member
        have same := List.mem_singleton.mp member
        subst output
        exact ⟨packet, rfl, rfl, Or.inr rfl, rfl⟩
    | some next =>
        cases next with
        | done =>
            refine ⟨rfl, rfl, bounded, known, ?_⟩
            intro output member
            have same := List.mem_singleton.mp member
            subst output
            exact ⟨packet, rfl, rfl, Or.inl rfl, rfl⟩
        | stuck => exact ⟨rfl, rfl, bounded, known, fun _ member => False.elim (List.not_mem_nil member)⟩
        | expand selected => exact ⟨selected, rfl, rfl, rfl, rfl, bounded, known⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
