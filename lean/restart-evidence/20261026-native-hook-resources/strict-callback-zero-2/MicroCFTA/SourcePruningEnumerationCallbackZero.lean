import MicroCFTA.SourcePruningEnumerationRecursiveCallback
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Actual fragment callbacks with zero recursive expansion fuel

The callback runs at one sufficient fuel and every larger fuel. Its restart
uses the returned metadata and cache. Expansion stops with an explicit
exhaustion receipt. Every branch retains the original native endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- One callback bound fixes the actual zero-expansion hook and its native resources. -/
theorem callback_zero_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (profile : Profile) (alphabet : Constraint → Prop)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits profile caller.checked) (known : Heap alphabet caller.checked.native.machine.heap) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (outcome = if result.1 then .complete [] caller memos.query
        else match SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before) with
          | none => .complete [⟨some result.2, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
              caller memos.query
          | some .done => .complete [⟨none, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
              caller memos.query
          | some .stuck => .complete [] caller memos.query
          | some (.expand selected) => .stopped []
              (.exhausted selected result.2 (EnumerationExpandableIndex.frame after before))
              (some (caller, memos.query))) ∧
      (match outcome with
      | .complete outputs reached saved =>
          reached = caller ∧ saved = memos.query ∧ Fits profile reached.checked ∧
          Heap alphabet reached.checked.native.machine.heap ∧
          ∀ output ∈ outputs,
            Packet formulas solver inventory caller memos result.2 output.cache ∧
            output.caller = caller ∧ output.queries = memos.query ∧
            (output.metadata = none ∨ output.metadata = some result.2) ∧
            output.cache = EnumerationExpandableIndex.frame after before
      | .stopped outputs reason endpoint =>
          ∃ selected, outputs = [] ∧
            reason = .exhausted selected result.2 (EnumerationExpandableIndex.frame after before) ∧
            endpoint = some (caller, memos.query) ∧ Fits profile caller.checked ∧
            Heap alphabet caller.checked.native.machine.heap) ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 0)
          graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome := by
  obtain ⟨fuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before
      packet allocated
  let outcome : Result := if result.1 then .complete [] caller memos.query
    else match SourcePruningEnumerationRestart.decision stop order result.2
        (EnumerationExpandableIndex.frame after before) with
      | none => .complete [⟨some result.2, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
          caller memos.query
      | some .done => .complete [⟨none, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
          caller memos.query
      | some .stuck => .complete [] caller memos.query
      | some (.expand selected) => .stopped []
          (.exhausted selected result.2 (EnumerationExpandableIndex.frame after before))
          (some (caller, memos.query))
  refine ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing, rfl, ?_, ?_⟩
  · dsimp only [outcome]
    by_cases accepted : result.1 = true
    · rw [ite_eq_left accepted]
      exact ⟨rfl, rfl, bounded, known, fun _ member => False.elim (List.not_mem_nil member)⟩
    · rw [ite_eq_right accepted]
      cases decision : SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame after before) with
      | none =>
          dsimp only
          refine ⟨rfl, rfl, bounded, known, ?_⟩
          intro output member
          have same := List.mem_singleton.mp member
          subst output
          exact ⟨returned, rfl, rfl, Or.inr rfl, rfl⟩
      | some next =>
          cases next with
          | done =>
              dsimp only
              refine ⟨rfl, rfl, bounded, known, ?_⟩
              intro output member
              have same := List.mem_singleton.mp member
              subst output
              exact ⟨returned, rfl, rfl, Or.inl rfl, rfl⟩
          | stuck =>
              exact ⟨rfl, rfl, bounded, known, fun _ member => False.elim (List.not_mem_nil member)⟩
          | expand selected => exact ⟨selected, rfl, rfl, rfl, bounded, known⟩
  · intro extra
    have actual := callback extra
    refine ⟨actual.1, actual.2.1, ?_⟩
    rw [actual.2.2
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) 0) stop order]
    dsimp only [outcome]
    by_cases accepted : result.1 = true
    · simp only [ite_eq_left accepted]
    · simp only [ite_eq_right accepted]
      cases decision : SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame after before) with
      | none => rfl
      | some next => cases next <;> rfl

end MicroCFTA.SourcePruningEnumerationRecursive
